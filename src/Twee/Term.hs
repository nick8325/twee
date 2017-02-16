-- Terms and substitutions, implemented using flatterms.
-- This module implements the usual term manipulation stuff
-- (matching, unification, etc.) on top of the primitives
-- in Twee.Term.Core.
{-# LANGUAGE BangPatterns, CPP, PatternSynonyms, ViewPatterns, TypeFamilies, OverloadedStrings, ScopedTypeVariables #-}
module Twee.Term(
  module Twee.Term,
  -- Stuff from Twee.Term.Core.
  Term, TermList, at, lenList,
  pattern Empty, pattern Cons, pattern ConsSym,
  pattern UnsafeCons, pattern UnsafeConsSym,
  Fun, fun, fun_id, fun_value, Var(..), pattern Var, pattern App, singleton, Builder) where

#include "errors.h"
import Prelude hiding (lookup)
import Twee.Term.Core
import Data.List hiding (lookup, find)
import Data.Maybe
import Data.Monoid
import Data.IntMap.Strict(IntMap)
import qualified Data.IntMap.Strict as IntMap

--------------------------------------------------------------------------------
-- A type class for builders.
--------------------------------------------------------------------------------

class Build a where
  type BuildFun a
  builder :: a -> Builder (BuildFun a)

instance Build (Builder f) where
  type BuildFun (Builder f) = f
  builder = id

instance Build (Term f) where
  type BuildFun (Term f) = f
  builder = emitTerm

instance Build (TermList f) where
  type BuildFun (TermList f) = f
  builder = emitTermList

instance Build a => Build [a] where
  type BuildFun [a] = BuildFun a
  {-# INLINE builder #-}
  builder = mconcat . map builder

{-# INLINE build #-}
build :: Build a => a -> Term (BuildFun a)
build x =
  case buildList x of
    Cons t Empty -> t

{-# INLINE buildList #-}
buildList :: Build a => a -> TermList (BuildFun a)
buildList x = {-# SCC buildList #-} buildTermList (builder x)

{-# INLINE con #-}
con :: Fun f -> Builder f
con x = emitApp x mempty

{-# INLINE app #-}
app :: Build a => Fun (BuildFun a) -> a -> Builder (BuildFun a)
app f ts = emitApp f (builder ts)

var :: Var -> Builder f
var = emitVar

--------------------------------------------------------------------------------
-- Pattern synonyms for substitutions.
--------------------------------------------------------------------------------

{-# INLINE listSubstList #-}
listSubstList :: Subst f -> [(Var, TermList f)]
listSubstList (Subst sub) = [(V x, t) | (x, t) <- IntMap.toList sub]

{-# INLINE listSubst #-}
listSubst :: Subst f -> [(Var, Term f)]
listSubst sub = [(x, t) | (x, Cons t Empty) <- listSubstList sub]

{-# INLINE foldSubst #-}
foldSubst :: (Var -> TermList f -> b -> b) -> b -> Subst f -> b
foldSubst op e !sub = foldr (uncurry op) e (listSubstList sub)

{-# INLINE allSubst #-}
allSubst :: (Var -> TermList f -> Bool) -> Subst f -> Bool
allSubst p = foldSubst (\x t y -> p x t && y) True

{-# INLINE forMSubst_ #-}
forMSubst_ :: Monad m => Subst f -> (Var -> TermList f -> m ()) -> m ()
forMSubst_ sub f = foldSubst (\x t m -> do { f x t; m }) (return ()) sub

--------------------------------------------------------------------------------
-- Substitution.
--------------------------------------------------------------------------------

class Substitution s where
  type SubstFun s
  evalSubst :: s -> Var -> Builder (SubstFun s)

  {-# INLINE substList #-}
  substList :: s -> TermList (SubstFun s) -> Builder (SubstFun s)
  substList sub ts = aux ts
    where
      aux Empty = mempty
      aux (Cons (Var x) ts) = evalSubst sub x <> aux ts
      aux (Cons (App f ts) us) = app f (aux ts) <> aux us

instance (Build a, v ~ Var) => Substitution (v -> a) where
  type SubstFun (v -> a) = BuildFun a

  {-# INLINE evalSubst #-}
  evalSubst sub x = builder (sub x)

instance Substitution (Subst f) where
  type SubstFun (Subst f) = f

  {-# INLINE evalSubst #-}
  evalSubst sub x =
    case lookupList x sub of
      Nothing -> var x
      Just ts -> builder ts

{-# INLINE subst #-}
subst :: Substitution s => s -> Term (SubstFun s) -> Builder (SubstFun s)
subst sub t = substList sub (singleton t)

newtype Subst f =
  Subst {
    unSubst :: IntMap (TermList f) }

{-# INLINE substSize #-}
substSize :: Subst f -> Int
substSize (Subst sub)
  | IntMap.null sub = 0
  | otherwise = fst (IntMap.findMax sub) + 1

-- Look up a variable.
{-# INLINE lookupList #-}
lookupList :: Var -> Subst f -> Maybe (TermList f)
lookupList x (Subst sub) = IntMap.lookup (var_id x) sub

-- Add a new binding to a substitution.
{-# INLINE extendList #-}
extendList :: Var -> TermList f -> Subst f -> Maybe (Subst f)
extendList x !t (Subst sub) =
  case IntMap.lookup (var_id x) sub of
    Nothing -> Just $! Subst (IntMap.insert (var_id x) t sub)
    Just u
      | t == u    -> Just (Subst sub)
      | otherwise -> Nothing

-- Remove a binding from a substitution.
{-# INLINE retract #-}
retract :: Var -> Subst f -> Subst f
retract x (Subst sub) = Subst (IntMap.delete (var_id x) sub)

-- Add a new binding to a substitution.
-- Overwrites any existing binding.
{-# INLINE unsafeExtendList #-}
unsafeExtendList :: Var -> TermList f -> Subst f -> Subst f
unsafeExtendList x !t (Subst sub) = Subst (IntMap.insert (var_id x) t sub)

-- Composition of substitutions.
substCompose :: Substitution s => Subst (SubstFun s) -> s -> Subst (SubstFun s)
substCompose (Subst !sub1) !sub2 =
  Subst (IntMap.map (buildList . substList sub2) sub1)

-- Are two substitutions compatible?
substCompatible :: Subst f -> Subst f -> Bool
substCompatible (Subst !sub1) (Subst !sub2) =
  IntMap.null (IntMap.mergeWithKey f g h sub1 sub2)
  where
    f _ t u
      | t == u = Nothing
      | otherwise = Just t
    g _ = IntMap.empty
    h _ = IntMap.empty

-- Take the union of two substitutions, which must be compatible.
substUnion :: Subst f -> Subst f -> Subst f
substUnion (Subst !sub1) (Subst !sub2) =
  Subst (IntMap.union sub1 sub2)

-- Is a substitution idempotent?
{-# INLINE idempotent #-}
idempotent :: Subst f -> Bool
idempotent !sub = allSubst (\_ t -> sub `idempotentOn` t) sub

-- Does a substitution affect a term?
{-# INLINE idempotentOn #-}
idempotentOn :: Subst f -> TermList f -> Bool
idempotentOn !sub = aux
  where
    aux Empty = True
    aux (ConsSym App{} t) = aux t
    aux (Cons (Var x) t) = isNothing (lookupList x sub) && aux t

-- Iterate a substitution to make it idempotent.
close :: TriangleSubst f -> Subst f
close (Triangle sub)
  | idempotent sub = sub
  | otherwise      = close (Triangle (substCompose sub sub))

-- Return a substitution for canonicalising a list of terms.
canonicalise :: [TermList f] -> Subst f
canonicalise [] = emptySubst
canonicalise (t:ts) = loop emptySubst vars t ts
  where
    n = maximum (V 0:map boundList (t:ts))
    vars =
      buildTermList $
        mconcat [emitVar x | x <- [V 0..n]]

    loop !_ !_ !_ !_ | False = __
    loop sub _ Empty [] = sub
    loop sub vs Empty (t:ts) = loop sub vs t ts
    loop sub vs (ConsSym App{} t) ts = loop sub vs t ts
    loop sub vs0@(Cons v vs) (Cons (Var x) t) ts =
      case extend x v sub of
        Just sub -> loop sub vs  t ts
        Nothing  -> loop sub vs0 t ts

-- The empty substitution.
{-# NOINLINE emptySubst #-}
emptySubst = Subst IntMap.empty

-- Turn a substitution list into a substitution.
flattenSubst :: [(Var, Term f)] -> Maybe (Subst f)
flattenSubst sub = matchList pat t
  where
    pat = buildList (map (var . fst) sub)
    t   = buildList (map snd sub)

--------------------------------------------------------------------------------
-- Matching.
--------------------------------------------------------------------------------

{-# INLINE match #-}
match :: Term f -> Term f -> Maybe (Subst f)
match pat t = matchList (singleton pat) (singleton t)

matchList :: TermList f -> TermList f -> Maybe (Subst f)
matchList !pat !t
  | lenList t < lenList pat = Nothing
  | otherwise =
    let loop !_ !_ !_ | False = __
        loop sub Empty _ = Just sub
        loop _ _ Empty = __
        loop sub (ConsSym (App f _) pat) (ConsSym (App g _) t)
          | f == g = loop sub pat t
        loop sub (Cons (Var x) pat) (Cons t u) = do
          sub <- extend x t sub
          loop sub pat u
        loop _ _ _ = Nothing
    in {-# SCC match #-} loop emptySubst pat t

--------------------------------------------------------------------------------
-- Unification.
--------------------------------------------------------------------------------

newtype TriangleSubst f = Triangle { unTriangle :: Subst f }
  deriving Show

instance Substitution (TriangleSubst f) where
  type SubstFun (TriangleSubst f) = f

  {-# INLINE evalSubst #-}
  evalSubst (Triangle sub) x =
    case lookupList x sub of
      Nothing  -> var x
      Just ts  -> substList (Triangle sub) ts

  -- Redefine substList to get better inlining behaviour
  {-# INLINE substList #-}
  substList (Triangle sub) ts = aux ts
    where
      aux Empty = mempty
      aux (Cons (Var x) ts) = auxVar x <> aux ts
      aux (Cons (App f ts) us) = app f (aux ts) <> aux us

      auxVar x =
        case lookupList x sub of
          Nothing -> var x
          Just ts -> aux ts

unify :: Term f -> Term f -> Maybe (Subst f)
unify t u = unifyList (singleton t) (singleton u)

unifyList :: TermList f -> TermList f -> Maybe (Subst f)
unifyList t u = do
  sub <- unifyListTri t u
  return $! close sub

unifyTri :: Term f -> Term f -> Maybe (TriangleSubst f)
unifyTri t u = unifyListTri (singleton t) (singleton u)

unifyListTri :: TermList f -> TermList f -> Maybe (TriangleSubst f)
unifyListTri !t !u = fmap Triangle ({-# SCC unify #-} loop emptySubst t u)
  where
    loop !_ !_ !_ | False = __
    loop sub Empty _ = Just sub
    loop _ _ Empty = __
    loop sub (ConsSym (App f _) t) (ConsSym (App g _) u)
      | f == g = loop sub t u
    loop sub (Cons (Var x) t) (Cons u v) = do
      sub <- var sub x u
      loop sub t v
    loop sub (Cons t u) (Cons (Var x) v) = do
      sub <- var sub x t
      loop sub u v
    loop _ _ _ = Nothing

    var sub x t =
      case lookupList x sub of
        Just u -> loop sub u (singleton t)
        Nothing -> var1 sub x t

    var1 sub x t@(Var y)
      | x == y = return sub
      | otherwise =
        case lookup y sub of
          Just t  -> var1 sub x t
          Nothing -> extend x t sub

    var1 sub x t = do
      occurs sub x (singleton t)
      extend x t sub

    occurs !_ !_ Empty = Just ()
    occurs sub x (ConsSym App{} t) = occurs sub x t
    occurs sub x (ConsSym (Var y) t)
      | x == y = Nothing
      | otherwise = do
          occurs sub x t
          case lookupList y sub of
            Nothing -> Just ()
            Just u  -> occurs sub x u

--------------------------------------------------------------------------------
-- Miscellaneous stuff.
--------------------------------------------------------------------------------

empty :: forall f. TermList f
empty = buildList (mempty :: Builder f)

children :: Term f -> TermList f
children t =
  case singleton t of
    UnsafeConsSym _ ts -> ts

unpack :: TermList f -> [Term f]
unpack t = unfoldr op t
  where
    op Empty = Nothing
    op (Cons t ts) = Just (t, ts)

instance Show (Term f) where
  show (Var x) = show x
  show (App f Empty) = show f
  show (App f ts) = show f ++ "(" ++ intercalate "," (map show (unpack ts)) ++ ")"

instance Show (TermList f) where
  show = show . unpack

instance Show (Subst f) where
  show subst =
    show
      [ (i, t)
      | i <- [0..substSize subst-1],
        Just t <- [lookup (V i) subst] ]

{-# INLINE lookup #-}
lookup :: Var -> Subst f -> Maybe (Term f)
lookup x s = do
  Cons t Empty <- lookupList x s
  return t

{-# INLINE extend #-}
extend :: Var -> Term f -> Subst f -> Maybe (Subst f)
extend x t sub = extendList x (singleton t) sub

{-# INLINE len #-}
len :: Term f -> Int
len = lenList . singleton

{-# INLINE emitTerm #-}
emitTerm :: Term f -> Builder f
emitTerm t = emitTermList (singleton t)

-- Find the lowest-numbered variable that doesn't appear in a term.
{-# INLINE bound #-}
bound :: Term f -> Var
bound t = boundList (singleton t)

{-# INLINE boundList #-}
boundList :: TermList f -> Var
boundList t = aux (V 0) t
  where
    aux n Empty = n
    aux n (ConsSym App{} t) = aux n t
    aux n (ConsSym (Var x) t)
      | x >= n = aux (succ x) t
      | otherwise = aux n t

-- Check if a variable occurs in a term.
{-# INLINE occurs #-}
occurs :: Var -> Term f -> Bool
occurs x t = occursList x (singleton t)

{-# INLINE occursList #-}
occursList :: Var -> TermList f -> Bool
occursList !x = aux
  where
    aux Empty = False
    aux (ConsSym App{} t) = aux t
    aux (ConsSym (Var y) t) = x == y || aux t

{-# INLINE termListToList #-}
termListToList :: TermList f -> [Term f]
termListToList Empty = []
termListToList (Cons t ts) = t:termListToList ts

-- The empty term list.
{-# NOINLINE emptyTermList #-}
emptyTermList :: TermList f
emptyTermList = buildList (mempty :: Builder f)

-- Functions for building terms.

{-# INLINE subtermsList #-}
subtermsList :: TermList f -> [Term f]
subtermsList t = unfoldr op t
  where
    op Empty = Nothing
    op (ConsSym t u) = Just (t, u)

{-# INLINE subterms #-}
subterms :: Term f -> [Term f]
subterms = subtermsList . singleton

{-# INLINE properSubterms #-}
properSubterms :: Term f -> [Term f]
properSubterms = subtermsList . children

isApp :: Term f -> Bool
isApp App{} = True
isApp _     = False

isVar :: Term f -> Bool
isVar Var{} = True
isVar _     = False

isInstanceOf :: Term f -> Term f -> Bool
t `isInstanceOf` pat = isJust (match pat t)

isVariantOf :: Term f -> Term f -> Bool
t `isVariantOf` u = t `isInstanceOf` u && u `isInstanceOf` t

mapFun :: (Fun f -> Fun g) -> Term f -> Builder g
mapFun f = mapFunList f . singleton

mapFunList :: (Fun f -> Fun g) -> TermList f -> Builder g
mapFunList f ts = aux ts
  where
    aux Empty = mempty
    aux (Cons (Var x) ts) = var x `mappend` aux ts
    aux (Cons (App ff ts) us) = app (f ff) (aux ts) `mappend` aux us

{-# INLINE replacePosition #-}
replacePosition :: (Build a, BuildFun a ~ f) => Int -> a -> TermList f -> Builder f
replacePosition n !x = aux n
  where
    aux !_ !_ | False = __
    aux _ Empty = mempty
    aux 0 (Cons _ t) = builder x `mappend` builder t
    aux n (Cons (Var x) t) = var x `mappend` aux (n-1) t
    aux n (Cons t@(App f ts) u)
      | n < len t =
        app f (aux (n-1) ts) `mappend` builder u
      | otherwise =
        builder t `mappend` aux (n-len t) u

{-# INLINE replacePositionSub #-}
replacePositionSub :: (Substitution sub, SubstFun sub ~ f) => sub -> Int -> TermList f -> TermList f -> Builder f
replacePositionSub sub n !x = aux n
  where
    aux !_ !_ | False = __
    aux _ Empty = mempty
    aux n (Cons t u)
      | n < len t = inside n t `mappend` outside u
      | otherwise = outside (singleton t) `mappend` aux (n-len t) u

    inside 0 _ = outside x
    inside n (App f ts) = app f (aux (n-1) ts)
    inside _ _ = __

    outside t = substList sub t
