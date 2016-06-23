-- Terms and substitutions, implemented using flatterms.
-- This module implements the usual term manipulation stuff
-- (matching, unification, etc.) on top of the primitives
-- in Twee.Term.Core.
{-# LANGUAGE BangPatterns, CPP, PatternSynonyms, RankNTypes, FlexibleContexts, ViewPatterns, FlexibleInstances, UndecidableInstances, ScopedTypeVariables, RecordWildCards, MultiParamTypeClasses, FunctionalDependencies, GADTs, OverloadedStrings #-}
module Twee.Term(
  module Twee.Term,
  -- Stuff from Twee.Term.Core.
  Term, TermList, at, lenList,
  pattern Empty, pattern Cons, pattern ConsSym,
  pattern UnsafeCons, pattern UnsafeConsSym,
  Fun(..), Var(..), pattern Var, pattern Fun, singleton, Builder) where

#include "errors.h"
import Prelude hiding (lookup)
import Twee.Term.Core
import Data.List hiding (lookup)
import Data.Maybe
import Data.Ord
import Data.Monoid
import Data.IntMap.Strict(IntMap)
import qualified Data.IntMap.Strict as IntMap
import Twee.Profile

--------------------------------------------------------------------------------
-- A type class for builders.
--------------------------------------------------------------------------------

class Build f a | a -> f where
  builder :: a -> Builder f

instance Build f (Builder f) where
  builder = id

instance Build f (Term f) where
  builder = emitTerm

instance Build f (TermList f) where
  builder = emitTermList

instance Build f a => Build f [a] where
  {-# INLINE builder #-}
  builder = mconcat . map builder

{-# INLINE build #-}
build :: Build f a => a -> Term f
build x =
  case buildList x of
    Cons t Empty -> t

{-# INLINE buildList #-}
buildList :: Build f a => a -> TermList f
buildList x = buildTermList (builder x)

{-# INLINE con #-}
con :: Fun f -> Builder f
con x = emitFun x mempty

{-# INLINE fun #-}
fun :: Build f a => Fun f -> a -> Builder f
fun f ts = emitFun f (builder ts)

var :: Var -> Builder f
var = emitVar

--------------------------------------------------------------------------------
-- Pattern synonyms for substitutions.
--------------------------------------------------------------------------------

{-# INLINE listSubstList #-}
listSubstList :: Subst f -> [(Var, TermList f)]
listSubstList (Subst sub) = [(MkVar x, t) | (x, t) <- IntMap.toList sub]

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

class Substitution f s | s -> f where
  evalSubst :: s -> Var -> Builder f

instance (Build f a, v ~ Var) => Substitution f (v -> a) where
  {-# INLINE evalSubst #-}
  evalSubst sub x = builder (sub x)

instance Substitution f (Subst f) where
  {-# INLINE evalSubst #-}
  evalSubst sub x =
    case lookupList x sub of
      Nothing -> var x
      Just ts -> builder ts

{-# INLINE subst #-}
subst :: Substitution f s => s -> Term f -> Builder f
subst sub t = substList sub (singleton t)

{-# INLINE substList #-}
substList :: Substitution f s => s -> TermList f -> Builder f
substList sub ts = aux ts
  where
    aux Empty = mempty
    aux (Cons (Var x) ts) = evalSubst sub x <> aux ts
    aux (Cons (Fun f ts) us) = fun f (aux ts) <> aux us

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
lookupList (MkVar x) (Subst sub) = IntMap.lookup x sub

-- Add a new binding to a substitution.
{-# INLINE extendList #-}
extendList :: Var -> TermList f -> Subst f -> Maybe (Subst f)
extendList (MkVar x) !t (Subst sub) =
  case IntMap.lookup x sub of
    Nothing -> Just $! Subst (IntMap.insert x t sub)
    Just u
      | t == u    -> Just (Subst sub)
      | otherwise -> Nothing

-- Remove a binding from a substitution.
{-# INLINE retract #-}
retract :: Var -> Subst f -> Subst f
retract (MkVar x) (Subst sub) = Subst (IntMap.delete x sub)

-- Add a new binding to a substitution.
-- Overwrites any existing binding.
{-# INLINE unsafeExtendList #-}
unsafeExtendList :: Var -> TermList f -> Subst f -> Subst f
unsafeExtendList (MkVar x) !t (Subst sub) = Subst (IntMap.insert x t sub)

-- Composition of substitutions.
substCompose :: Substitution f s => Subst f -> s -> Subst f
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
    aux (ConsSym Fun{} t) = aux t
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
    n = maximum (0:map boundList (t:ts))
    vars =
      buildTermList $
        mconcat [emitVar (MkVar i) | i <- [0..n]]

    loop !_ !_ !_ !_ | False = __
    loop sub _ Empty [] = sub
    loop sub vs Empty (t:ts) = loop sub vs t ts
    loop sub vs (ConsSym Fun{} t) ts = loop sub vs t ts
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
        loop sub (ConsSym (Fun f _) pat) (ConsSym (Fun g _) t)
          | f == g = loop sub pat t
        loop sub (Cons (Var x) pat) (Cons t u) = do
          sub <- extend x t sub
          loop sub pat u
        loop _ _ _ = Nothing
    in stamp "match" (loop emptySubst pat t)

--------------------------------------------------------------------------------
-- Unification.
--------------------------------------------------------------------------------

newtype TriangleSubst f = Triangle { unTriangle :: Subst f }
  deriving Show

instance Substitution f (TriangleSubst f) where
  evalSubst (Triangle sub) x = substTri sub x

{-# INLINE substTri #-}
substTri :: Subst f -> Var -> Builder f
substTri sub x = aux x
  where
    aux x =
      case lookupList x sub of
        Nothing -> var x
        Just ts -> substList aux ts

{-# INLINE unify #-}
unify :: Term f -> Term f -> Maybe (Subst f)
unify t u = unifyList (singleton t) (singleton u)

unifyList :: TermList f -> TermList f -> Maybe (Subst f)
unifyList t u = do
  sub <- unifyListTri t u
  return $! close sub

{-# INLINE unifyTri #-}
unifyTri :: Term f -> Term f -> Maybe (TriangleSubst f)
unifyTri t u = unifyListTri (singleton t) (singleton u)

unifyListTri :: TermList f -> TermList f -> Maybe (TriangleSubst f)
unifyListTri !t !u = fmap Triangle (stamp "unify" (loop emptySubst t u))
  where
    loop !_ !_ !_ | False = __
    loop sub Empty _ = Just sub
    loop _ _ Empty = __
    loop sub (ConsSym (Fun f _) t) (ConsSym (Fun g _) u)
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
    occurs sub x (ConsSym Fun{} t) = occurs sub x t
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

children :: Term f -> TermList f
children t =
  case singleton t of
    UnsafeConsSym _ ts -> ts

fromTermList :: TermList f -> [Term f]
fromTermList t = unfoldr op t
  where
    op Empty = Nothing
    op (Cons t ts) = Just (t, ts)

instance Show (Term f) where
  show (Var x) = show x
  show (Fun f Empty) = show f
  show (Fun f ts) = show f ++ "(" ++ intercalate "," (map show (fromTermList ts)) ++ ")"

instance Show (TermList f) where
  show = show . fromTermList

instance Show (Subst f) where
  show subst =
    show
      [ (i, t)
      | i <- [0..substSize subst-1],
        Just t <- [lookup (MkVar i) subst] ]

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
bound :: Term f -> Int
bound t = boundList (singleton t)

{-# INLINE boundList #-}
boundList :: TermList f -> Int
boundList t = aux 0 t
  where
    aux n Empty = n
    aux n (ConsSym Fun{} t) = aux n t
    aux n (ConsSym (Var (MkVar x)) t)
      | x >= n = aux (x+1) t
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
    aux (ConsSym Fun{} t) = aux t
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

{-# INLINE properSubtermsList #-}
properSubtermsList :: TermList f -> [Term f]
properSubtermsList Empty = []
properSubtermsList (ConsSym _ t) = subtermsList t

{-# INLINE properSubterms #-}
properSubterms :: Term f -> [Term f]
properSubterms = properSubtermsList . singleton

isFun :: Term f -> Bool
isFun Fun{} = True
isFun _     = False

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
    aux (Cons (Fun ff ts) us) = fun (f ff) (aux ts) `mappend` aux us

--------------------------------------------------------------------------------
-- Typeclass for getting at the 'f' in a 'Term f'.
--------------------------------------------------------------------------------

class Numbered f where
  fromInt :: Int -> f
  toInt   :: f -> Int

fromFun :: Fun f -> f
fromFun (MkFun _ x) = x

toFun :: Numbered f => f -> Fun f
toFun f = MkFun (toInt f) f

instance (Ord f, Numbered f) => Ord (Fun f) where
  compare = comparing fromFun

pattern App f ts <- Fun (fromFun -> f) (fromTermList -> ts)

app :: Numbered a => a -> [Term a] -> Term a
app f ts = build (fun (toFun f) ts)
