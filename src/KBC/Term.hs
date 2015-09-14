-- Terms and substitutions, implemented using flatterms.
-- This module implements the usual term manipulation stuff
-- (matching, unification, etc.) on top of the primitives
-- in KBC.Term.Core.
{-# LANGUAGE BangPatterns, CPP, PatternSynonyms, RankNTypes, FlexibleContexts, ViewPatterns #-}
module KBC.Term(
  module KBC.Term,
  -- Stuff from KBC.Term.Core.
  Term, TermList, at, lenList,
  pattern Empty, pattern Cons, pattern ConsSym,
  pattern UnsafeCons, pattern UnsafeConsSym,
  Fun(..), OrdFun(..), Var(..), pattern Var, pattern Fun, singleton,
  BuildM, buildTermList, emitRoot, emitFun, emitVar, emitTermList,
  Subst, substSize, lookupList,
  MutableSubst, newMutableSubst, unsafeFreezeSubst, freezeSubst, copySubst,
  mutableLookupList, extendList, unsafeExtendList, retract, unsafeRetract) where

#include "errors.h"
import Prelude hiding (lookup)
import KBC.Term.Core hiding (subst)
import Control.Monad
import Control.Monad.ST.Strict
import Data.List hiding (lookup)
import Data.Maybe

--------------------------------------------------------------------------------
-- Pattern synonyms for substitutions.
--------------------------------------------------------------------------------

data SubstView f =
  SubstView {-# UNPACK #-} !Int {-# UNPACK #-} !(Subst f)

viewSubst :: Subst f -> SubstView f
viewSubst sub = SubstView 0 sub

patNextSubst :: SubstView f -> Maybe (Maybe (Var, TermList f), SubstView f)
patNextSubst (SubstView n sub)
  | n == substSize sub = Nothing
  | otherwise = Just (x, SubstView (n+1) sub)
  where
    x = do
      t <- lookupList sub (MkVar n)
      return (MkVar n, t)

pattern EmptySubst <- (patNextSubst -> Nothing)
pattern ConsSubst x s <- (patNextSubst -> Just (x, s))

{-# INLINE foldSubst #-}
foldSubst :: (Var -> TermList f -> b -> b) -> b -> Subst f -> b
foldSubst op e !sub = aux (viewSubst sub)
  where
    aux EmptySubst = e
    aux (ConsSubst Nothing sub) = aux sub
    aux (ConsSubst (Just (x, t)) sub) = op x t (aux sub)

{-# INLINE allSubst #-}
allSubst :: (Var -> TermList f -> Bool) -> Subst f -> Bool
allSubst p = foldSubst (\x t y -> p x t && y) True

{-# INLINE forMSubst_ #-}
forMSubst_ :: Monad m => Subst f -> (Var -> TermList f -> m ()) -> m ()
forMSubst_ sub f = foldSubst (\x t m -> do { f x t; m }) (return ()) sub

{-# INLINE substToList #-}
substToList :: Subst f -> [(Var, TermList f)]
substToList = foldSubst (\x t xs -> (x,t):xs) []

--------------------------------------------------------------------------------
-- Substitution.
--------------------------------------------------------------------------------

{-# INLINE subst #-}
subst :: Subst f -> Term f -> Term f
subst sub t =
  case substList sub (singleton t) of
    Cons u Empty -> u

substList :: Subst f -> TermList f -> TermList f
substList !sub !t = {-# SCC substList #-} buildTermList (2*lenList t) (emitSubstList sub t)

-- Emit a substitution applied to a term.
{-# INLINE emitSubst #-}
emitSubst :: Subst f -> Term f -> BuildM s f ()
emitSubst sub t = emitSubstList sub (singleton t)

-- Emit a substitution applied to a term list.
{-# INLINE emitSubstList #-}
emitSubstList :: Subst f -> TermList f -> BuildM s f ()
emitSubstList !sub = emitTransSubstList emitTermList sub

-- Emit a substitution applied to a term list, with some transformation
-- applied to the result of the substitution.
{-# INLINE emitTransSubstList #-}
emitTransSubstList :: (TermList f -> BuildM s f ()) -> Subst f -> TermList f -> BuildM s f ()
emitTransSubstList f !sub = aux
  where
    aux Empty = return ()
    aux (Cons (Var x) ts) = do
      case lookupList sub x of
        Nothing -> emitVar x
        Just u  -> f u
      aux ts
    aux (Cons (Fun f ts) us) = do
      emitFun f (aux ts)
      aux us

{-# INLINE iterSubst #-}
iterSubst :: TriangleSubst f -> Term f -> Term f
iterSubst sub t =
  case iterSubstList sub (singleton t) of
    Cons u Empty -> u

iterSubstList :: TriangleSubst f -> TermList f -> TermList f
iterSubstList !sub !t = buildTermList (2*lenList t) (emitIterSubstList sub t)

-- Emit a substitution repeatedly applied to a term.
{-# INLINE emitIterSubst #-}
emitIterSubst :: TriangleSubst f -> Term f -> BuildM s f ()
emitIterSubst sub t = emitIterSubstList sub (singleton t)

-- Emit a substitution repeatedly applied to a term list.
{-# INLINE emitIterSubstList #-}
emitIterSubstList :: TriangleSubst f -> TermList f -> BuildM s f ()
emitIterSubstList (Triangle !sub) = aux
  where
    aux !t = emitTransSubstList aux sub t

-- Composition of substitutions.
substCompose :: Subst f -> Subst f -> Subst f
substCompose !sub1 !sub2 =
  runST $ do
    sub <- newMutableSubst (substSize sub1)
    let
      loop EmptySubst !t = unsafeFreezeSubst sub
      loop (ConsSubst Nothing sub1) t = loop sub1 t
      loop (ConsSubst (Just (x, _)) sub1) (UnsafeCons (Fun _ t) u) = do
        unsafeExtendList sub x t
        loop sub1 u
    loop (viewSubst sub1) t
  where
    !t =
      buildTermList 32 $
        forMSubst_ sub1 $ \_ t ->
          emitFun (MkFun 0) (emitSubstList sub2 t)

-- Are two substitutions compatible?
substCompatible :: Subst f -> Subst f -> Bool
substCompatible sub1 sub2 = loop (viewSubst sub1) (viewSubst sub2)
  where
    loop !_ !_ | False = __
    loop !_ !_ | False = __
    loop EmptySubst _ = True
    loop _ EmptySubst = True
    loop (ConsSubst (Just (_, t)) sub1) (ConsSubst (Just (_, u)) sub2) =
      t == u && loop sub1 sub2
    loop (ConsSubst _ sub1) (ConsSubst _ sub2) =
      loop sub1 sub2

-- Take the union of two substitutions, which must be compatible.
substUnion :: Subst f -> Subst f -> Subst f
substUnion sub1 sub2 = runST $ do
  msub <- newMutableSubst (vars sub1 `max` vars sub2)
  let
    loop EmptySubst = return ()
    loop (ConsSubst (Just (x, t)) sub) = do
      unsafeExtendList msub x t
      loop sub
    loop (ConsSubst Nothing sub) = loop sub
  loop (viewSubst sub1)
  loop (viewSubst sub2)
  unsafeFreezeSubst msub

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
    aux (Cons (Var x) t) = isNothing (lookupList sub x) && aux t

-- Iterate a substitution to make it idempotent.
close :: TriangleSubst f -> Subst f
close (Triangle sub)
  | idempotent sub = sub
  | otherwise = close (Triangle (substCompose sub sub))

-- Return a substitution for canonicalising a list of terms.
canonicalise :: [TermList f] -> Subst f
canonicalise [] = emptySubst
canonicalise (t:ts) = runST $ do
  msub <- newMutableSubst n
  let
    loop !_ !_ !_ | False = __
    loop _ Empty [] = return ()
    loop vs Empty (t:ts) = loop vs t ts
    loop vs (ConsSym Fun{} t) ts = loop vs t ts
    loop vs0@(Cons v vs) (Cons (Var x) t) ts = do
      res <- extend msub x v
      case res of
        Just () -> loop vs  t ts
        Nothing -> loop vs0 t ts

  loop vars t ts
  unsafeFreezeSubst msub
  where
    n = maximum (0:map boundList (t:ts))
    vars =
      buildTermList (n+1) $ do
        forM_ [0..n] $ \i ->
          emitVar (MkVar i)

-- The empty substitution.
{-# NOINLINE emptySubst #-}
emptySubst =
  runST $ do
    msub <- newMutableSubst 0
    unsafeFreezeSubst msub

-- Turn a substitution list into a substitution.
flattenSubst :: [(Var, Term f)] -> Subst f
flattenSubst sub = fromMaybe err (matchList pat t)
  where
    pat = concatTerms (map (singleton . var . fst) sub)
    t   = concatTerms (map (singleton . snd) sub)
    err = ERROR("variable bound to two different terms")

--------------------------------------------------------------------------------
-- Matching.
--------------------------------------------------------------------------------

{-# INLINE match #-}
match :: Term f -> Term f -> Maybe (Subst f)
match pat t = matchList (singleton pat) (singleton t)

matchList :: TermList f -> TermList f -> Maybe (Subst f)
matchList !pat !t
  | lenList t < lenList pat = Nothing
  | otherwise = {-# SCC matchList #-} runST $ do
    subst <- newMutableSubst (boundList pat)
    let loop !_ !_ | False = __
        loop Empty _ = fmap Just (unsafeFreezeSubst subst)
        loop _ Empty = __
        loop (ConsSym (Fun f _) pat) (ConsSym (Fun g _) t)
          | f == g = loop pat t
        loop (Cons (Var x) pat) (Cons t u) = do
          res <- extend subst x t
          case res of
            Nothing -> return Nothing
            Just () -> loop pat u
        loop _ _ = return Nothing
    loop pat t

--------------------------------------------------------------------------------
-- Unification.
--------------------------------------------------------------------------------

newtype TriangleSubst f = Triangle { unTriangle :: Subst f }
  deriving Show

{-# INLINE unify #-}
unify :: Term f -> Term f -> Maybe (Subst f)
unify t u = unifyList (singleton t) (singleton u)

unifyList :: TermList f -> TermList f -> Maybe (Subst f)
unifyList t u = {-# SCC unifyList #-} do
  sub <- unifyListTri t u
  return $! close sub

{-# INLINE unifyTri #-}
unifyTri :: Term f -> Term f -> Maybe (TriangleSubst f)
unifyTri t u = unifyListTri (singleton t) (singleton u)

unifyListTri :: TermList f -> TermList f -> Maybe (TriangleSubst f)
unifyListTri !t !u = {-# SCC unifyListTri #-} runST $ do
  subst <- newMutableSubst (boundList t `max` boundList u)
  let
    loop !_ !_ | False = __
    loop Empty t = return True
    loop _ Empty = __
    loop (ConsSym (Fun f _) t) (ConsSym (Fun g _) u)
      | f == g = loop t u
    loop (Cons (Var x) t) (Cons u v) =
      both (var x u) (loop t v)
    loop (Cons t u) (Cons (Var x) v) =
      both (var x t) (loop u v)
    loop _ _ = return False

    both mx my = do
      x <- mx
      if x then my else return False

    either mx my = do
      x <- mx
      if x then return True else my

    var x t = do
      res <- mutableLookupList subst x
      case res of
        Just u -> loop u (singleton t)
        Nothing -> var1 x t

    var1 x t@(Var y) = do
      res <- mutableLookup subst y
      case res of
        Just t -> var1 x t
        Nothing -> do
          when (x /= y) $ do
            extend subst x t
            return ()
          return True

    var1 x t = do
      res <- occurs x (singleton t)
      if res then return False else do
        extend subst x t
        return True

    occurs !x Empty = return False
    occurs x (ConsSym Fun{} t) = occurs x t
    occurs x (ConsSym (Var y) t)
      | x == y = return True
      | otherwise = either (occurs x t) $ do
          mu <- mutableLookupList subst y
          case mu of
            Nothing -> return False
            Just u  -> occurs x u

  res <- loop t u
  case res of
    True  -> fmap (Just . Triangle) (unsafeFreezeSubst subst)
    False -> return Nothing

--------------------------------------------------------------------------------
-- Miscellaneous stuff.
--------------------------------------------------------------------------------

children :: Term f -> TermList f
children t =
  case singleton t of
    UnsafeConsSym _ ts -> ts

fromTermList :: TermList f -> [Term f]
fromTermList Empty = []
fromTermList (Cons t ts) = t:fromTermList ts

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
        Just t <- [lookup subst (MkVar i)] ]

{-# INLINE lookup #-}
lookup :: Subst f -> Var -> Maybe (Term f)
lookup s x = do
  Cons t Empty <- lookupList s x
  return t

{-# INLINE mutableLookup #-}
mutableLookup :: MutableSubst s f -> Var -> ST s (Maybe (Term f))
mutableLookup s x = do
  res <- mutableLookupList s x
  return $ do
    Cons t Empty <- res
    return t

{-# INLINE extend #-}
extend :: MutableSubst s f -> Var -> Term f -> ST s (Maybe ())
extend sub x t = extendList sub x (singleton t)

{-# INLINE len #-}
len :: Term f -> Int
len = lenList . singleton

{-# INLINE emitTerm #-}
emitTerm :: Term f -> BuildM s f ()
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
emptyTermList = buildTermList 0 (return ())

-- Functions for building terms.
var :: Var -> Term f
var x = buildTerm 1 (emitVar x)

fun :: Fun f -> [Term f] -> Term f
fun f ts = buildTerm (1+sum (map len ts)) (emitFun f (mapM_ emitTerm ts))

concatTerms :: [TermList f] -> TermList f
concatTerms ts = buildTermList (sum (map lenList ts)) (mapM_ emitTermList ts)

{-# INLINE buildTerm #-}
buildTerm :: Int -> (forall s. BuildM s f ()) -> Term f
buildTerm n m =
  case buildTermList n m of
    Cons t Empty -> t

subterms :: Term f -> [Term f]
subterms t = t:properSubterms t

properSubterms :: Term f -> [Term f]
properSubterms Var{} = []
properSubterms (Fun f ts) = concatMap subterms (fromTermList ts)

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
