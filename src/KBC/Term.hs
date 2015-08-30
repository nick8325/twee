-- Terms and substitutions, implemented using flatterms.
-- This module implements the usual term manipulation stuff
-- (matching, unification, etc.) on top of the primitives
-- in KBC.Term.Core.
{-# LANGUAGE BangPatterns, CPP, PatternSynonyms, RankNTypes, FlexibleContexts, ViewPatterns #-}
{-# OPTIONS_GHC -funfolding-creation-threshold=1000000 -funfolding-use-threshold=100000 #-}
module KBC.Term(
  module KBC.Term,
  -- Stuff from KBC.Term.Core.
  Term, TermList, lenList,
  pattern Empty, pattern Cons, pattern ConsSym,
  pattern UnsafeCons, pattern UnsafeConsSym,
  Fun(..), Var(..), pattern Var, pattern Fun, singleton,
  Builder, buildTermList, emitRoot, emitFun, emitVar, emitTermList,
  Subst, substSize, lookupList,
  MutableSubst, newMutableSubst, unsafeFreezeSubst, mutableLookupList,
  extendList, unsafeExtendList, retract, unsafeRetract) where

#include "errors.h"
import Prelude hiding (lookup)
import KBC.Term.Core hiding (subst)
import Control.Monad
import Control.Monad.ST.Strict
import Data.List hiding (lookup)
import Data.Maybe

--------------------------------------------------------------------------------
-- A helper datatype for building terms.
--------------------------------------------------------------------------------

-- An algebraic data type for terms, with flatterms at the leaf.
data CompoundTerm f =
    CTerm      (TermList f)
  | CSubstTerm (Subst f) (TermList f)
  | CIterSubstTerm (Subst f) (TermList f)
  | CVar Var
  | CFun (Fun f) (CompoundTerm f)
  | CNil
  | CAppend (CompoundTerm f) (CompoundTerm f)

fromList :: [CompoundTerm f] -> CompoundTerm f
fromList = foldr CAppend CNil

-- Turn a compound term into a flatterm.
flattenTerm :: CompoundTerm f -> Term f
flattenTerm t =
  case flattenList t of
    Cons u Empty -> u

-- Turn a compound termlist into a flatterm list.
flattenList :: CompoundTerm f -> TermList f
flattenList (CTerm t) = t
flattenList t =
  buildTermList $ do
    let
      loop (CTerm t) = emitTermList t
      loop (CSubstTerm sub t) = emitSubstList sub t
      loop (CIterSubstTerm sub t) = emitIterSubstList sub t
      loop (CVar x) = emitVar x
      loop (CFun f t) = emitFun f (loop t)
      loop CNil = return ()
      loop (CAppend t u) = do
        loop t
        loop u
    loop t

-- Functions for building terms.
var :: Var -> Term f
var x =
  case buildTermList (emitVar x) of
    Cons t Empty -> t

fun :: Fun f -> [Term f] -> Term f
fun f ts =
  case buildTermList (emitFun f (mapM_ emitTerm ts)) of
    Cons t Empty -> t

--------------------------------------------------------------------------------
-- A helper datatype for building substitutions.
--------------------------------------------------------------------------------

-- An algebraic data type for substitutions.
data CompoundSubst f =
    CSubst  (Subst f)
  | CSingle Var (Term f)
  | CUnion [CompoundSubst f]

-- Flatten a compound substitution.
flattenSubst :: CompoundSubst f -> Maybe (Subst f)
flattenSubst (CSubst sub) = Just sub
flattenSubst sub = matchList pat t
  where
    pat = flattenSubst' (\x _ -> emitVar x)  [sub]
    t   = flattenSubst' (\_ t -> emitTermList t) [sub]

{-# INLINE flattenSubst' #-}
flattenSubst' ::
  (forall m. Builder f m => Var -> TermList f -> m ()) ->
  [CompoundSubst f] -> TermList f
flattenSubst' emit subs =
  buildTermList $ do
    let
      loop [] = return ()
      loop (CSubst sub:subs) = forMSubst_ sub emit
      loop (CSingle x t:subs) = do
        emit x (singleton t)
        loop subs
      loop (CUnion subs:subs') = loop (subs ++ subs')
    loop subs

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
substList !sub !t = buildTermList (emitSubstList sub t)

-- Emit a substitution applied to a term.
{-# INLINE emitSubst #-}
emitSubst :: Builder f m => Subst f -> Term f -> m ()
emitSubst sub t = emitSubstList sub (singleton t)

-- Emit a substitution applied to a term list.
{-# INLINE emitSubstList #-}
emitSubstList :: Builder f m => Subst f -> TermList f -> m ()
emitSubstList !sub = aux
  where
    aux Empty = return ()
    aux (Cons (Var x) ts) = do
      case lookupList sub x of
        Nothing -> emitVar x
        Just u  -> emitTermList u
      aux ts
    aux (Cons (Fun f ts) us) = do
      emitFun f (aux ts)
      aux us

{-# INLINE iterSubst #-}
iterSubst :: Subst f -> Term f -> Term f
iterSubst sub t =
  case iterSubstList sub (singleton t) of
    Cons u Empty -> u

iterSubstList :: Subst f -> TermList f -> TermList f
iterSubstList !sub !t = buildTermList (emitIterSubstList sub t)

-- Emit a substitution repeatedly applied to a term.
{-# INLINE emitIterSubst #-}
emitIterSubst :: Builder f m => Subst f -> Term f -> m ()
emitIterSubst sub t = emitIterSubstList sub (singleton t)

-- Emit a substitution repeatedly applied to a term list.
{-# INLINE emitIterSubstList #-}
emitIterSubstList :: Builder f m => Subst f -> TermList f -> m ()
emitIterSubstList !sub = aux
  where
    aux Empty = return ()
    aux (Cons (Var x) ts) = do
      case lookupList sub x of
        Nothing -> emitVar x
        Just u  -> aux u
      aux ts
    aux (Cons (Fun f ts) us) = do
      emitFun f (aux ts)
      aux us

-- Composition of substitutions.
substCompose :: Subst f -> Subst f -> Subst f
substCompose !sub1 !sub2 =
  runST $ do
    sub <- newMutableSubst t (substSize sub1)
    let
      loop EmptySubst !t = unsafeFreezeSubst sub
      loop (ConsSubst Nothing sub1) t = loop sub1 t
      loop (ConsSubst (Just (x, _)) sub1) (UnsafeCons (Fun _ t) u) = do
        unsafeExtendList sub x t
        loop sub1 u
    loop (viewSubst sub1) t
  where
    !t =
      buildTermList $
        forMSubst_ sub1 $ \_ t ->
          emitFun (MkFun 0) (emitSubstList sub2 t)

-- Is a substitution idempotent?
{-# INLINE idempotent #-}
idempotent :: Subst f -> Bool
idempotent !sub = foldSubst p True sub
  where
    p _ t x = sub `idempotentOn` t && x

-- Does a substitution affect a term?
{-# INLINE idempotentOn #-}
idempotentOn :: Subst f -> TermList f -> Bool
idempotentOn !sub = aux
  where
    aux Empty = True
    aux (ConsSym Fun{} t) = aux t
    aux (Cons (Var x) t) = isNothing (lookupList sub x) && aux t

-- Iterate a substitution to make it idempotent.
close :: Subst f -> Subst f
close sub
  | idempotent sub = sub
  | otherwise = close (substCompose sub sub)

-- Return a substitution for canonicalising a list of terms.
canonicalise :: [TermList f] -> Subst f
canonicalise (t:ts) = runST $ do
  msub <- newMutableSubst vars n
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
    n = maximum (0:map boundList ts)
    vars =
      buildTermList $ do
        forM_ [0..n] $ \i ->
          emitVar (MkVar i)

--------------------------------------------------------------------------------
-- Matching.
--------------------------------------------------------------------------------

{-# INLINE match #-}
match :: Term f -> Term f -> Maybe (Subst f)
match pat t = matchList (singleton pat) (singleton t)

matchList :: TermList f -> TermList f -> Maybe (Subst f)
matchList !pat !t = runST $ do
  subst <- newMutableSubst t (boundList pat)
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

{-# INLINE unify #-}
unify :: Term f -> Term f -> Maybe (Subst f)
unify t u = unifyList (singleton t) (singleton u)

unifyList :: TermList f -> TermList f -> Maybe (Subst f)
unifyList t u = do
  sub <- unifyListTri t u
  return $! close sub

{-# INLINE unifyTri #-}
unifyTri :: Term f -> Term f -> Maybe (Subst f)
unifyTri t u = unifyListTri (singleton t) (singleton u)

unifyListTri :: TermList f -> TermList f -> Maybe (Subst f)
unifyListTri !t !u = runST $ do
  let (t', u') = shareList2 t u
  subst <- newMutableSubst t' (boundList t' `max` boundList u)
  let
    loop !_ !_ | False = __
    loop Empty _ = return True
    loop _ Empty = __
    loop (ConsSym (Fun f _) t) (ConsSym (Fun g _) u)
      | f == g = loop t u
    loop (Cons (Var x) t) (Cons u v) = do
      var x u
      loop t v
    loop (Cons t u) (Cons (Var x) v) = do
      var x t
      loop u v
    loop _ _ = return False

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

    var1 x t
      | occurs x t = return False
      | otherwise = do
          extend subst x t
          return True

  res <- loop t' u'
  case res of
    True  -> fmap Just (unsafeFreezeSubst subst)
    False -> return Nothing

--------------------------------------------------------------------------------
-- Miscellaneous stuff.
--------------------------------------------------------------------------------

children :: Term f -> TermList f
children t =
  case singleton t of
    UnsafeConsSym _ ts -> ts

toList :: TermList f -> [Term f]
toList Empty = []
toList (Cons t ts) = t:toList ts

instance Show (Term f) where
  show (Var x) = show x
  show (Fun f Empty) = show f
  show (Fun f ts) = show f ++ "(" ++ intercalate "," (map show (toList ts)) ++ ")"

instance Show (TermList f) where
  show = show . toList

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
emitTerm :: Builder f m => Term f -> m ()
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

{-# INLINE shared #-}
shared :: Term f -> Term f -> Bool
shared t u = sharedList (singleton t) (singleton u)

-- Make two terms share the same storage.
share2 :: Term f -> Term f -> (Term f, Term f)
share2 t u
  | shared t u = (t, u)
  | otherwise = (t', u')
  where
    UnsafeCons t' (UnsafeCons u' _) =
      buildTermList $ do
        emitTerm t
        emitTerm u

shareList2 :: TermList f -> TermList f -> (TermList f, TermList f)
shareList2 t u
  | sharedList t u = (t, u)
  | otherwise = (children ft', u')
  where
    UnsafeCons ft' u' =
      buildTermList $ do
        emitFun (MkFun 0) (emitTermList t)
        emitTermList u

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
