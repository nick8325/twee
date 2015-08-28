-- Terms and substitutions, implemented using flatterms.
-- This module implements the usual term manipulation stuff
-- (matching, unification, etc.) on top of the primitives
-- in KBC.Term.Core.
{-# LANGUAGE BangPatterns, CPP, PatternSynonyms #-}
module KBC.Term(
  module KBC.Term,
  -- Stuff from KBC.Term.Core.
  Term, TermList, len,
  pattern Empty, pattern Cons, pattern ConsSym,
  pattern UnsafeCons, pattern UnsafeConsSym,
  Fun(..), Var(..), pattern Var, pattern Fun, singleton,
  BuildM, buildTermList, freezeTermList,
  emitRoot, emitFun, emitVar, emitTermList,
  Subst, substSize, lookupList,
  MutableSubst, newMutableSubst, freezeSubst, extend) where

#include "errors.h"
import Prelude hiding (lookup)
import KBC.Term.Core hiding (subst)
import Control.Monad
import Control.Monad.ST.Strict
import Data.List hiding (lookup)

--------------------------------------------------------------------------------
-- A helper datatype for building terms.
--------------------------------------------------------------------------------

-- An algebraic data type for terms, with flatterms or substitutions applied
-- to flatterms at the leaf.
data CompoundTerm f =
    CFlat  (Term f)
  | CFun   (Fun f) [CompoundTerm f]
  | CVar   Var
  | CSubst (Subst f) (Term f)

-- Turn a compound term into a flatterm.
flattenTerm :: CompoundTerm f -> Term f
flattenTerm t =
  case flattenList [t] of
    Cons u Empty -> u

-- Turn a list of compound term into a list of flatterms.
flattenList :: [CompoundTerm f] -> TermList f
flattenList ts =
  buildTermList (sum (map clen ts)) $ do
    let
      loop [] = return ()
      loop (CFlat t:ts) = do
        emitTerm t
        loop ts
      loop (CFun f ts:us) = do
        emitFun f (loop ts)
        loop us
      loop (CVar x:ts) = do
        emitVar x
        loop ts
      loop (CSubst sub t:ts) = do
        emitSubst sub t
        loop ts
    loop ts
    freezeTermList
  where
    clen (CFlat t) = len (singleton t)
    clen (CFun _ ts) = 1 + sum (map clen ts)
    clen (CVar _) = 1
    clen (CSubst sub t) = substTermSize sub (singleton t)

--------------------------------------------------------------------------------
-- Substitution.
--------------------------------------------------------------------------------

{-# INLINE subst #-}
subst :: Subst f -> Term f -> Term f
subst sub t =
  case substList sub (singleton t) of
    Cons u Empty -> u

substList :: Subst f -> TermList f -> TermList f
substList sub t =
  buildTermList (substTermSize sub t) $ do
    emitSubstList sub t
    freezeTermList

-- Work out the size of a term after substitution.
{-# INLINE substTermSize #-}
substTermSize :: Subst f -> TermList f -> Int
substTermSize !sub = aux 0
  where
    aux n Empty = n
    aux n (ConsSym Fun{} t) = aux (n+1) t
    aux n (ConsSym (Var x) t) =
      case lookupList sub x of
        Nothing -> aux (n+1) t
        Just u  -> aux (n+len u) t

-- Emit a substitution applied to a term.
{-# INLINE emitSubst #-}
emitSubst :: Subst f -> Term f -> BuildM s f ()
emitSubst sub t = emitSubstList sub (singleton t)

-- Emit a substitution applied to a term list.
{-# INLINE emitSubstList #-}
emitSubstList :: Subst f -> TermList f -> BuildM s f ()
emitSubstList !sub = aux
  where
    aux Empty = return ()
    aux (Cons v@(Var x) ts) = do
      case lookupList sub x of
        Nothing -> emitVar x
        Just u  -> emitTermList u
      aux ts
    aux (Cons x@(Fun f ts) us) = do
      emitFun f (aux ts)
      aux us

--------------------------------------------------------------------------------
-- Matching.
--------------------------------------------------------------------------------

{-# INLINE match #-}
match :: Term f -> Term f -> Maybe (Subst f)
match pat t = matchList (singleton pat) (singleton t)

matchList :: TermList f -> TermList f -> Maybe (Subst f)
matchList !pat !t = runST $ do
  subst <- newMutableSubst t (bound pat)
  let loop !_ !_ | False = __
      loop Empty _ = fmap Just (freezeSubst subst)
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
-- Miscellaneous stuff.
--------------------------------------------------------------------------------

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

{-# INLINE emitTerm #-}
emitTerm :: Term f -> BuildM s f ()
emitTerm t = emitTermList (singleton t)

-- Find the lowest-numbered variable that doesn't appear in a term.
{-# INLINE bound #-}
bound :: TermList f -> Int
bound t = aux 0 t
  where
    aux n Empty = n
    aux n (ConsSym Fun{} t) = aux n t
    aux n (ConsSym (Var (MkVar x)) t)
      | x >= n = aux (x+1) t
      | otherwise = aux n t
