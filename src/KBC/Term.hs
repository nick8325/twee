{-# LANGUAGE BangPatterns, CPP, PatternGuards, PatternSynonyms, ViewPatterns, RecordWildCards, GeneralizedNewtypeDeriving, RankNTypes, MagicHash, UnboxedTuples #-}
module KBC.Term(module KBC.Term.Core, module KBC.Term) where

#include "errors.h"
import Prelude hiding (lookup)
import KBC.Term.Core
import Data.Primitive
import Control.Monad
import Control.Monad.ST.Strict
import Data.Bits
import Data.Int
import Data.Word
import Data.List hiding (lookup)
import GHC.Types(Int(..))
import GHC.Prim
import GHC.ST hiding (liftST)

instance Show (Term f) where
  show = show . singleton

instance Show (TermList f) where
  show (TermList lo hi arr) =
    "<" ++ show lo ++ "," ++ show hi ++ ">[" ++
      intercalate "," [show (toSymbol (indexByteArray arr n)) | n <- [lo..hi-1]] ++ "]"

toSubst :: Subst f -> [(Int, Term f)]
toSubst subst@(Subst _ n _) =
  [(i, t)
  | i <- [0..n-1],
    Just t <- [lookup subst (MkVar i)] ]

instance Show (Subst f) where
  show = show . toSubst

{-# INLINE lookup #-}
lookup :: Subst f -> Var -> Maybe (Term f)
lookup s x = do
  Cons t Empty <- lookupList s x
  return t

{-# INLINE bound #-}
bound :: TermList f -> Int
bound t = aux 0 t
  where
    aux n Empty = n
    aux n (ConsSym Fun{} t) = aux n t
    aux n (ConsSym (Var (MkVar x)) t)
      | x >= n = aux (x+1) t
      | otherwise = aux n t

{-# INLINE match #-}
match :: Term f -> Term f -> Maybe (Subst f)
match pat t = matchTerms (singleton pat) (singleton t)

{-# INLINE emitTerm #-}
emitTerm :: Term f -> BuildM s f ()
emitTerm t = emitTermList (singleton t)

matchTerms :: TermList f -> TermList f -> Maybe (Subst f)
matchTerms !pat !t = runST $ do
  subst <- newMutableSubst t (bound pat)
  let loop !_ !_ | False = __
      loop Empty _ = fmap Just (freezeSubst subst)
      loop _ Empty = __
      loop (ConsSym (Fun f _) pat) (ConsSym (Fun g _) t)
        | f == g = loop pat t
      -- XXX change to Cons?
      loop (ConsSym (Var x) pat) (Cons t u) = do
        res <- extend subst x t
        case res of
          Nothing -> return Nothing
          Just () -> loop pat u
      loop _ _ = return Nothing
  loop pat t

data CompoundTerm f =
    CFlat  (Term f)
  | CFun   (Fun f) [CompoundTerm f]
  | CVar   Var
  | CSubst (Subst f) (Term f)

flattenTerm :: CompoundTerm f -> Term f
flattenTerm t =
  case flattenTerms [t] of
    Cons u Empty -> u

flattenTerms :: [CompoundTerm f] -> TermList f
flattenTerms ts =
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
    clen (CSubst sub t) = substSize sub (singleton t)

{-# INLINE subst_ #-}
subst_ :: Subst f -> Term f -> Term f
subst_ sub t =
  case substList sub (singleton t) of
    Cons u Empty -> u

substList :: Subst f -> TermList f -> TermList f
substList sub t =
  buildTermList (substSize sub t) $ do
    emitSubstList sub t
    freezeTermList

{-# INLINE substSize #-}
substSize :: Subst f -> TermList f -> Int
substSize !sub = aux 0
  where
    aux n Empty = n
    aux n (ConsSym Fun{} t) = aux (n+1) t
    aux n (ConsSym (Var x) t) =
      case lookupList sub x of
        Nothing -> aux (n+1) t
        Just u  -> aux (n+len u) t

{-# INLINE emitSubst #-}
emitSubst :: Subst f -> Term f -> BuildM s f ()
emitSubst sub t = emitSubstList sub (singleton t)

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
