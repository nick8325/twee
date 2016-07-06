{-# LANGUAGE CPP, PatternGuards #-}
module Twee.LPO where

#include "errors.h"
import Twee.Base hiding (lessEq, lessIn)
import Twee.Constraints hiding (lessEq, lessIn)
import Data.Maybe
import Control.Monad

lessEq :: Function f => Term f -> Term f -> Bool
lessEq (Var x) (Var y) = x == y
lessEq (Var x) t = x `elem` vars t
lessEq (Fun f _) (Var _) = f == minimal
lessEq t@(Fun f ts) u@(Fun g us) =
  case compare f g of
    LT ->
      and [ lessEq t u | t <- unpack ts ] &&
      and [ isNothing (match u t) | t <- unpack ts ]
    EQ -> lexLess t u ts us
    GT -> or [ lessEq t u | u <- unpack us ]
  where
    lexLess _ _ Empty Empty = True
    lexLess t u (Cons t' ts) (Cons u' us)
      | t' == u' = lexLess t u ts us
      | lessEq t' u' =
        and [ lessEq t u | t <- unpack ts ] &&
        and [ isNothing (match u t) | t <- unpack ts ] &&
        case match u' t' of
          Nothing -> True
          Just sub ->
            lexLess (subst sub t) (subst sub u) (subst sub ts) (subst sub us)
      | otherwise =
        or [ lessEq t u | u <- unpack us ]
    lexLess _ _ _ _ = ERROR("incorrect function arity")

lessIn :: Function f => Model f -> Term f -> Term f -> Maybe Strictness
lessIn model (Var x) t
  | or [isJust (varLessIn x u) | u <- properSubterms t] = Just Strict
  | Just str <- varLessIn x t = Just str
  | otherwise = Nothing
  where
    varLessIn x t = fromTerm t >>= lessEqInModel model (Variable x)
lessIn model t (Var x) = do
  a <- fromTerm t
  lessEqInModel model a (Variable x)
lessIn model t@(Fun f ts) u@(Fun g us) =
  case compare f g of
    LT -> do
      guard (and [ lessIn model t u == Just Strict | t <- unpack ts ])
      return Strict
    EQ -> lexLess t u ts us
    GT -> do
      msum [ lessIn model t u | u <- unpack us ]
      return Strict
  where
    lexLess _ _ Empty Empty = Just Nonstrict
    lexLess t u (Cons t' ts) (Cons u' us)
      | t' == u' = lexLess t u ts us
      | Just str <- lessIn model t' u' = do
        guard (and [ lessIn model t u == Just Strict | t <- unpack ts ])
        case str of
          Strict -> Just Strict
          Nonstrict ->
            let Just sub = unify t' u' in
            lexLess (subst sub t) (subst sub u) (subst sub ts) (subst sub us)
      | otherwise = do
        msum [ lessIn model t u | u <- unpack us ]
        return Strict
    lexLess _ _ _ _ = ERROR("incorrect function arity")
