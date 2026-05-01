-- | An implementation of lexicographic path ordering.

{-# LANGUAGE PatternGuards, BangPatterns #-}
module Twee.LPO(lessEqBasic, lessEq, lessIn, lessEqSkolem) where

import Twee.Base hiding (lessEq, lessIn, lessEqSkolem)
import Twee.Equation
import Twee.Constraints hiding (lessEq, lessIn, lessEqSkolem)
import qualified Data.Map.Strict as Map
import Data.Map.Strict(Map)
import Data.Maybe
import Control.Monad
import Twee.Utils
import Data.Intern

lessEqSkolem :: Function f => Term f -> Term f -> Bool
lessEqSkolem (App f Nil) _ | f == minimal = True
lessEqSkolem _ (App f Nil) | f == minimal = False
lessEqSkolem (Var x) (Var y) = x <= y
lessEqSkolem _ (Var _) = False
lessEqSkolem (Var _) _ = True
lessEqSkolem t@(App f ts) u@(App g us)
  | f == g = lexMA ts us
  | f << g = majo ts u
  | otherwise = alpha t us
  where
    lexMA Nil Nil = True
    lexMA (Cons t' ts) (Cons u' us)
      | t' == u' = lexMA ts us
      | lessEqSkolem t' u' = majo ts u
      | otherwise = alpha t us

    majo ts u = and [t /= u && lessEqSkolem t u | t <- unpack ts]
    alpha t us = or [lessEqSkolem t u | u <- unpack us]

-- For testing
lessEqBasic :: Function f => Term f -> Term f -> Bool
lessEqBasic t u = eqModErasure t u || lessBasic t u
  where
    eqModErasure (App f _) _ | f == minimal = True
    eqModErasure (Var x) (Var y) = x == y
    eqModErasure (App f ts) (App g us) =
      f == g && and (zipWith eqModErasure (unpack ts) (unpack us))
    eqModErasure _ _ = False

lessBasic :: Function f => Term f -> Term f -> Bool
lessBasic (App f Nil) (App g _) | f == minimal && g /= minimal = True
lessBasic (Var x) (Var y) = False
lessBasic (Var x) (App _ ts) = x `elem` vars ts
lessBasic t@(App f ts) u@(App g us)
  | or [lessEqBasic t u' | u' <- unpack us] = True
  | f << g && and [lessBasic t' u | t' <- unpack ts] = True
  | f == g = and [lessBasic t' u | t' <- unpack ts] && loop ts us
  where
    loop Nil Nil = False
    loop (Cons t ts) (Cons u us) =
      if t == u then loop ts us else lessBasic t u
lessBasic _ _ = False

-- | Check if one term is less than another in LPO.
lessEq :: Function f => Term f -> Term f -> Bool
lessEq (App f Nil) _ | f == minimal = True
lessEq (Var x) (Var y) = x == y
lessEq _ (Var _) = False
lessEq (Var x) t = x `elem` vars t
lessEq t@(App f ts) u@(App g us)
  | f == g = lexMA ts us
  | f << g = majo ts u
  | otherwise = alpha t us
  where
    lexMA Nil Nil = True
    lexMA (Cons t' ts) (Cons u' us)
      | t' == u' = lexMA ts us
      | lessEq t' u' =
        case unify t' u' of
          Just sub -> majo ts u && lexMA (subst sub ts) (subst sub us)
          Nothing -> majo ts u
      | otherwise = alpha t us

    majo ts u = and [isNothing (unify t u) && lessEq t u | t <- unpack ts]
    alpha t us = or [lessEq t u | u <- unpack us]

lessIn :: Function f => Model f -> Term f -> Term f -> Maybe Strictness
lessIn model t u
  | Just a <- fromTerm t,
    Just b <- fromTerm u,
    Just s <- lessEqInModel model a b = Just s
lessIn model _ (Var _) = Nothing
lessIn model (Var x) t
  | any isJust [lessEqInModel model (Variable x) a | a <- catMaybes (map fromTerm (subterms t))] = Just Strict
  | otherwise = Nothing
lessIn model t@(App f ts) u@(App g us)
  | f == g = lexMA ts us
  | f << g = majo ts u
  | otherwise = alpha t us
  where
    lexMA Nil Nil = Just Nonstrict
    lexMA (Cons t' ts) (Cons u' us) =
      case lessIn model t' u' of
        Just Nonstrict ->
          case (let Just sub = unify t' u' in lexMA (subst sub ts) (subst sub us), majo ts u) of
            (Just Strict, Just Strict) -> Just Strict
            (Just _, Just _) -> Just Nonstrict
            _ -> Nothing
        Just Strict -> majo ts u
        Nothing -> alpha t us

    majo ts u = do
      guard (and [lessIn model t u == Just Strict | t <- unpack ts])
      return Strict
    alpha t us = do
      guard (or [isJust (lessIn model t u) | u <- unpack us])
      return Strict
