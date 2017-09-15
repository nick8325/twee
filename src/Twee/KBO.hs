-- | An implementation of Knuth-Bendix ordering.

{-# LANGUAGE PatternGuards #-}
module Twee.KBO(lessEq, lessIn) where

import Twee.Base hiding (lessEq, lessIn)
import Data.List
import Twee.Constraints hiding (lessEq, lessIn)
import qualified Data.Map.Strict as Map
import Data.Map.Strict(Map)
import Data.Maybe
import Control.Monad

-- | Check if one term is less than another in KBO.
lessEq :: Function f => Term f -> Term f -> Bool
lessEq (App f Empty) _ | f == minimal = True
lessEq (Var x) (Var y) | x == y = True
lessEq _ (Var _) = False
lessEq (Var x) t = x `elem` vars t
lessEq t@(App f ts) u@(App g us) =
  (st < su ||
   (st == su && f << g) ||
   (st == su && f == g && lexLess ts us)) &&
  xs `isSubsequenceOf` ys
  where
    lexLess Empty Empty = True
    lexLess (Cons t ts) (Cons u us)
      | t == u = lexLess ts us
      | otherwise =
        lessEq t u &&
        case unify t u of
          Nothing -> True
          Just sub
            | not (allSubst (\_ (Cons t Empty) -> isMinimal t) sub) -> error "weird term inequality"
            | otherwise -> lexLess (subst sub ts) (subst sub us)
    lexLess _ _ = error "incorrect function arity"
    xs = sort (vars t)
    ys = sort (vars u)
    st = size t
    su = size u

-- | Check if one term is less than another in a given model.

-- See "notes/kbo under assumptions" for how this works.

lessIn :: Function f => Model f -> Term f -> Term f -> Maybe Strictness
lessIn model t u =
  case sizeLessIn model t u of
    Nothing -> Nothing
    Just Strict -> Just Strict
    Just Nonstrict -> lexLessIn model t u

sizeLessIn :: Function f => Model f -> Term f -> Term f -> Maybe Strictness
sizeLessIn model t u =
  case minimumIn model m of
    Just l
      | l >  -k -> Just Strict
      | l == -k -> Just Nonstrict
    _ -> Nothing
  where
    (k, m) =
      foldr (addSize id)
        (foldr (addSize negate) (0, Map.empty) (subterms t))
        (subterms u)
    addSize op (App f _) (k, m) = (k + op (size f), m)
    addSize op (Var x) (k, m) = (k, Map.insertWith (+) x (op 1) m)

minimumIn :: Function f => Model f -> Map Var Int -> Maybe Int
minimumIn model t =
  liftM2 (+)
    (fmap sum (mapM minGroup (varGroups model)))
    (fmap sum (mapM minOrphan (Map.toList t)))
  where
    minGroup (lo, xs, mhi)
      | all (>= 0) sums = Just (sum coeffs * size lo)
      | otherwise =
        case mhi of
          Nothing -> Nothing
          Just hi ->
            let coeff = negate (minimum coeffs) in
            Just $
              sum coeffs * size lo +
              coeff * (size lo - size hi)
      where
        coeffs = map (\x -> Map.findWithDefault 0 x t) xs
        sums = scanr1 (+) coeffs

    minOrphan (x, k)
      | varInModel model x = Just 0
      | k < 0 = Nothing
      | otherwise = Just k

lexLessIn :: Function f => Model f -> Term f -> Term f -> Maybe Strictness
lexLessIn _ t u | t == u = Just Nonstrict
lexLessIn cond t u
  | Just a <- fromTerm t,
    Just b <- fromTerm u,
    Just x <- lessEqInModel cond a b = Just x
  | Just a <- fromTerm t,
    any isJust
      [ lessEqInModel cond a b
      | v <- properSubterms u, Just b <- [fromTerm v]] =
        Just Strict
lexLessIn cond (App f ts) (App g us)
  | f == g = loop ts us
  | f << g = Just Strict
  | otherwise = Nothing
  where
    loop Empty Empty = Just Nonstrict
    loop (Cons t ts) (Cons u us)
      | t == u = loop ts us
      | otherwise =
        case lessIn cond t u of
          Nothing -> Nothing
          Just Strict -> Just Strict
          Just Nonstrict ->
            let Just sub = unify t u in
            loop (subst sub ts) (subst sub us)
    loop _ _ = error "incorrect function arity"
lexLessIn _ t _ | isMinimal t = Just Nonstrict
lexLessIn _ _ _ = Nothing
