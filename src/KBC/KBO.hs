{-# LANGUAGE CPP, PatternGuards #-}
module KBC.KBO where

#include "errors.h"
import KBC.Base hiding (lessEq, lessIn)
import Data.List
import KBC.Constraints
import qualified Data.Map.Strict as Map
import Data.Map.Strict(Map)
import qualified Data.Rewriting.Substitution.Type as Subst
import Data.Maybe
import Control.Monad

lessEq :: Function f => Tm f -> Tm f -> Bool
lessEq (Fun f []) _    | f == minimal = True
lessEq (Var x) (Var y) | x == y = True
lessEq _ (Var _) = False
lessEq (Var x) t = x `elem` vars t
lessEq t@(Fun f ts) u@(Fun g us) =
  (st < su ||
   (st == su && f < g) ||
   (st == su && f == g && lexLess ts us)) &&
  xs `isSubsequenceOf` ys
  where
    lexLess [] [] = True
    lexLess (t:ts) (u:us)
      | t == u = lexLess ts us
      | otherwise =
        lessEq t u &&
        case unify t u of
          Nothing -> True
          Just sub
            | or [t /= minimalTerm | t <- Map.elems (Subst.toMap sub)] -> ERROR("weird term inequality")
            | otherwise -> lexLess (substf (evalSubst sub) ts) (substf (evalSubst sub) us)
    lexLess _ _ = ERROR("incorrect function arity")
    xs = sort (vars t)
    ys = sort (vars u)
    st = size t
    su = size u

lessIn :: Function f => Model f -> Tm f -> Tm f -> Maybe Strictness
lessIn model t u =
  case sizeLessIn model t u of
    Nothing -> Nothing
    Just Strict -> Just Strict
    Just Nonstrict -> lexLessIn model t u

sizeLessIn :: Function f => Model f -> Tm f -> Tm f -> Maybe Strictness
sizeLessIn model t u =
  case minimumIn model m of
    Just l
      | l < k  -> Just Strict
      | l == k -> Just Nonstrict
    _ -> Nothing
  where
    (k, m) =
      foldr (addSize id)
        (foldr (addSize negate) (0, Map.empty) (symbols t))
        (symbols u)
    addSize op (Left f) (k, m) = (k + op (size f), m)
    addSize op (Right x) (k, m) = (k, Map.insertWith (+) x (op 1) m)

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

lexLessIn :: Function f => Model f -> Tm f -> Tm f -> Maybe Strictness
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
lexLessIn cond (Fun f ts) (Fun g us) =
  case compare f g of
    LT -> Just Strict
    GT -> Nothing
    EQ -> loop ts us
  where
    loop [] [] = Just Nonstrict
    loop (t:ts) (u:us)
      | t == u = loop ts us
      | otherwise =
        case lessIn cond t u of
          Nothing -> Nothing
          Just Strict -> Just Strict
          Just Nonstrict ->
            let Just sub = unify t u in
            loop (substf (evalSubst sub) ts) (substf (evalSubst sub) us)
    loop _ _ = ERROR("incorrect function arity")
lexLessIn model t _ | t == minimalTerm = Just Nonstrict
lexLessIn model _ _ = Nothing
