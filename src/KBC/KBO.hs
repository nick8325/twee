{-# LANGUAGE CPP #-}
module KBC.KBO where

#include "errors.h"
import KBC.Base
import KBC.Term hiding (lessEq, lessEqIn)
import Data.List
import KBC.Constraints
import qualified Data.Map.Strict as Map
import qualified Data.Rewriting.Substitution.Type as Subst
import qualified Solver.FourierMotzkin.Internal as FM
import Data.Maybe

lessEq :: (Sized f, Minimal f, Ord f) => Tm f -> Tm f -> Bool
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
        -- XXXX t must be u with some variables replaced with minimal constant
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

lessEqIn :: (Function f, Sized f) => [Formula f] -> Tm f -> Tm f -> Bool
lessEqIn _ t _       |  t == minimalTerm = True
lessEqIn _ (Var x) (Var y) | x == y = True
lessEqIn cond (Var x) (Var y) = Less x y `elem` cond || LessEq x y `elem` cond
lessEqIn _ _ (Var _) = False
lessEqIn cond (Var x) t = x `elem` vars t || or [ y `elem` vars t | Less x' y <- cond, x == x' ] || or [ y `elem` vars t | LessEq x' y <- cond, x == x' ]
lessEqIn cond t@(Fun f ts) u@(Fun g us)
  | f < g     = nonstrict
  | f > g     = strict
  | otherwise = nonstrict && (strict || lexLess ts us)
  where
    nonstrict =
      (xs `isSubsequenceOf` ys && st <= su) || termSizeIs (FM.>/=)
    strict    =
      (xs `isSubsequenceOf` ys && st <  su) || termSizeIs (FM.>==)

    termSizeIs op = isNothing (FM.solve prob)
      where
        prob = FM.addConstraints [sz `op` 0] prob0
        sz = termSize t - termSize u

    prob0 =
      FM.problem $
        [FM.var x FM.<== FM.var y | Less x y <- cond] ++
        [FM.var x FM.<== FM.var y | LessEq x y <- cond] ++
        [FM.var x FM.>== 1 | x <- Map.keys (FM.vars (termSize t - termSize u))]

    termSize (Var x) = FM.var x
    termSize (Fun f xs) = FM.scalar (fromIntegral (size f)) + sum (map termSize xs)

    lexLess [] [] = True
    lexLess (t:ts) (u:us) =
      lessEqIn cond t u &&
      case unify t u of
        Nothing -> True
        Just sub
          | Map.null (Subst.toMap sub) -> lexLess ts us
          | otherwise ->
            lexLess (substf (evalSubst sub) ts) (substf (evalSubst sub) us)
    lexLess _ _ = ERROR("incorrect function arity")
    xs = sort (vars t)
    ys = sort (vars u)
    st = fromIntegral (size t)
    su = fromIntegral (size u)
