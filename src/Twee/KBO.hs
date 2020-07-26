-- | An implementation of Knuth-Bendix ordering.

{-# LANGUAGE PatternGuards, BangPatterns #-}
module Twee.KBO(lessEq, lessIn, lessEqSkolem, Sized(..), Weighted(..)) where

import Twee.Base hiding (lessEq, lessIn, lessEqSkolem)
import Twee.Equation
import Twee.Constraints hiding (lessEq, lessIn, lessEqSkolem)
import qualified Data.Map.Strict as Map
import Data.Map.Strict(Map)
import Data.Maybe
import Control.Monad
import Twee.Utils

lessEqSkolem :: (Function f, Sized f, Weighted f) => Term f -> Term f -> Bool
lessEqSkolem !t !u
  | m < n = True
  | m > n = False
  where
    m = size t
    n = size u
lessEqSkolem (App x Empty) _
  | x == minimal = True
lessEqSkolem _ (App x Empty)
  | x == minimal = False
lessEqSkolem (Var x) (Var y) = x <= y
lessEqSkolem (Var _) _ = True
lessEqSkolem _ (Var _) = False
lessEqSkolem (App (F _ f) ts) (App (F _ g) us) =
  case compare f g of
    LT -> True
    GT -> False
    EQ ->
      let loop Empty Empty = True
          loop (Cons t ts) (Cons u us)
            | t == u = loop ts us
            | otherwise = lessEqSkolem t u
      in loop ts us

-- | Check if one term is less than another in KBO.
{-# SCC lessEq #-}
lessEq :: (Function f, Sized f, Weighted f) => Term f -> Term f -> Bool
lessEq (App f Empty) _ | f == minimal = True
lessEq (Var x) (Var y) | x == y = True
lessEq _ (Var _) = False
lessEq (Var x) t = x `elem` vars t
lessEq t@(App f ts) u@(App g us) =
  (st < su ||
   (st == su && f << g) ||
   (st == su && f == g && lexLess ts us)) &&
  xs `lessVars` ys
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
    xs = weightedVars t
    ys = weightedVars u
    st = size t
    su = size u

    [] `lessVars` _ = True
    ((x,k1):xs) `lessVars` ((y,k2):ys)
      | x == y = k1 <= k2 && xs `lessVars` ys
      | x > y  = ((x,k1):xs) `lessVars` ys
    _ `lessVars` _ = False

-- | Check if one term is less than another in a given model.

-- See "notes/kbo under assumptions" for how this works.

{-# SCC lessIn #-}
lessIn :: (Function f, Sized f, Weighted f) => Model f -> Term f -> Term f -> Maybe Strictness
lessIn model t u =
  case sizeLessIn model t u of
    Nothing -> Nothing
    Just Strict -> Just Strict
    Just Nonstrict -> lexLessIn model t u

sizeLessIn :: (Function f, Sized f, Weighted f) => Model f -> Term f -> Term f -> Maybe Strictness
sizeLessIn model t u =
  case minimumIn model m of
    Just l
      | l >  -k -> Just Strict
      | l == -k -> Just Nonstrict
    _ -> Nothing
  where
    (k, m) =
      add 1 u (add (-1) t (0, Map.empty))

    add a (App f ts) (k, m) =
      foldr (add (a * argWeight f)) (k + a * size f, m) (unpack ts)
    add a (Var x) (k, m) = (k, Map.insertWith (+) x a m)

minimumIn :: (Function f, Sized f) => Model f -> Map Var Integer -> Maybe Integer
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

lexLessIn :: (Function f, Sized f, Weighted f) => Model f -> Term f -> Term f -> Maybe Strictness
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

class Sized a where
  -- | Compute the size.
  size  :: a -> Integer

class Weighted f where
  argWeight :: f -> Integer

instance (Weighted f, Labelled f) => Weighted (Fun f) where
  argWeight = argWeight . fun_value

weightedVars :: (Weighted f, Labelled f) => Term f -> [(Var, Integer)]
weightedVars t = collate sum (loop 1 t)
  where
    loop k (Var x) = [(x, k)]
    loop k (App f ts) =
      concatMap (loop (k * argWeight f)) (unpack ts)

instance (Labelled f, Sized f) => Sized (Fun f) where
  size = size . fun_value

instance (Labelled f, Sized f, Weighted f) => Sized (TermList f) where
  size = aux 0
    where
      aux n Empty = n
      aux n (Cons (App f t) u) =
        aux (n + size f + argWeight f * size t) u
      aux n (Cons (Var _) t) = aux (n+1) t

instance (Labelled f, Sized f, Weighted f) => Sized (Term f) where
  size = size . singleton

instance (Labelled f, Sized f, Weighted f) => Sized (Equation f) where
  size (x :=: y) = size x + size y

