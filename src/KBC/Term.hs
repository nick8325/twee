-- Terms and evaluation.
{-# LANGUAGE CPP, GeneralizedNewtypeDeriving, TypeSynonymInstances, FlexibleInstances, DeriveFunctor, FlexibleContexts, GADTs #-}
module KBC.Term where

#include "errors.h"
import Data.List
import KBC.Base
#if __GLASGOW_HASKELL__ < 710
import KBC.Utils
#endif
import qualified Data.Map.Strict as Map
import qualified Data.Rewriting.Substitution.Type as Subst

class Minimal a where
  minimal :: a
  skolem  :: Int -> a

minimalTerm :: Minimal f => Tm f v
minimalTerm = Fun minimal []

skolemConst :: Minimal f => Int -> Tm f v
skolemConst n = Fun (skolem n) []

skolemise :: (Minimal f, Numbered v) => Tm f v -> Tm f v
skolemise = foldTerm (skolemConst . number) Fun

class Sized a where
  funSize  :: a -> Int
  funArity :: a -> Int

size :: Sized f => Tm f v -> Int
size (Var _) = 1
size (Fun f xs) = funSize f + sum (map size xs)

orientTerms :: (Sized f, Minimal f, Ord f, Ord v) => Tm f v -> Tm f v -> Maybe Ordering
orientTerms t u
  | t == u = Just EQ
  | lessEq t u = Just LT
  | lessEq u t = Just GT
  | otherwise = Nothing
{-
data Comparison f v =
    Equal
  | NotLessEq
  | LessEq (Maybe (Subst f v)) (Map v Int) Int

minus :: Ord v => Map v Int -> Map v Int -> Map v Int
minus x y =
  Map.mergeWithKey (\_ x y -> if x == y then Nothing else Just (x - y)) id (fmap negate) x y

varMap :: Ord v => Tm f v -> Map v Int
varMap t = Map.fromListWith (+) [(x, 1) | x <- vars t]

lessEq' :: (Sized f, Minimal f, Ord f, Ord v) => Tm f v -> Tm f v -> Comparison f v
lessEq' t@(Fun f []) x | f == minimal =
  LessEq (unify t x) (minus Map.empty (varMap x)) (1-size x)
lessEq' (Var x) (Var y) | x == y =
  LessEq (Just (Subst.fromMap Map.empty)) Map.empty 0
lessEq' _ (Var _) = NotLessEq
lessEq' (Var x) t
  | x `Map.member` m = LessEq Nothing (Map.singleton x 1 `minus` m) (1-size t)
  | otherwise = NotLessEq
lessEq' t@(Fun f ts) u@(Fun g us) =
-}

lessEq :: (Sized f, Minimal f, Ord f, Ord v) => Tm f v -> Tm f v -> Bool
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
