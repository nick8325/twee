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

lessEq :: (Sized f, Minimal f, Ord f, Ord v) => Tm f v -> Tm f v -> Bool
lessEq (Fun f []) _    | f == minimal = True
lessEq (Var x) (Var y) | x == y = True
lessEq _ (Var _) = False
lessEq (Var x) t = x `elem` vars t
lessEq t@(Fun f ts) u@(Fun g us) =
  xs `isSubsequenceOf` ys &&
  (st < su ||
   (st == su && f < g) ||
   (st == su && f == g && lexLess ts us))
  where
    lexLess [] [] = True
    lexLess (t:ts) (u:us) =
      lessEq t u &&
      case unify t u of
        Nothing -> True
        Just sub
          | Map.null (Subst.toMap sub) -> lexLess ts us
          | otherwise -> lexLess (substf (evalSubst sub) ts) (substf (evalSubst sub) us)
    lexLess _ _ = ERROR("incorrect function arity")
    xs = sort (vars t)
    ys = sort (vars u)
    st = size t
    su = size u
