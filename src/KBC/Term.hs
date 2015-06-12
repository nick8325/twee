-- Terms and evaluation.
{-# LANGUAGE CPP, GeneralizedNewtypeDeriving, TypeSynonymInstances, FlexibleInstances, DeriveFunctor, FlexibleContexts, GADTs #-}
module KBC.Term where

#include "errors.h"
import Data.List
import KBC.Base
#if __GLASGOW_HASKELL__ < 710
import KBC.Utils
#endif

class Minimal a where
  minimal :: a

class Sized a where
  funSize  :: a -> Rational
  funArity :: a -> Int

size :: Sized f => Tm f v -> Int
size t = ceiling (exactSize t)

exactSize :: Sized f => Tm f v -> Rational
exactSize (Var _) = 1
exactSize (Fun f xs) = funSize f + sum (map exactSize xs)

data Strictness = Strict | Nonstrict deriving (Eq, Ord, Show)

negateStrictness :: Strictness -> Strictness
negateStrictness Strict = Nonstrict
negateStrictness Nonstrict = Strict

orientTerms :: (Sized f, Minimal f, Ord f, Ord v) => Tm f v -> Tm f v -> Maybe Ordering
orientTerms t u
  | t == u = Just EQ
  | lessThan Strict t u = Just LT
  | lessThan Strict u t = Just GT
  | otherwise = Nothing

lessThan :: (Sized f, Minimal f, Ord f, Ord v) => Strictness -> Tm f v -> Tm f v -> Bool
lessThan Nonstrict (Fun f []) _    | f == minimal = True
lessThan Strict _ (Fun f [])       | f == minimal = False
lessThan Nonstrict (Var x) (Var y) | x == y = True
lessThan _ _ (Var _) = False
lessThan _ (Var x) t = x `elem` vars t
lessThan str t@(Fun f ts) u@(Fun g us) =
  xs `isSubsequenceOf` ys &&
  (st < su ||
   (st == su && f < g) ||
   (st == su && f == g && lexLess ts us))
  where
    lexLess [] [] = str == Nonstrict
    lexLess (t:ts) (u:us) =
      (t == u && lexLess ts us) || lessThan Strict t u
    lexLess _ _ = ERROR("incorrect function arity")
    xs = sort (vars t)
    ys = sort (vars u)
    st = exactSize t
    su = exactSize u
