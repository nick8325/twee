-- Terms and evaluation.
{-# LANGUAGE CPP, GeneralizedNewtypeDeriving, TypeSynonymInstances, FlexibleInstances, DeriveFunctor, FlexibleContexts, GADTs #-}
module KBC.Term where

#include "errors.h"
#if __GLASGOW_HASKELL__ < 710
import Control.Applicative
#endif
import Control.Monad
import Data.List
import Data.Ord
import KBC.Base
import KBC.Utils

class Minimal a where
  minimal :: a

class Sized a where
  funSize  :: a -> Rational
  funArity :: a -> Int

-- Term ordering - size, skeleton, generality.
-- Satisfies the property:
-- if measure (schema t) < measure (schema u) then t < u.
type Measure f v = (Rational, Int, MeasureFuns f (), Int, [v])
measure :: (Sized f, Ord f, Ord v) => Tm f v -> Measure f v
measure t = (exactSize t, -length (vars t),
             MeasureFuns (rename (const ()) t), -length (usort (vars t)), vars t)

newtype MeasureFuns f v = MeasureFuns (Tm f v)
instance (Sized f, Ord f, Ord v) => Eq (MeasureFuns f v) where
  t == u = compare t u == EQ
instance (Sized f, Ord f, Ord v) => Ord (MeasureFuns f v) where
  compare (MeasureFuns t) (MeasureFuns u) = compareFuns t u

compareFuns :: (Sized f, Ord f, Ord v) => Tm f v -> Tm f v -> Ordering
compareFuns (Var x) (Var y) = compare x y
compareFuns Var{} Fun{} = LT
compareFuns Fun{} Var{} = GT
compareFuns (Fun f ts) (Fun g us) =
  compare f g `orElse`
  compare (map MeasureFuns ts) (map MeasureFuns us)

-- Take two terms and find the first place where they differ.
compareTerms :: (Sized f, Ord f, Ord v) => Tm f v -> Tm f v -> Maybe (Tm f v, Tm f v, Ordering)
compareTerms t u =
  here (comparing exactSize t u) `mplus`
  case (t, u) of
    (Var x, Var y) -> here (compare x y)
    (Var{}, Fun{}) -> here LT
    (Fun{}, Var{}) -> here GT
    (Fun f xs, Fun g ys) ->
      here (compare f g) `mplus`
      msum (zipWith compareTerms xs ys)
  where
    here EQ = Nothing
    here ord = Just (t, u, ord)

-- Reduction ordering (i.e., a partial order closed under substitution).
orientTerms :: (Sized f, Ord f, Ord v) => Tm f v -> Tm f v -> Maybe Ordering
orientTerms t u =
  case compareTerms t u of
    Just (t', u', LT) -> do { guard (check t u t' u'); return LT }
    Just (t', u', GT) -> do { guard (check u t u' t'); return GT }
    Just (_,  _,  EQ) -> ERROR("invalid result from compareTerms")
    Nothing           -> Just EQ
  where
    check t u t' u' =
      sort (vars t') `isSubsequenceOf` sort (vars u') &&
      sort (vars t)  `isSubsequenceOf` sort (vars u)

simplerThan :: (Sized f, Ord f, Ord v) => Tm f v -> Tm f v -> Bool
t `simplerThan` u = orientTerms t u == Just LT

size :: Sized f => Tm f v -> Int
size t = ceiling (exactSize t)

exactSize :: Sized f => Tm f v -> Rational
exactSize (Var _) = 1
exactSize (Fun f xs) = funSize f + sum (map exactSize xs)
