-- Common code used by the rest of the tests.

{-# LANGUAGE FlexibleInstances, ScopedTypeVariables, DeriveGeneric, DeriveAnyClass #-}
module Common where

import Data.Intern
import Twee.Base
import Twee.Constraints
import Twee.Equation
import Twee.Utils
import qualified Twee.KBO as KBO
import Control.Monad
import Data.Hashable
import Data.List
import Data.Maybe
import Data.Typeable
import GHC.Generics
import Test.QuickCheck hiding (Function)
import Text.Printf

data Func = Min | Skolem Int | F Int Integer deriving (Eq, Ord, Generic, Hashable)

instance Show Func where
  show Min = "m"
  show (Skolem n) = printf "sk%d" n
  show (F x y) = printf "f%d_%d" x y

instance Pretty Func where
  pPrint Min = text "m"
  pPrint (Skolem m) = text "sk" <#> int m
  pPrint (F 3 _) = text "a"
  pPrint (F 4 _) = text "b"
  pPrint (F 5 _) = text "zero"
  pPrint (F 6 _) = text "plus"
  pPrint (F 7 _) = text "times"
  pPrint (F f _) = text "f" <#> int f
instance PrettyTerm Func
instance Arbitrary (Subst Func) where
  arbitrary = fmap fromJust (fmap listToSubst (liftM2 zip (fmap nub arbitrary) (infiniteListOf arbitrary)))
instance Arbitrary Func where
  arbitrary =
    frequency
      [(10, F <$> choose (0, 2) <*> choose (1, 3)),
       (2, Skolem <$> choose (0, 2)),
       (1, return Min)]
instance Minimal Func where
  minimal = intern Min
  skolem n = intern (Skolem n)
instance KBO.Sized Func where
  size (F _ n) = n
  size _ = 1
instance Weighted Func where
  weight (F _ n) = fromIntegral n
  weight _ = 1
instance KBO.ArgWeighted Func where argWeight _ = 1
class Arity f where
  arity :: f -> Int
instance Arity Func where
  arity (F 0 _) = 0
  arity (F 1 _) = 1
  arity (F 2 _) = 2
  arity (F 3 _) = 0 -- a
  arity (F 4 _) = 0 -- b
  arity (F 5 _) = 0 -- zero
  arity (F 6 _) = 2 -- plus
  arity (F 7 _) = 2 -- times
  arity _ = 0
instance EqualsBonus Func

instance Arbitrary Var where arbitrary = fmap V (choose (0, 3))
instance (Hashable f, Eq f, Typeable f, Arbitrary f, Arity f) => Arbitrary (Sym f) where
  arbitrary = fmap intern arbitrary

instance (Hashable f, Eq f, Typeable f, Arbitrary f, Arity f) => Arbitrary (Term f) where
  arbitrary =
    sized $ \n ->
      oneof $
        [ build <$> var <$> arbitrary ] ++
        [ do { f <- arbitrary; build <$> app (Sym f) <$> vectorOf (arity f) (resize ((n-1) `div` arity f) arbitrary :: Gen (Term f)) } | n > 0 ]
  shrink (App f ts0) =
    ts ++ (build <$> app f <$> shrinkOne ts)
    where
      ts = unpack ts0
      shrinkOne [] = []
      shrinkOne (x:xs) =
        [ y:xs | y <- shrink x ] ++
        [ x:ys | ys <- shrinkOne xs ]
  shrink _ = []

instance (Hashable f, Eq f, Typeable f, Arbitrary f, Arity f) => Arbitrary (TermList f) where
  arbitrary = buildList <$> listOf (arbitrary :: Gen (Term f))
  shrink = map buildList . shrink . unpack

data Pair f = Pair (Term f) (Term f) deriving Show

instance (Hashable f, Eq f, Typeable f, Arbitrary f, Arity f) => Arbitrary (Pair f) where
  arbitrary = liftM2 Pair arbitrary arbitrary
  shrink (Pair x y) =
    [ Pair x' y  | x' <- shrink x ] ++
    [ Pair x y'  | y' <- shrink y ] ++
    [ Pair x' y' | x' <- shrink x, y' <- shrink y ]

instance (Hashable f, Eq f, Typeable f, Arbitrary f, Arity f) => Arbitrary (Equation f) where
  arbitrary = do
    Pair t u <- arbitrary
    return (t :=: u)
  shrink (t :=: u) = [t' :=: u' | Pair t' u' <- shrink (Pair t u)]

instance Ordered Func where
  lessIn = KBO.lessIn
  lessEq = KBO.lessEq
  lessEqSkolem = KBO.lessEqSkolem

instance Function f => Arbitrary (Model f) where
  arbitrary = fmap (modelFromOrder . map Variable . nub) arbitrary
  shrink = weakenModel

genSubst :: [Var] -> Gen (Subst Func)
genSubst xs = do
  let xs' = usort xs
  ts <- sequence [arbitrary | _ <- xs']
  let Just sub = listToSubst (zip xs' ts)
  return sub
