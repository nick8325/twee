{-# LANGUAGE TemplateHaskell, FlexibleInstances, FlexibleContexts, UndecidableInstances #-}
import Twee.Constraints
import Twee.Term hiding (subst)
import Test.QuickCheck
import Test.QuickCheck.All
import Twee.Pretty
import qualified Twee.LPO as Ord
import Text.PrettyPrint
import Twee.Base
import Twee.Rule
import Control.Monad
import qualified Data.Map as Map
import Data.Maybe
import Data.Ord
import Data.List

data Func = F Int Int Int deriving (Eq, Ord, Show)

fromFunc :: Fun Func -> Func
fromFunc (MkFun n) = F n 1 2

toFunc :: Func -> Fun Func
toFunc (F n 1 2) = MkFun n

instance Pretty Func where
  pPrint (F f s n) = text "f" <> int f

instance Pretty (Fun Func) where pPrint = pPrint . fromFunc

instance PrettyTerm Func where
  termStyle _ = uncurried

instance Arbitrary (Subst Func) where
  arbitrary = fmap flattenSubst (liftM2 zip (fmap nub arbitrary) (infiniteListOf arbitrary))

instance Arbitrary Func where
  arbitrary = F <$> choose (1, 1) <*> choose (1, 1) <*> choose (2, 2)

instance Arbitrary (Fun Func) where arbitrary = fmap toFunc arbitrary

instance Minimal Func where
  minimal = MkFun 0

instance Sized Func where
  size (F _ s _) = fromIntegral s

instance Sized (Fun Func) where
  size = size . fromFunc

instance Arity Func where
  arity f = let F _ _ n = fromFunc f in n

instance Arbitrary Var where arbitrary = fmap MkVar (choose (0, 1))

instance (Arbitrary (Fun f), Sized f, Arity f) => Arbitrary (Term f) where
  arbitrary =
    sized $ \n ->
      oneof $
        [ var <$> arbitrary ] ++
        [ do { f <- arbitrary; fun f <$> vectorOf (arity f) (resize ((n-1) `div` arity f) arbitrary) } | n > 0 ]
  shrink (Fun f ts) =
    fromTermList ts ++
    (fun f <$> shrinkOne (fromTermList ts))
    where
      shrinkOne [] = []
      shrinkOne (x:xs) =
        [ y:xs | y <- shrink x ] ++
        [ x:ys | ys <- shrinkOne xs ]
  shrink _ = []

data Pair f = Pair (Term f) (Term f) deriving Show

instance (Arbitrary f, Arbitrary (Fun f), Arity f, Sized f) => Arbitrary (Pair f) where
  arbitrary = liftM2 Pair arbitrary arbitrary
  shrink (Pair x y) =
    [ Pair x' y  | x' <- shrink x ] ++
    [ Pair x y'  | y' <- shrink y ] ++
    [ Pair x' y' | x' <- shrink x, y' <- shrink y ]

instance Skolem Func
instance SizedFun Func
instance OrdFun Func where
  compareFun = comparing fromFunc
instance Function Func
instance Ordered Func where
  lessIn = Ord.lessIn
  lessEq = Ord.lessEq

lessThan Strict t u = lessIn (modelFromOrder []) t u == Just Strict
lessThan Nonstrict t u = isJust (lessIn (modelFromOrder []) t u)

instance Function f => Arbitrary (Model f) where
  arbitrary = fmap (modelFromOrder . map Variable . nub) arbitrary
  shrink = weakenModel

prop_1 :: Model Func -> Pair Func -> Subst Func -> Property
prop_1 model (Pair t u) sub =
  counterexample ("Model: " ++ prettyShow model) $
  counterexample ("Subst: " ++ prettyShow sub) $
  conjoin $ do
    r@(Rule _ t' u') <- orient (t :=: u)
    return $
      counterexample ("LHS:   " ++ prettyShow t') $
      counterexample ("RHS:   " ++ prettyShow u') $
      counterexample ("Rule:  " ++ prettyShow r) $
      counterexample ("Inst:  " ++ prettyShow (Rule Oriented (subst sub t') (subst sub u'))) $
      counterexample ("Res:   " ++ show (lessIn model (subst sub u') (subst sub t'))) $
      not (reducesInModel model r sub) || isJust (lessIn model (subst sub u') (subst sub t'))

prop_2 :: Model Func -> Pair Func -> Bool
prop_2 model (Pair t u) =
  not (lessIn model t u == Just Strict && isJust (lessIn model u t))

prop_3 :: Pair Func -> Bool
prop_3 (Pair t u) =
  not (lessThan Strict t u && lessThan Nonstrict u t)

prop_4 :: Pair Func -> Property
prop_4 (Pair t u) =
  t /= u ==> 
  not (lessThan Nonstrict t u && lessThan Nonstrict u t)

prop_5 :: Term Func -> Property
prop_5 t =
  lessThan Nonstrict t t .&&. not (lessThan Strict t t)

-- return []
-- main = $forAllProperties (quickCheckWithResult stdArgs { maxSuccess = 1000000 })

main = quickCheckWith stdArgs { maxSuccess = 1000000 } prop_1

x, y, z :: Var
x = MkVar 0
y = MkVar 1
z = MkVar 2

times, plus :: Fun Func
plus = MkFun 1
times = MkFun 2

a, b, c :: Term Func
a = fun plus [fun times [var x, var y], fun times [var z, var y]]
b = fun plus [fun times [var y, var z], fun times [var y, var x]]
c = fun plus [fun times [var y, var x], fun times [var y, var z]]

-- main = do
--   prettyPrint b
--   prettyPrint a
--   print (lessIn (modelFromOrder (map Variable [x, y, z])) b a)
--   print (lessIn (modelFromOrder (map Variable [x, y, z])) c b)
--   print (lessIn (modelFromOrder (map Variable [x, y, z])) a c)
