{-# LANGUAGE TemplateHaskell #-}
import Twee.Constraints
import Twee.Term
import Test.QuickCheck
import Test.QuickCheck.All
import Twee.Pretty
import Text.PrettyPrint
import Data.Rewriting.Term
import Twee.Base
import Control.Monad

lhs, rhs :: Term Fun Var
lhs = (x `f` (y `f` w)) `f` z
rhs = ((x `f` y) `f` z) `f` w

f x y = Fun (F 1 1 2) [x, y]
g x y = Fun (F 2 1 2) [x, y]
h x y = Fun (F 3 1 2) [x, y]
x = Var (V 0)
y = Var (V 1)
z = Var (V 2)
w = Var (V 3)

lhs' = x `f` ((x `g` y) `f` (x `g` x))
rhs' = (y `f` x) `f` (Fun minimal [] `h` (x `f` Fun minimal []))

lhs1 = x `f` (x `f` (y `f` z))
rhs1 = y `f` (z `f` (x `f` x))

lhs2 = f (f z x) (f (f y y) y)
rhs2 = f (f y y) (f (f z z) z)

data Fun = F Int Int Int deriving (Eq, Ord, Show)

instance Pretty Fun where
  pPrint (F f s n) = text "f" <> int f

instance PrettyTerm Fun where
  termStyle _ = uncurried

instance Arbitrary Fun where
  arbitrary = F <$> choose (0, 0) <*> choose (1, 1) <*> choose (2, 2)

instance Minimal Fun where
  minimal = F 0 1 0

instance Sized Fun where
  funSize (F _ s _) = fromIntegral s
  funArity (F _ _ n) = n

newtype Var = V Int deriving (Eq, Ord, Show)

instance Numbered Var where
  number (V x) = x
  withNumber n _ = V n

instance Pretty Var where
  pPrint (V n) = text "X" <> int n

instance Arbitrary Var where
  arbitrary = V <$> choose (0, 2)

instance (Arbitrary f, Arbitrary v, Sized f) => Arbitrary (Term f v) where
  arbitrary =
    sized $ \n ->
      oneof $
        [ Var <$> arbitrary ] ++
        [ do { f <- arbitrary; Fun f <$> vectorOf (funArity f) (resize ((n-1) `div` funArity f) arbitrary) } | n > 0 ]
  shrink (Fun f ts) =
    ts ++
    (Fun f <$> shrinkOne ts)
    where
      shrinkOne [] = []
      shrinkOne (x:xs) =
        [ y:xs | y <- shrink x ] ++
        [ x:ys | ys <- shrinkOne xs ]
  shrink _ = []

data Pair f v = Pair (Tm f v) (Tm f v) deriving Show

instance (Arbitrary f, Arbitrary v, Sized f) => Arbitrary (Pair f v) where
  arbitrary = liftM2 Pair arbitrary arbitrary
  shrink (Pair x y) =
    [ Pair x' y  | x' <- shrink x ] ++
    [ Pair x y'  | y' <- shrink y ] ++
    [ Pair x' y' | x' <- shrink x, y' <- shrink y ]

prop_1 :: Pair Fun Var -> Property
prop_1 (Pair t u) =
  counterexample (prettyShow (Less t u)) $
  counterexample (show (orientTerms t u)) $
  counterexample (prettyShow (less Strict t u)) $
  agrees (orientTerms t u) (less Strict t u)
  where
    agrees (Just LT) (And [])   = True
    agrees (Just EQ) (Or [])    = True
    agrees (Just GT) (Or [])    = True
    agrees Nothing   (Less _ _) = True
    agrees _         _          = False

prop_2 :: Pair Fun Var -> Property
prop_2 (Pair t u) =
  counterexample (prettyShow (Less t u)) $
  counterexample (show (orientTerms t u)) $
  counterexample (show (lessThan Strict t u)) $
  lessThan Strict t u == (orientTerms t u == Just LT)

prop_3 :: Pair Fun Var -> Bool
prop_3 (Pair t u) =
  not (lessThan Strict t u && lessThan Nonstrict u t)

prop_4 :: Pair Fun Var -> Property
prop_4 (Pair t u) =
  t /= u ==> 
  not (lessThan Nonstrict t u && lessThan Nonstrict u t)

prop_5 :: Term Fun Var -> Property
prop_5 t =
  lessThan Nonstrict t t .&&. not (lessThan Strict t t)

prop_6 :: Pair Fun Var -> Property
prop_6 (Pair t u) =
  counterexample (prettyShow t) $
  counterexample (prettyShow u) $
  counterexample (prettyShow (less Strict t u)) $
  counterexample (prettyShow (branches (toConstraint (less Strict t u)))) $
  conjoin [ counterexample (prettyShow sol) $ counterexample (prettyShow (toModel sol)) $ trueIn (toModel sol) (less Strict t u) | sol <- solve (branches (toConstraint (less Strict t u))) ]

prop_7 :: Pair Fun Var -> Property
prop_7 (Pair t u) =
  counterexample (prettyShow t) $
  counterexample (prettyShow u) $
  counterexample (prettyShow (less Strict t u)) $
  conjoin [ counterexample (prettyShow model) $ trueIn model (Less t u) | model <- fmap toModel (solve (branches (toConstraint (less Strict t u)))) ]

prop_8 :: Pair Fun Var -> Pair Fun Var -> Property
prop_8 (Pair t u) (Pair v w) =
  counterexample ("t = " ++ prettyShow t) $
  counterexample ("u = " ++ prettyShow u) $
  counterexample ("v = " ++ prettyShow v) $
  counterexample ("w = " ++ prettyShow w) $
  let c1 = less Strict t u
      c2 = less Strict v w
      b = branches . toConstraint in
  counterexample ("t < u: " ++ prettyShow (b c1)) $
  counterexample ("v < w: " ++ prettyShow (b c2)) $
  counterexample ("t < u && v < w: " ++ prettyShow (b (c1 &&& c2))) $
  counterexample ("t < u && v >= w: " ++ prettyShow (b (c1 &&& negateFormula c2))) $
  not (null (solve (branches (toConstraint (c1 &&& c2))))) ==>
  branches (toConstraint (c1 &&& negateFormula c2)) /= branches (toConstraint c1)

return []
--main = $forAllProperties (quickCheckWithResult stdArgs { maxSuccess = 1000000 })
main = quickCheckWith stdArgs { maxSuccess = 1000000 } prop_8
