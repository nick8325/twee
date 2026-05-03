-- Tests for basic term functionality.

{-# LANGUAGE StandaloneDeriving, DeriveGeneric #-}
module Terms(tests) where

import Common
import Twee.Base
import Twee.Term.Core
import Data.Int
import GHC.Generics
import Test.Tasty
import Test.Tasty.QuickCheck

deriving instance Eq Symbol
deriving instance Generic Symbol

instance Arbitrary Symbol where
  arbitrary =
    Symbol <$>
      arbitrary <*>
      fmap getLarge arbitrary <*>
      (fmap (fromIntegral . getLarge) (arbitrary :: Gen (Large Int32)) `suchThat` (> 0) `suchThat` (< 2^31))
  shrink s =
    filter ok (genericShrink s)
    where
      ok s = Twee.Term.Core.size s > 0

prop_paths :: Term Func -> Property
prop_paths t =
  forAllShrink (choose (0, len t-1)) shrink $ \n ->
    counterexample (show (positionToPath t n)) $
    pathToPosition t (positionToPath t n) === n
  -- implies x = positionToPath t n ==> positionToPath t (pathToPosition t x) == x

prop_symbol :: Int64 -> Property
prop_symbol n =
  fromSymbol (toSymbol n) === n
  -- implies x = toSymbol n ==> toSymbol (fromSymbol x) == x

tests :: TestTree
tests =
  localOption (QuickCheckTests 1000000) $
  testGroup "Terms" [
    testProperty "Paths to positions round trip" prop_paths,
    testProperty "Symbols to Int64 round trip" prop_symbol]
