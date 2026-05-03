module Main where

import qualified Index
import qualified Nest
import qualified Ordering
import qualified TermOrder
import qualified Terms
import Test.Tasty

tests :: TestTree
tests =
  testGroup "Twee tests"
    [Terms.tests,
    TermOrder.tests,
    Ordering.tests,
    Index.tests,
    Nest.tests]

main = defaultMain tests
