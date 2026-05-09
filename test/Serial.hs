-- Tests for serialisation.

{-# LANGUAGE DeriveGeneric, DeriveAnyClass, StandaloneDeriving #-}
module Serial(tests) where

import Test.Tasty
import Test.Tasty.QuickCheck
import Data.Binary.Sharing
import Data.Intern
import GHC.Generics
import Data.Hashable
import qualified Data.ByteString.Lazy as BS
import Data.Int

data Tree = Leaf Int8 | Node Tree Tree | SharedNode (Shared Tree) | SymNode (Sym Tree)
  deriving (Eq, Show, Generic, Binary)
instance Hashable Tree where
  hashWithSalt s (Leaf x) = hashWithSalt s (0 :: Int, x)  
  hashWithSalt s (Node t u) = hashWithSalt s (1 :: Int, t, u)
  hashWithSalt s (SharedNode (Shared t)) = hashWithSalt s (2 :: Int, t)
  hashWithSalt s (SymNode (Sym t)) = hashWithSalt s (2 :: Int, t)

instance Arbitrary Tree where
  arbitrary = sized arb
    where
      arb n =
        frequency [
          (1, Leaf <$> arbitrary),
          (n, Node <$> arb (n `div` 2) <*> arb (n `div` 2)),
          (n, SharedNode . Shared <$> arb (n-1)),
          (n, SymNode . Sym <$> arb (n-1)) ]

  shrink (Leaf n) = Leaf <$> shrink n
  shrink (Node t u) =
    [t, u] ++
    [Node t' u' | (t', u') <- shrink (t, u)]
  shrink (SharedNode (Shared t)) =
    [t] ++ map (SharedNode . Shared) (shrink t)
  shrink (SymNode (Sym t)) =
    [t] ++ map (SymNode . Sym) (shrink t)

{-# NOINLINE prop_tree_serialise #-}
prop_tree_serialise :: Tree -> Property
prop_tree_serialise t =
  counterexample (show (BS.unpack serial)) $
  counterexample (show t') $
  t === t'
  where
    serial = encode t
    t' = decode serial

tests :: TestTree
tests =
  localOption (QuickCheckTests 100000) $
  testGroup "Serialisation" [
     testProperty "Tree serialisation round trip" prop_tree_serialise]
