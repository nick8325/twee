-- Tests for the term index.

{-# LANGUAGE TupleSections #-}
module Index(tests) where

import Common
import Twee.Base
import qualified Twee.Index as Index
import Data.Hashable
import Data.List
import Data.Maybe
import Data.Typeable
import Test.Tasty
import Test.Tasty.QuickCheck

newtype IndexOps f = IndexOps [IndexOp f] deriving Show
data IndexOp f = Add (Term f) | Delete (Term f) deriving Show

instance (Hashable f, Eq f, Typeable f, Arbitrary f, Arity f) => Arbitrary (IndexOps f) where
  arbitrary =
    sized $ \n -> IndexOps <$> take n <$> arbOps []
    where
      arbOps ts =
        frequency $
          [(2, do { t <- arbitrary; ops <- arbOps (t:ts); return (Add t:ops) })] ++
          [(1, do { t <- elements ts; ops <- arbOps (delete t ts); return (Delete t:ops) }) | not (null ts)]
  shrink (IndexOps ops) =
    IndexOps <$> shrinkList shr ops
    where
      shr (Add t) = Add <$> shrink t
      shr (Delete t) = Delete <$> shrink t

prop_index_insert :: [Term Func] -> Term Func -> Property
prop_index_insert ts u =
  counterexample (show ts') $
  counterexample (show idx) $
  sort (catMaybes [fmap (,t) (match t u) | t <- ts']) ===
  sort (Index.matches u idx)
  where
    idx = foldr (\t -> Index.insert t t) Index.empty ts
    ts' = map canonicalise ts

prop_index_invariant :: IndexOps Func -> Property
prop_index_invariant (IndexOps ops) =
  flip (foldr (counterexample . show)) idxs $
  property $ Index.invariant (last idxs)
  where
    idxs = scanl (\idx op -> applyIndex op idx) Index.empty ops
    applyIndex (Add t) = Index.insert t t
    applyIndex (Delete t) = Index.delete t t

tests :: TestTree
tests =
  localOption (QuickCheckTests 100000) $
  testGroup "Term indexing"
    [testProperty "Invariant holds" prop_index_invariant,
     testProperty "Inserted terms are found" prop_index_insert]
