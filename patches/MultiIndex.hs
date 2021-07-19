{-# LANGUAGE RecordWildCards, ScopedTypeVariables, FlexibleContexts #-}
module Twee.MultiIndex(
  MultiIndex,
  empty, insert, delete, index,
  approxMatches, matches, lookup) where

import Prelude hiding (lookup)
import Twee.Base hiding (lookup, empty)
import Twee.Rule
import Twee.Index hiding (insert, delete, empty)
import qualified Twee.Index as Index
import qualified Data.Map.Strict as Map
import Data.Map.Strict(Map)

data MultiIndex idx f a =
  MultiIndex (idx -> a -> Bool) (Map idx (Index f a))
  deriving Show

empty :: Ord idx => (idx -> a -> Bool) -> [idx] -> MultiIndex idx f a
empty p is = MultiIndex p (Map.fromList (zip is (repeat Index.empty)))

insert :: Ord idx => Term f -> a -> RuleIndex f a -> RuleIndex f a
insert t x (MultiIndex p idxs) =
  MultiIndex p $
    Map.mapWithKey (\k idx -> if p k then Index.insert t x idx else idx) idxs

delete :: (Ord idx, Eq a) => Term f -> a -> RuleIndex f a -> RuleIndex f a
delete t x (MultiIndex p idxs) =
  MultiIndex p $
    Map.mapWithKey (\k idx -> if p k then Index.delete t x idx else idx) idxs

index :: Ord idx => idx -> MultiIndex idx f a -> Index f a
index idx (MultiIndex _ idxs) = idxs Map.! idx
