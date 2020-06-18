{-# LANGUAGE RecordWildCards, ScopedTypeVariables, FlexibleContexts #-}
module Twee.Rule.Index(
  RuleIndex(..),
  empty, insert, delete,
  approxMatches, matches, lookup) where

import Prelude hiding (lookup)
import Twee.Base hiding (lookup, empty)
import Twee.Rule
import Twee.Index hiding (insert, delete, empty)
import qualified Twee.Index as Index

data RuleIndex f a =
  RuleIndex {
    index_oriented :: !(Index f a),
    index_all      :: !(Index f a) }
  deriving Show

empty :: RuleIndex f a
empty = RuleIndex Index.empty Index.empty

insert :: forall f a. Has a (Rule f) => Term f -> a -> RuleIndex f a -> RuleIndex f a
insert t x RuleIndex{..} =
  RuleIndex {
    index_oriented = insertWhen (oriented or) index_oriented,
    index_all = insertWhen True index_all }
  where
    Rule or _ _ = the x :: Rule f

    insertWhen False idx = idx
    insertWhen True idx = Index.insert t x idx

delete :: forall f a. (Eq a, Has a (Rule f)) => Term f -> a -> RuleIndex f a -> RuleIndex f a
delete t x RuleIndex{..} =
  RuleIndex {
    index_oriented = deleteWhen (oriented or) index_oriented,
    index_all = deleteWhen True index_all }
  where
    Rule or _ _ = the x :: Rule f

    deleteWhen False idx = idx
    deleteWhen True idx = Index.delete t x idx
