-- A queue of passive critical pairs.
{-# LANGUAGE TypeFamilies, RecordWildCards, FlexibleContexts, ScopedTypeVariables, StandaloneDeriving #-}
module Twee.PassiveQueue(
  Params(..),
  Queue,
  Passive(..),
  empty, insert, removeMin, mapMaybe) where

import qualified Twee.Heap as Heap
import qualified Data.Vector.Unboxed as Vector
import Data.Int
import Data.List hiding (insert)
import qualified Data.Maybe
import Data.Ord
import Data.Proxy
import Twee.Utils

class (Eq (Id params), Integral (Id params), Ord (Score params), Vector.Unbox (PackedScore params), Vector.Unbox (PackedId params)) => Params params where
  type Score params
  type Id params
  type PackedScore params
  type PackedId params
  packScore :: proxy params -> Score params -> PackedScore params
  unpackScore :: proxy params -> PackedScore params -> Score params
  packId :: proxy params -> Id params -> PackedId params
  unpackId :: proxy params -> PackedId params -> Id params

type Queue params =
  Heap.Heap (PassiveSet params)

-- All passive CPs generated from one given rule.
data PassiveSet params =
  PassiveSet {
    passiveset_best  :: {-# UNPACK #-} !(Passive params),
    passiveset_rule  :: !(Id params),
    -- CPs where the rule is the left-hand rule
    passiveset_left  :: {-# UNPACK #-} !(Vector.Vector (PackedScore params, PackedId params, Int32)),
    -- CPs where the rule is the right-hand rule
    passiveset_right :: {-# UNPACK #-} !(Vector.Vector (PackedScore params, PackedId params, Int32)) }
instance Params params => Eq (PassiveSet params) where
  x == y = compare x y == EQ
instance Params params => Ord (PassiveSet params) where
  compare = comparing passiveset_best

-- A smart-ish constructor.
{-# INLINEABLE mkPassiveSet #-}
mkPassiveSet ::
  Params params =>
  Proxy params ->
  Id params ->
  Vector.Vector (PackedScore params, PackedId params, Int32) ->
  Vector.Vector (PackedScore params, PackedId params, Int32) ->
  Maybe (PassiveSet params)
mkPassiveSet proxy rule left right
  | Vector.null left && Vector.null right = Nothing
  | not (Vector.null left) &&
    (Vector.null right || l <= r) =
    Just PassiveSet {
      passiveset_best  = l,
      passiveset_rule  = rule,
      passiveset_left  = Vector.tail left,
      passiveset_right = right }
    -- In this case we must have not (Vector.null right).
  | otherwise =
    Just PassiveSet {
      passiveset_best  = r,
      passiveset_rule  = rule,
      passiveset_left  = left,
      passiveset_right = Vector.tail right }
  where
    l = unpack proxy rule True (Vector.head left)
    r = unpack proxy rule False (Vector.head right)

{-# INLINEABLE unpack #-}
unpack :: Params params => Proxy params -> Id params -> Bool -> (PackedScore params, PackedId params, Int32) -> Passive params
unpack proxy rule isLeft (score, id, pos) =
  Passive {
    passive_score = unpackScore proxy score,
    passive_rule1 = if isLeft then rule else rule',
    passive_rule2 = if isLeft then rule' else rule,
    passive_pos = fromIntegral pos }
  where
    rule' = unpackId proxy id

{-# INLINEABLE makePassiveSet #-}
makePassiveSet :: forall params. Params params => Id params -> [Passive params] -> Maybe (PassiveSet params)
makePassiveSet _ [] = Nothing
makePassiveSet rule ps
  | and [passive_rule2 p == rule | p <- right] =
    mkPassiveSet proxy rule
      (Vector.fromList (map (pack True) (sort left)))
      (Vector.fromList (map (pack False) (sort right)))
  | otherwise = error "rule id does not occur in passive"
  where
    proxy :: Proxy params
    proxy = Proxy
    
    (left, right) = partition (\p -> passive_rule1 p == rule) ps
    pack isLeft Passive{..} =
      (packScore proxy passive_score,
       packId proxy (if isLeft then passive_rule2 else passive_rule1),
       fromIntegral passive_pos)

{-# INLINEABLE unconsPassiveSet #-}
unconsPassiveSet :: forall params. Params params => PassiveSet params -> (Passive params, Maybe (PassiveSet params))
unconsPassiveSet PassiveSet{..} =
  (passiveset_best, mkPassiveSet (Proxy :: Proxy params) passiveset_rule passiveset_left passiveset_right)

data Passive params =
  Passive {
    passive_score :: !(Score params),
    passive_rule1 :: !(Id params),
    passive_rule2 :: !(Id params),
    passive_pos   :: {-# UNPACK #-} !Int }

instance Params params => Eq (Passive params) where
  x == y = compare x y == EQ

instance Params params => Ord (Passive params) where
  compare = comparing f
    where
      f Passive{..} =
        (passive_score,
         intMax (fromIntegral passive_rule1) (fromIntegral passive_rule2),
         intMin (fromIntegral passive_rule1) (fromIntegral passive_rule2),
         passive_pos)

-- The empty queue.
empty :: Queue params
empty = Heap.empty

-- Add a set of passives to the queue.
{-# INLINEABLE insert #-}
insert :: Params params => Id params -> [Passive params] -> Queue params -> Queue params
insert rule passives q =
  case makePassiveSet rule passives of
    Nothing -> q
    Just p -> Heap.insert p q

-- Remove the minimum passive from the queue.
{-# INLINEABLE removeMin #-}
removeMin :: Params params => Queue params -> Maybe (Passive params, Queue params)
removeMin q = do
  (passiveset, q) <- Heap.removeMin q
  case unconsPassiveSet passiveset of
    (passive, Just passiveset') ->
      Just (passive, Heap.insert passiveset' q)
    (passive, Nothing) ->
      Just (passive, q)

-- Map a function over all passives.
{-# INLINEABLE mapMaybe #-}
mapMaybe :: Params params => (Passive params -> Maybe (Passive params)) -> Queue params -> Queue params
mapMaybe f = Heap.mapMaybe g
  where
    g PassiveSet{..} =
      makePassiveSet passiveset_rule $ Data.Maybe.mapMaybe f $
        passiveset_best:
        map (unpack proxy passiveset_rule True) (Vector.toList passiveset_left) ++
        map (unpack proxy passiveset_rule False) (Vector.toList passiveset_right)
    proxy :: Proxy params
    proxy = Proxy
