-- | A queue of passive critical pairs, using a memory-efficient representation.
{-# LANGUAGE TypeFamilies, RecordWildCards, FlexibleContexts, ScopedTypeVariables, StandaloneDeriving, DeriveGeneric #-}
module Twee.PassiveQueue(
  Queue,
  Passive(..),
  empty, insert, removeMin, mapMaybe, toList, queueSize) where

import qualified Data.Heap as Heap
import Data.Int
import Data.List hiding (insert)
import qualified Data.Maybe
import Data.Ord
import Data.Proxy
import Twee.Utils
import Data.Serialize
import qualified Data.ByteString as BS
import Data.ByteString(ByteString)
import GHC.Generics
import Data.Either
import Twee.Base hiding (unpack, empty)

-- | A critical pair queue.
newtype Queue =
  Queue (Heap.Heap PassiveSet)

-- All passive CPs generated from one given rule.
data PassiveSet =
  PassiveSet {
    passiveset_best  :: {-# UNPACK #-} !Passive,
    passiveset_rule  :: {-# UNPACK #-} !Id,
    -- CPs where the rule is the left-hand rule
    passiveset_left  :: {-# UNPACK #-} !Passives,
    -- CPs where the rule is the right-hand rule
    passiveset_right :: {-# UNPACK #-} !Passives }
instance Eq PassiveSet where
  x == y = compare x y == EQ
instance Ord PassiveSet where
  compare = comparing passiveset_best

data Passives =
  Passives {-# UNPACK #-} !Int {-# UNPACK #-} !ByteString

nullPassives :: Passives -> Bool
nullPassives (Passives 0 _) = True
nullPassives _ = False

passivesSize :: Passives -> Int
passivesSize (Passives n _) = n

packPassives :: [(Int32, Id, Int32)] -> Passives
packPassives ps =
  Passives (length ps) (runPut (mapM_ put ps))

unconsPassives :: Passives -> Maybe ((Int32, Id, Int32), Passives)
unconsPassives (Passives 0 _) = Nothing
unconsPassives (Passives n bs) =
  case runGetState get bs 0 of
    Left err -> error ("unconsPassives: " ++ err)
    Right (x, rest) -> Just (x, Passives (n-1) rest)

unpackPassives :: Passives -> [(Int32, Id, Int32)]
unpackPassives = unfoldr unconsPassives

-- A smart-ish constructor.
{-# INLINEABLE mkPassiveSet #-}
mkPassiveSet ::
  Proxy params ->
  Id ->
  Passives ->
  Passives ->
  Maybe PassiveSet
mkPassiveSet proxy rule left right
  | nullPassives left && nullPassives right = Nothing
  | not (nullPassives left) &&
    (nullPassives right || l <= r) =
    Just PassiveSet {
      passiveset_best  = l,
      passiveset_rule  = rule,
      passiveset_left  = ltl,
      passiveset_right = right }
    -- In this case we must have not (nullPassives right).
  | otherwise =
    Just PassiveSet {
      passiveset_best  = r,
      passiveset_rule  = rule,
      passiveset_left  = left,
      passiveset_right = rtl }
  where
    Just (lhd, ltl) = unconsPassives left
    Just (rhd, rtl) = unconsPassives right

    l = unpack proxy rule True lhd
    r = unpack proxy rule False rhd

-- Unpack a triple into a Passive.
{-# INLINEABLE unpack #-}
unpack :: Proxy params -> Id -> Bool -> (Int32, Id, Int32) -> Passive
unpack proxy rule isLeft (score, rule', pos) =
  Passive {
    passive_score = score,
    passive_rule1 = if isLeft then rule else rule',
    passive_rule2 = if isLeft then rule' else rule,
    passive_pos = pos }

-- Make a PassiveSet from a list of Passives.
{-# INLINEABLE makePassiveSet #-}
makePassiveSet :: forall params. Id -> [Passive] -> Maybe PassiveSet
makePassiveSet _ [] = Nothing
makePassiveSet rule ps
  | and [passive_rule2 p == rule | p <- right] =
    mkPassiveSet proxy rule
      (packPassives (map (pack True) (sort left)))
      (packPassives (map (pack False) (sort right)))
  | otherwise = error "rule id does not occur in passive"
  where
    proxy :: Proxy params
    proxy = Proxy
    
    (left, right) = partition (\p -> passive_rule1 p == rule) ps
    pack isLeft Passive{..} =
      (passive_score,
       if isLeft then passive_rule2 else passive_rule1,
       passive_pos)

-- Convert a PassiveSet back into a list of Passives.
{-# INLINEABLE unpackPassiveSet #-}
unpackPassiveSet :: forall params. PassiveSet -> (Int, [Passive])
unpackPassiveSet PassiveSet{..} =
  (1 + passivesSize passiveset_left + passivesSize passiveset_right,
   passiveset_best:
   map (unpack proxy passiveset_rule True) (unpackPassives passiveset_left) ++
   map (unpack proxy passiveset_rule False) (unpackPassives passiveset_right))
  where
    proxy :: Proxy params
    proxy = Proxy

-- Find and remove the best element from a PassiveSet.
{-# INLINEABLE unconsPassiveSet #-}
unconsPassiveSet :: forall params. PassiveSet -> (Passive, Maybe PassiveSet)
unconsPassiveSet PassiveSet{..} =
  (passiveset_best, mkPassiveSet (Proxy :: Proxy params) passiveset_rule passiveset_left passiveset_right)

-- | A queued critical pair.
data Passive =
  Passive {
    -- | The score of this critical pair.
    passive_score :: {-# UNPACK #-} !Int32,
    -- | The rule which does the outermost rewrite in this critical pair.
    passive_rule1 :: {-# UNPACK #-} !Id,
    -- | The rule which does the innermost rewrite in this critical pair.
    passive_rule2 :: {-# UNPACK #-} !Id,
    -- | The position of the overlap. See 'Twee.CP.overlap_pos'.
    passive_pos   :: {-# UNPACK #-} !Int32 }
  deriving Generic

instance Serialize Passive

instance Eq Passive where
  x == y = compare x y == EQ

instance Ord Passive where
  compare = comparing f
    where
      f Passive{..} =
        (passive_score,
         intMax (fromIntegral passive_rule1) (fromIntegral passive_rule2),
         intMin (fromIntegral passive_rule1) (fromIntegral passive_rule2),
         passive_pos)

-- | The empty queue.
empty :: Queue
empty = Queue Heap.empty

-- | Add a set of 'Passive's to the queue.
{-# INLINEABLE insert #-}
insert :: Id -> [Passive] -> Queue -> Queue
insert rule passives (Queue q) =
  Queue $
  case makePassiveSet rule passives of
    Nothing -> q
    Just p -> Heap.insert p q

-- | Remove the minimum 'Passive' from the queue.
{-# INLINEABLE removeMin #-}
removeMin :: Queue -> Maybe (Passive, Queue)
removeMin (Queue q) = do
  (passiveset, q) <- Heap.removeMin q
  case unconsPassiveSet passiveset of
    (passive, Just passiveset') ->
      Just (passive, Queue (Heap.insert passiveset' q))
    (passive, Nothing) ->
      Just (passive, Queue q)

-- | Map a function over all 'Passive's.
{-# INLINEABLE mapMaybe #-}
mapMaybe :: (Passive -> Maybe Passive) -> Queue -> Queue
mapMaybe f (Queue q) = Queue (Heap.mapMaybe g q)
  where
    g passiveSet@PassiveSet{..} =
      makePassiveSet passiveset_rule $ Data.Maybe.mapMaybe f $
        snd (unpackPassiveSet passiveSet)

-- | Convert a queue into a list of 'Passive's.
-- The 'Passive's are produced in batches, with each batch labelled
-- with its size.
{-# INLINEABLE toList #-}
toList :: Queue -> [(Int, [Passive])]
toList (Queue h) = map unpackPassiveSet (Heap.toList h)

queueSize :: Queue -> Int
queueSize = sum . map fst . toList
