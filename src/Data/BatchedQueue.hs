-- | A queue where entries can be added in batches and stored compactly.
{-# LANGUAGE TypeFamilies, RecordWildCards, FlexibleContexts, ScopedTypeVariables #-}
module Data.BatchedQueue(
  Queue, Batch(..), StandardBatch, unbatch, empty, insert, removeMin, mapMaybe, toBatches, toList, size) where

import qualified Data.Heap as Heap
import Data.List(unfoldr, sort, foldl')
import qualified Data.Maybe
import Data.PackedSequence(PackedSequence)
import qualified Data.PackedSequence as PackedSequence
import Data.Serialize
import Data.Ord

-- | A queue of batches.
newtype Queue a = Queue (Heap.Heap a)

class (Ord a, Ord (Entry a)) => Batch a where
  type Label a
  type Entry a

  makeBatch :: Label a -> Entry a -> [Entry a] -> [a]
  unconsBatch :: a -> (Entry a, Maybe a)
  batchLabel :: a -> Label a
  batchSize :: a -> Int

data StandardBatch a =
  StandardBatch {
    batch_best :: !a,
    batch_rest :: {-# UNPACK #-} !(PackedSequence a) }

instance Ord a => Eq (StandardBatch a) where
  x == y = compare x y == EQ
instance Ord a => Ord (StandardBatch a) where
  compare = comparing batch_best

instance (Ord a, Serialize a) => Batch (StandardBatch a) where
  type Label (StandardBatch a) = ()
  type Entry (StandardBatch a) = a

  makeBatch _ x xs = [StandardBatch x (PackedSequence.fromList xs)]
  unconsBatch StandardBatch{..} =
    (batch_best,
     case PackedSequence.uncons batch_rest of
       Nothing -> Nothing
       Just (x, xs) -> Just (StandardBatch x xs))
  batchLabel _ = ()
  batchSize StandardBatch{..} = 1 + PackedSequence.size batch_rest

-- | Convert a batch into a list of entries.
unbatch :: Batch a => a -> [Entry a]
unbatch batch = unfoldr (fmap unconsBatch) (Just batch)

-- | The empty queue.
empty :: Queue a
empty = Queue Heap.empty

-- | Add entries to the queue.
{-# INLINEABLE insert #-}
insert :: forall a. Batch a => Label a -> [Entry a] -> Queue a -> Queue a
insert _ [] q = q
insert l is (Queue q) =
  Queue $ foldl' (flip Heap.insert) q (makeBatch l (head is') (tail is'))
  where
    is' = sort is

-- | Remove the minimum entry from the queue.
{-# INLINEABLE removeMin #-}
removeMin :: Batch a => (Label a -> Bool) -> Queue a -> Maybe (Entry a, Queue a)
removeMin ok (Queue q) = do
  (batch, q) <- Heap.removeMin q
  if not (ok (batchLabel batch)) then removeMin ok (Queue q) else
    case unconsBatch batch of
      (entry, Just batch') ->
        Just (entry, Queue (Heap.insert batch' q))
      (entry, Nothing) ->
        Just (entry, Queue q)

-- | Map a function over all entries.
-- The function must preserve the label of the inference,
-- and the number of batches returned by 'make'.
{-# INLINEABLE mapMaybe #-}
mapMaybe :: Batch a => (Entry a -> Maybe (Entry a)) -> Queue a -> Queue a
mapMaybe f (Queue q) = Queue (Heap.mapMaybe g q)
  where
    g batch =
      case Data.Maybe.mapMaybe f (unbatch batch) of
        [] -> Nothing
        is ->
          let is' = sort is in
          case makeBatch (batchLabel batch) (head is') (tail is') of
            [] -> Nothing
            [batch'] -> Just batch'
            _ -> error "multiple batches produced"

-- | Convert a queue into a list of batches, in unspecified order.
{-# INLINEABLE toBatches #-}
toBatches :: Queue a -> [a]
toBatches (Queue q) = Heap.toList q

-- | Convert a queue into a list of entries, in unspecified order.
{-# INLINEABLE toList #-}
toList :: Batch a => Queue a -> [Entry a]
toList q = concatMap unbatch (toBatches q)

{-# INLINEABLE size #-}
size :: Batch a => Queue a -> Int
size = sum . map batchSize . toBatches
