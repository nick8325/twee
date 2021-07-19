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
newtype Queue a = Queue (Heap.Heap (Best a))

-- | The type of batches must be a member of this class.
class Ord (Entry a) => Batch a where
  -- | Each batch can have an associated label,
  -- which is specified when calling 'insert'.
  -- A label represents a piece of information which is
  -- shared in common between all entries in a batch,
  -- and which might be used to store that batch more
  -- efficiently. 
  -- Labels are optional, and by default @Label a = ()@.
  type Label a

  -- | Individual entries in the batch.
  type Entry a

  -- | Given a label, and a non-empty list of entries,
  -- sorted in ascending order, produce a list of batches.
  makeBatch :: Label a -> [Entry a] -> [a]

  -- | Remove the smallest entry from a batch.
  unconsBatch :: a -> (Entry a, Maybe a)
  
  -- | Return the label of a batch.
  batchLabel :: a -> Label a

  -- | Compute the size of a batch. Used in 'size'.
  -- The default implementation works by repeatedly calling
  -- 'unconsBatch'.
  batchSize :: a -> Int
  batchSize = length . unbatch

  type Label a = ()

-- A newtype wrapper for batches which compares the smallest entry.
newtype Best a = Best { unBest :: a }
instance Batch a => Eq (Best a) where x == y = compare x y == EQ
instance Batch a => Ord (Best a) where
  compare = comparing (fst . unconsBatch . unBest)

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
  Queue $ foldl' (flip (Heap.insert . Best)) q (makeBatch l (sort is))

-- | Remove the minimum entry from the queue.
-- The first argument is a predicate: if the minimum entry's batch
-- does not satisfy the predicate, that batch is discarded.
{-# INLINEABLE removeMin #-}
removeMin :: Batch a => (Label a -> Bool) -> Queue a -> Maybe (Entry a, Queue a)
removeMin ok (Queue q) = do
  (Best batch, q) <- Heap.removeMin q
  if not (ok (batchLabel batch)) then removeMin ok (Queue q) else
    case unconsBatch batch of
      (entry, Just batch') ->
        Just (entry, Queue (Heap.insert (Best batch') q))
      (entry, Nothing) ->
        Just (entry, Queue q)

-- | Map a function over all entries.
-- The function must preserve the label of each batch,
-- and must not split existing batches into two.
{-# INLINEABLE mapMaybe #-}
mapMaybe :: Batch a => (Entry a -> Maybe (Entry a)) -> Queue a -> Queue a
mapMaybe f (Queue q) = Queue (Heap.mapMaybe g q)
  where
    g (Best batch) =
      case Data.Maybe.mapMaybe f (unbatch batch) of
        [] -> Nothing
        is ->
          case makeBatch (batchLabel batch) (sort is) of
            [] -> Nothing
            [batch'] -> Just (Best batch')
            _ -> error "multiple batches produced"

-- | Convert a queue into a list of batches, in unspecified order.
{-# INLINEABLE toBatches #-}
toBatches :: Queue a -> [a]
toBatches (Queue q) = map unBest (Heap.toList q)

-- | Convert a queue into a list of entries, in unspecified order.
{-# INLINEABLE toList #-}
toList :: Batch a => Queue a -> [Entry a]
toList q = concatMap unbatch (toBatches q)

{-# INLINEABLE size #-}
size :: Batch a => Queue a -> Int
size = sum . map batchSize . toBatches

-- | A "standard" type of batches. By using @Queue (StandardBatch a)@,
-- you will get a queue where entries have type @a@ and labels have
-- type @()@.
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

  makeBatch _ (x:xs) = [StandardBatch x (PackedSequence.fromList xs)]
  unconsBatch StandardBatch{..} =
    (batch_best,
     case PackedSequence.uncons batch_rest of
       Nothing -> Nothing
       Just (x, xs) -> Just (StandardBatch x xs))
  batchLabel _ = ()
  batchSize StandardBatch{..} = 1 + PackedSequence.size batch_rest

