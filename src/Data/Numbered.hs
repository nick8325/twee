-- | An array of key-value pairs, where the keys are integers.
-- Can be accessed both as a map ("give me the value corresponding
-- to the key 2") and as an array ("give me the 3rd key-value pair").
-- Array-like access is fast; everything else is slow.
module Data.Numbered(
  Numbered,
  empty, fromList, singleton, toList, size, (!),
  lookup, put, modify, filter, delete) where

import Prelude hiding (filter, lookup)
import qualified Data.List as List
import Data.Primitive.ByteArray
import Data.Primitive.SmallArray
import Data.Int
import Data.Maybe

-- | An array of key-value pairs.
data Numbered a =
  Numbered
    {-# UNPACK #-} !ByteArray
    {-# UNPACK #-} !(SmallArray a)

instance Show a => Show (Numbered a) where show = show . toList

-- | An empty array.
empty :: Numbered a
empty = fromList []

-- | A singleton array.
singleton :: Int -> a -> Numbered a
singleton i x = fromList [(i, x)]

-- | Convert a list of pairs to an array.
-- Duplicate keys are allowed.
fromList :: [(Int, a)] -> Numbered a
fromList xs =
  Numbered
    (byteArrayFromList (map (fromIntegral . fst) xs :: [Int32]))
    (smallArrayFromList (map snd xs))

-- | Convert an array to a list.
toList :: Numbered a -> [(Int, a)]
toList num =
  [num ! i | i <- [0..size num-1]]

-- | Get the number of key-value pairs in an array. O(1) time.
size :: Numbered a -> Int
size (Numbered _ elems) = sizeofSmallArray elems

-- | Index into the array. O(1) time.
(!) :: Numbered a -> Int -> (Int, a)
Numbered idxs elems ! i =
  (fromIntegral (indexByteArray idxs i :: Int32),
   indexSmallArray elems i)

-- | Look up the value associated with a particular key.
-- If the key occurs multiple times, any of its values
-- may be returned. O(n) time.
lookup :: Int -> Numbered a -> Maybe a
lookup i num =
  List.lookup i (toList num)

-- | Associate a value with a key. Any existing occurences
-- of the key are removed. O(n) time.
put :: Int -> a -> Numbered a -> Numbered a
put i x num =
  fromList $ lt ++ [(i, x)] ++ gt
  where
    xs = toList num
    lt = List.filter ((< i) . fst) xs
    gt = List.filter ((> i) . fst) xs

-- | Remove a given key. O(n) time.
delete :: Int -> Numbered a -> Numbered a
delete i = fromList . List.filter ((/= i) . fst) . toList

-- | Modify the value associated with a given key.
-- If the key occurs multiple times, one of its values
-- is chosen and the others deleted. In the call
-- @modify k def f@, if the key @k@ is not present,
-- the entry @k -> f def@ is added. O(n) time.
modify :: Int -> a -> (a -> a) -> Numbered a -> Numbered a
modify i def f num =
  put i (f (fromMaybe def (lookup i num))) num

-- | Keep only keys satisfying a predicate.
filter :: (a -> Bool) -> Numbered a -> Numbered a
filter p = fromList . List.filter (p . snd) . toList

