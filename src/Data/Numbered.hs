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

data Numbered a =
  Numbered
    {-# UNPACK #-} !ByteArray
    {-# UNPACK #-} !(SmallArray a)

instance Show a => Show (Numbered a) where show = show . toList

empty :: Numbered a
empty = fromList []

singleton :: Int -> a -> Numbered a
singleton i x = fromList [(i, x)]

fromList :: [(Int, a)] -> Numbered a
fromList xs =
  Numbered
    (byteArrayFromList (map (fromIntegral . fst) xs :: [Int32]))
    (smallArrayFromList (map snd xs))

toList :: Numbered a -> [(Int, a)]
toList num =
  [num ! i | i <- [0..size num-1]]

size :: Numbered a -> Int
size (Numbered _ elems) = sizeofSmallArray elems

(!) :: Numbered a -> Int -> (Int, a)
Numbered idxs elems ! i =
  (fromIntegral (indexByteArray idxs i :: Int32),
   indexSmallArray elems i)

lookup :: Int -> Numbered a -> Maybe a
lookup i num =
  List.lookup i (toList num)

put :: Int -> a -> Numbered a -> Numbered a
put i x num =
  fromList $ lt ++ [(i, x)] ++ gt
  where
    xs = toList num
    lt = List.filter ((< i) . fst) xs
    gt = List.filter ((> i) . fst) xs

delete :: Int -> Numbered a -> Numbered a
delete i = fromList . List.filter ((/= i) . fst) . toList

modify :: Int -> a -> (a -> a) -> Numbered a -> Numbered a
modify i def f num =
  put i (f (fromMaybe def (lookup i num))) num

filter :: (a -> Bool) -> Numbered a -> Numbered a
filter p = fromList . List.filter (p . snd) . toList

