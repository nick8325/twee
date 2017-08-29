-- | Zero-indexed dynamic arrays, optimised for lookup.
-- Modification is slow. Uninitialised indices have a default value.
{-# LANGUAGE CPP #-}
module Twee.Array where

#include "errors.h"
#ifdef BOUNDS_CHECKS
import qualified Data.Primitive.SmallArray.Checked as P
#else
import qualified Data.Primitive.SmallArray as P
#endif
import Control.Monad.ST
import Data.List

-- | A type which has a default value.
class Default a where
  -- | The default value.
  def :: a

-- | An array.
data Array a =
  Array {
    -- | The size of the array.
    arraySize     :: {-# UNPACK #-} !Int,
    -- | The contents of the array.
    arrayContents :: {-# UNPACK #-} !(P.SmallArray a) }

-- | Convert an array to a list of (index, value) pairs.
{-# INLINE toList #-}
toList :: Array a -> [(Int, a)]
toList arr =
  [ (i, x)
  | i <- [0..arraySize arr-1],
    let x = P.indexSmallArray (arrayContents arr) i ]

instance Show a => Show (Array a) where
  show arr =
    "{" ++
    intercalate ", "
      [ show i ++ "->" ++ show x
      | (i, x) <- toList arr ] ++
    "}"

-- | Create an empty array.
newArray :: Default a => Array a
newArray = runST $ do
  marr <- P.newSmallArray 0 def
  arr  <- P.unsafeFreezeSmallArray marr
  return (Array 0 arr)

-- | Index into an array. O(1) time.
{-# INLINE (!) #-}
(!) :: Default a => Array a -> Int -> a
arr ! n
  | 0 <= n && n < arraySize arr =
    P.indexSmallArray (arrayContents arr) n
  | otherwise = def

-- | Update the array. O(n) time.
{-# INLINEABLE update #-}
update :: Default a => Int -> a -> Array a -> Array a
update n x arr = runST $ do
  let size = arraySize arr `max` (n+1)
  marr <- P.newSmallArray size def
  P.copySmallArray marr 0 (arrayContents arr) 0 (arraySize arr)
  P.writeSmallArray marr n $! x
  arr' <- P.unsafeFreezeSmallArray marr
  return (Array size arr')
