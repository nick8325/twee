-- | Zero-indexed dynamic arrays, optimised for lookup.
-- Modification is slow. Uninitialised indices have a default value.
{-# LANGUAGE CPP #-}
module Data.DynamicArray where

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
    arrayStart    :: {-# UNPACK #-} !Int,
    -- | The contents of the array.
    arrayContents :: {-# UNPACK #-} !(P.SmallArray a) }

arraySize :: Array a -> Int
arraySize = P.sizeofSmallArray . arrayContents

-- | Convert an array to a list of (index, value) pairs.
{-# INLINE toList #-}
toList :: Array a -> [(Int, a)]
toList arr =
  [ (i+arrayStart arr, x)
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
{-# NOINLINE newArray #-}
newArray :: Array a
newArray = runST $ do
  marr <- P.newSmallArray 0 undefined
  arr  <- P.unsafeFreezeSmallArray marr
  return (Array maxBound arr)

-- | Index into an array. O(1) time.
{-# INLINE (!) #-}
(!) :: Default a => Array a -> Int -> a
arr ! n = getWithDefault def n arr

-- | Index into an array. O(1) time.
{-# INLINE getWithDefault #-}
getWithDefault :: a -> Int -> Array a -> a
getWithDefault def n arr
  | arrayStart arr <= n && n < arrayStart arr + arraySize arr =
    P.indexSmallArray (arrayContents arr) (n - arrayStart arr)
  | otherwise = def

-- | Update the array. O(n) time.
{-# INLINE update #-}
update :: Default a => Int -> a -> Array a -> Array a
update n x arr = updateWithDefault def n x arr

{-# INLINEABLE updateWithDefault #-}
updateWithDefault :: a -> Int -> a -> Array a -> Array a
updateWithDefault def n x arr = runST $ do
  let size = if arraySize arr == 0 then 1 else if n < arrayStart arr then arraySize arr + (arrayStart arr - n) else arraySize arr `max` (n+1)
      start = n `min` arrayStart arr
  marr <- P.newSmallArray size def
  P.copySmallArray marr (arrayStart arr - start) (arrayContents arr) 0 (arraySize arr)
  P.writeSmallArray marr (n - start) $! x
  arr' <- P.unsafeFreezeSmallArray marr
  return (Array start arr')
