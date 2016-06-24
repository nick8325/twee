{-# LANGUAGE CPP #-}
module Twee.Array where

#include "errors.h"
import qualified Data.Primitive.SmallArray as P
import Control.Monad.ST
import Data.List

-- Zero-indexed dynamic arrays.
-- Optimised for lookup. Modification is slow.
data Array a =
  Array {
    arraySize     :: {-# UNPACK #-} !Int,
    arrayContents :: {-# UNPACK #-} !(P.SmallArray a) }

class Default a where def :: a

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

newArray :: Default a => Array a
newArray = runST $ do
  marr <- P.newSmallArray 0 def
  arr  <- P.unsafeFreezeSmallArray marr
  return (Array 0 arr)

{-# INLINE (!) #-}
(!) :: Default a => Array a -> Int -> a
arr ! n
  | 0 <= n && n < arraySize arr =
    P.indexSmallArray (arrayContents arr) n
  | otherwise = def

{-# INLINEABLE update #-}
update :: Default a => Int -> a -> Array a -> Array a
update n x arr = runST $ do
  let size = arraySize arr `max` (n+1)
  marr <- P.newSmallArray size def
  P.copySmallArray (arrayContents arr) 0 marr 0 (arraySize arr)
  P.writeSmallArray marr n $! x
  arr' <- P.unsafeFreezeSmallArray marr
  return (Array size arr')
