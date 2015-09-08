{-# LANGUAGE CPP #-}
module KBC.Array where

#include "errors.h"
import qualified Data.Primitive as P
import Control.Monad.ST
import Control.Monad
import Data.List

-- Zero-indexed dynamic arrays.
-- Optimised for lookup. Modification is slow.
data Array a =
  Array {
    arraySize     :: {-# UNPACK #-} !Int,
    arrayContents :: {-# UNPACK #-} !(P.Array a) }

class Default a where def :: a

toList :: Array a -> [(Int, a)]
toList arr =
  [ (i, x)
  | i <- [0..arraySize arr-1],
    let x = P.indexArray (arrayContents arr) i ]

instance Show a => Show (Array a) where
  show arr =
    "{" ++
    intercalate ", "
      [ show i ++ "->" ++ show x
      | (i, x) <- toList arr ] ++
    "}"

newArray :: Default a => Array a
newArray = runST $ do
  marr <- P.newArray 0 def
  arr  <- P.unsafeFreezeArray marr
  return (Array 0 arr)

{-# INLINE (!) #-}
(!) :: Default a => Array a -> Int -> a
arr ! n
  | 0 <= n && n < arraySize arr =
    P.indexArray (arrayContents arr) n
  | otherwise = def

{-# INLINEABLE update #-}
update :: Default a => Int -> a -> Array a -> Array a
update n x arr = runST $ do
  let size = arraySize arr `max` (n+1)
  marr <- P.newArray size def
  P.copyArray marr 0 (arrayContents arr) 0 (arraySize arr)
  P.writeArray marr n x
  arr' <- P.unsafeFreezeArray marr
  return (Array size arr')
