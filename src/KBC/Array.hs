{-# LANGUAGE CPP #-}
module KBC.Array where

#include "errors.h"
import qualified Data.Primitive as P
import Control.Monad.ST
import Control.Monad
import Data.List

-- Zero-indexed dynamic arrays.
-- Optimised for lookup. Modification is slow.

-- XXX make it use a Numbered instance instead.
data Array a =
  Array {
    arraySize     :: {-# UNPACK #-} !Int,
    arrayLoad     :: {-# UNPACK #-} !Int,
    arrayContents :: {-# UNPACK #-} !(P.Array (Maybe a)) }

toList :: Array a -> [(Int, a)]
toList arr =
  [ (i, x)
  | i <- [0..arraySize arr-1],
    Just x <- [P.indexArray (arrayContents arr) i] ]

null :: Array a -> Bool
null arr = arrayLoad arr == 0

instance Show a => Show (Array a) where
  show arr =
    "{" ++
    intercalate ", "
      [ show i ++ "->" ++ show x
      | (i, x) <- toList arr ] ++
    "}"

newArray :: Array a
newArray = runST $ do
  marr <- P.newArray 0 Nothing
  arr  <- P.unsafeFreezeArray marr
  return (Array 0 0 arr)

{-# INLINE (!) #-}
(!) :: Array a -> Int -> Maybe a
arr ! n = do
  guard (0 <= n && n < arraySize arr)
  P.indexArray (arrayContents arr) n

{-# INLINEABLE update #-}
update :: Int -> Maybe a -> Array a -> Array a
update n x arr = runST $ do
  let size = arraySize arr `max` (n+1)
  marr <- P.newArray size Nothing
  P.copyArray marr 0 (arrayContents arr) 0 (arraySize arr)
  P.writeArray marr n x
  arr' <- P.unsafeFreezeArray marr
  let diff =
        case (x, arr ! n) of
          (Nothing, Nothing) -> 0
          (Just _,  Just _)  -> 0
          (Nothing, Just _)  -> -1
          (Just _,  Nothing) -> 1
  return (Array size (arrayLoad arr + diff) arr')
