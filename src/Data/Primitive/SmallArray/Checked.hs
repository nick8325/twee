module Data.Primitive.SmallArray.Checked(
  module Data.Primitive.SmallArray,
  module Data.Primitive.SmallArray.Checked) where

import Control.Monad.Primitive
import qualified Data.Primitive.SmallArray as P
import Data.Primitive.SmallArray(
  SmallArray(..), SmallMutableArray(..), newSmallArray, unsafeFreezeSmallArray,
  unsafeThawSmallArray, sizeofSmallArray, sizeofSmallMutableArray)
import Data.Primitive.Checked

instance Sized (SmallArray a) where
  size = sizeofSmallArray
instance Sized (SmallMutableArray m a) where
  size = sizeofSmallMutableArray

{-# INLINE readSmallArray #-}
readSmallArray :: PrimMonad m => SmallMutableArray (PrimState m) a -> Int -> m a
readSmallArray arr n =
  check arr n $
  P.readSmallArray arr n

{-# INLINE writeSmallArray #-}
writeSmallArray :: PrimMonad m => SmallMutableArray (PrimState m) a -> Int -> a -> m ()
writeSmallArray arr n x =
  check arr n $
  P.writeSmallArray arr n x

{-# INLINE indexSmallArrayM #-}
indexSmallArrayM :: Monad m => SmallArray a -> Int -> m a
indexSmallArrayM arr n =
  check arr n $
  P.indexSmallArrayM arr n

{-# INLINE indexSmallArray #-}
indexSmallArray :: SmallArray a -> Int -> a
indexSmallArray arr n =
  check arr n $
  P.indexSmallArray arr n

{-# INLINE cloneSmallArray #-}
cloneSmallArray :: SmallArray a -> Int -> Int -> SmallArray a
cloneSmallArray arr n len =
  range arr n len $
  P.cloneSmallArray arr n len

{-# INLINE cloneSmallMutableArray #-}
cloneSmallMutableArray :: PrimMonad m => SmallMutableArray (PrimState m) a -> Int -> Int -> m (SmallMutableArray (PrimState m) a)
cloneSmallMutableArray arr n len =
  range arr n len $
  P.cloneSmallMutableArray arr n len

{-# INLINE freezeSmallArray #-}
freezeSmallArray :: PrimMonad m => SmallMutableArray (PrimState m) a -> Int -> Int -> m (SmallArray a)
freezeSmallArray arr n len =
  range arr n len $
  P.freezeSmallArray arr n len

{-# INLINE thawSmallArray #-}
thawSmallArray :: PrimMonad m => SmallArray a -> Int -> Int -> m (SmallMutableArray (PrimState m) a)
thawSmallArray arr n len =
  range arr n len $
  P.thawSmallArray arr n len

{-# INLINE copySmallArray #-}
copySmallArray :: PrimMonad m => SmallMutableArray (PrimState m) a -> Int -> SmallArray a -> Int -> Int -> m ()
copySmallArray arr1 n1 arr2 n2 len =
  range arr1 n1 len $
  range arr2 n2 len $
  P.copySmallArray arr1 n1 arr2 n2 len

{-# INLINE copySmallMutableArray #-}
copySmallMutableArray :: PrimMonad m => SmallMutableArray (PrimState m) a -> Int -> SmallMutableArray (PrimState m) a -> Int -> Int -> m ()
copySmallMutableArray arr1 n1 arr2 n2 len =
  range arr1 n1 len $
  range arr2 n2 len $
  P.copySmallMutableArray arr1 n1 arr2 n2 len
