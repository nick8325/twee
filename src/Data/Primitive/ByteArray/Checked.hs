{-# LANGUAGE ScopedTypeVariables #-}
module Data.Primitive.ByteArray.Checked(
  module Data.Primitive.ByteArray,
  module Data.Primitive.ByteArray.Checked) where

import Control.Monad.Primitive
import qualified Data.Primitive.ByteArray as P
import Data.Primitive(Prim)
import Data.Primitive.ByteArray(
  ByteArray(..), MutableByteArray(..),
  newByteArray, newPinnedByteArray, newAlignedPinnedByteArray,
  byteArrayContents, mutableByteArrayContents,
  sameMutableByteArray,
  unsafeFreezeByteArray, unsafeThawByteArray,
  sizeofByteArray, sizeofMutableByteArray)
import Data.Primitive.Checked
import Data.Word

instance Sized ByteArray where
  size = sizeofByteArray
instance Sized (MutableByteArray m) where
  size = sizeofMutableByteArray

{-# INLINE readByteArray #-}
readByteArray :: forall m a. (PrimMonad m, Prim a) => MutableByteArray (PrimState m) -> Int -> m a
readByteArray arr n =
  checkPrim (undefined :: a) arr n $
  P.readByteArray arr n

{-# INLINE writeByteArray #-}
writeByteArray :: (PrimMonad m, Prim a) => MutableByteArray (PrimState m) -> Int -> a -> m ()
writeByteArray arr n x =
  checkPrim x arr n $
  P.writeByteArray arr n x

{-# INLINE indexByteArray #-}
indexByteArray :: forall a. Prim a => ByteArray -> Int -> a
indexByteArray arr n =
  checkPrim (undefined :: a) arr n $
  P.indexByteArray arr n

{-# INLINE copyByteArray #-}
copyByteArray :: PrimMonad m => MutableByteArray (PrimState m) -> Int -> ByteArray -> Int -> Int -> m ()
copyByteArray arr1 n1 arr2 n2 len =
  range arr1 n1 len $
  range arr2 n2 len $
  P.copyByteArray arr1 n1 arr2 n2 len

{-# INLINE moveByteArray #-}
moveByteArray :: PrimMonad m => MutableByteArray (PrimState m) -> Int -> MutableByteArray (PrimState m) -> Int -> Int -> m ()
moveByteArray arr1 n1 arr2 n2 len =
  range arr1 n1 len $
  range arr2 n2 len $
  P.moveByteArray arr1 n1 arr2 n2 len

{-# INLINE copyMutableByteArray #-}
copyMutableByteArray :: PrimMonad m => MutableByteArray (PrimState m) -> Int -> MutableByteArray (PrimState m) -> Int -> Int -> m ()
copyMutableByteArray arr1 n1 arr2 n2 len =
  range arr1 n1 len $
  range arr2 n2 len $
  P.copyMutableByteArray arr1 n1 arr2 n2 len

{-# INLINE setByteArray #-}
setByteArray :: (Prim a, PrimMonad m) => MutableByteArray (PrimState m) -> Int -> Int -> a -> m ()
setByteArray arr n len x =
  rangePrim x arr n len $
  P.setByteArray arr n len x

{-# INLINE fillByteArray #-}
fillByteArray :: PrimMonad m => MutableByteArray (PrimState m) -> Int -> Int -> Word8 -> m ()
fillByteArray = setByteArray
