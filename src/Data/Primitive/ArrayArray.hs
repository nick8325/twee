{-# LANGUAGE MagicHash, UnboxedTuples #-}
module Data.Primitive.ArrayArray where

import Control.Monad.Primitive
import Data.Primitive
import GHC.Prim
import GHC.Types

data ArrayArray = ArrayArray ArrayArray#
data MutableArrayArray s = MutableArrayArray (MutableArrayArray# s)

{-# INLINE newArrayArray #-}
newArrayArray :: PrimMonad m => Int -> m (MutableArrayArray (PrimState m))
newArrayArray (I# len#) =
  primitive $ \s ->
    case newArrayArray# len# s of
      (# s, marray# #) -> (# s, MutableArrayArray marray# #)

{-# INLINE unsafeFreezeArrayArray #-}
unsafeFreezeArrayArray :: PrimMonad m => MutableArrayArray (PrimState m) -> m ArrayArray
unsafeFreezeArrayArray (MutableArrayArray marray#) =
  primitive $ \s ->
    case unsafeFreezeArrayArray# marray# s of
      (# s, array# #) -> (# s, ArrayArray array# #)

{-# INLINE indexByteArrayArray #-}
indexByteArrayArray :: ArrayArray -> Int -> ByteArray
indexByteArrayArray (ArrayArray array#) (I# n#) =
  ByteArray (indexByteArrayArray# array# n#)

{-# INLINE readByteArrayArray #-}
readByteArrayArray :: PrimMonad m => MutableArrayArray (PrimState m) -> Int -> m ByteArray
readByteArrayArray (MutableArrayArray marray#) (I# n#) =
  primitive $ \s -> 
    case readByteArrayArray# marray# n# s of
      (# s, byteArray# #) -> (# s, ByteArray byteArray# #)

{-# INLINE writeByteArrayArray #-}
writeByteArrayArray :: PrimMonad m => MutableArrayArray (PrimState m) -> Int -> ByteArray -> m ()
writeByteArrayArray (MutableArrayArray marray#) (I# n#) (ByteArray byteArray#) =
  primitive_ (writeByteArrayArray# marray# n# byteArray#)

{-# INLINE writeMutableArrayArrayArray #-}
writeMutableArrayArrayArray :: PrimMonad m => MutableArrayArray (PrimState m) -> Int -> MutableArrayArray (PrimState m) -> m ()
writeMutableArrayArrayArray (MutableArrayArray marray#) (I# n#) (MutableArrayArray marray'#) =
  primitive_ (writeMutableArrayArrayArray# marray# n# marray'#)
