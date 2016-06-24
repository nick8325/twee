{-# LANGUAGE MagicHash, UnboxedTuples #-}
module Data.Primitive.SmallArray where

import GHC.Prim
import GHC.Types
import GHC.ST

data SmallArray a = SmallArray (SmallArray# a)
data SmallMutableArray s a = SmallMutableArray (SmallMutableArray# s a)

{-# INLINE newSmallArray #-}
newSmallArray :: Int -> a -> ST s (SmallMutableArray s a)
newSmallArray (I# n) x =
  ST $ \s ->
  case newSmallArray# n x s of
    (# s, arr #) -> (# s, SmallMutableArray arr #)
  
{-# INLINE writeSmallArray #-}
writeSmallArray :: SmallMutableArray s a -> Int -> a -> ST s ()
writeSmallArray (SmallMutableArray arr) (I# n) x =
  ST $ \s ->
  case writeSmallArray# arr n x s of
    s -> (# s, () #)

{-# INLINE copySmallArray #-}
copySmallArray :: SmallArray a -> Int -> SmallMutableArray s a -> Int -> Int -> ST s ()
copySmallArray (SmallArray arr) (I# i) (SmallMutableArray marr) (I# j) (I# n) =
  ST $ \s ->
  case copySmallArray# arr i marr j n s of
    s -> (# s, () #)

{-# INLINE unsafeFreezeSmallArray #-}
unsafeFreezeSmallArray :: SmallMutableArray s a -> ST s (SmallArray a)
unsafeFreezeSmallArray (SmallMutableArray marr) =
  ST $ \s ->
  case unsafeFreezeSmallArray# marr s of
    (# s, arr #) -> (# s, SmallArray arr #)

{-# INLINE indexSmallArray #-}
indexSmallArray :: SmallArray a -> Int -> a
indexSmallArray (SmallArray arr) (I# i) =
  case indexSmallArray# arr i of
    (# x #) -> x
