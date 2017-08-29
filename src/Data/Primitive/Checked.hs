module Data.Primitive.Checked where

import Data.Primitive(Prim, sizeOf)

class Sized a where
  size :: a -> Int

{-# INLINE check #-}
check :: Sized a => a -> Int -> b -> b
check arr n x
  | n >= 0 && n < size arr = x
  | otherwise = error "out-of-bounds array access"

{-# INLINE range #-}
range :: Sized a => a -> Int -> Int -> b -> b
range arr n len x
  | len < 0 = error "array slice has negative length"
  | len == 0 = x
  | otherwise =
    check arr n $
    check arr (n+len-1) $ x

{-# INLINE checkPrim #-}
checkPrim :: (Sized a, Prim b) => b -> a -> Int -> c -> c
checkPrim x arr n res =
  range arr (n*sizeOf x) (sizeOf x) res
  
{-# INLINE rangePrim #-}
rangePrim :: (Sized a, Prim b) => b -> a -> Int -> Int -> c -> c
rangePrim x arr n len res =
  range arr (n*sizeOf x) (len*sizeOf x) res
  
