-- | A helper module for array bounds checking.

module Data.Primitive.Checked where

import Data.Primitive(Prim, sizeOf)

-- | A type class of things which have a size (e.g., arrays).
class Sized a where
  -- | Read the size of the thing.
  size :: a -> Int

-- | Check that a single access is in bounds.
{-# INLINE check #-}
check :: Sized a => a -> Int -> b -> b
check arr n x
  | n >= 0 && n < size arr = x
  | otherwise = error "out-of-bounds array access"

-- | Check that a range of accesses is in bounds.
-- The range is inclusive.
{-# INLINE range #-}
range :: Sized a => a -> Int -> Int -> b -> b
range arr n len x
  | len < 0 = error "array slice has negative length"
  | len == 0 = x
  | otherwise =
    check arr n $
    check arr (n+len-1) $ x

-- | Check that a single access is in bounds.
-- The index accessed is computed by multiplying by the size
-- of the first argument.
{-# INLINE checkPrim #-}
checkPrim :: (Sized a, Prim b) => b -> a -> Int -> c -> c
checkPrim x arr n res =
  range arr (n*sizeOf x) (sizeOf x) res
  
-- | Check that a range of accesses is in bounds.
-- The range is inclusive.
-- The index accessed is computed by multiplying by the size
-- of the first argument.
{-# INLINE rangePrim #-}
rangePrim :: (Sized a, Prim b) => b -> a -> Int -> Int -> c -> c
rangePrim x arr n len res =
  range arr (n*sizeOf x) (len*sizeOf x) res
  
