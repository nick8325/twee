{-# LANGUAGE ScopedTypeVariables #-}
module Data.MemoFun(MemoFun, memo, apply) where

import Data.DynamicArray
import Twee.Term
import Data.IORef
import System.IO.Unsafe

data MemoFun a b = MemoFun (IORef (Array (Maybe b))) (Fun a -> b)

memo :: forall a b. (Fun a -> b) -> MemoFun a b
memo f =
  unsafePerformIO $ do
    ref <- newIORef (newArray :: Array (Maybe b))
    return (MemoFun ref f)

apply :: MemoFun a b -> Fun a -> b
apply (MemoFun ref f) x = unsafePerformIO $ do
  table <- readIORef ref
  case table ! fun_id x of
    Nothing -> do
      let y = f x
      atomicModifyIORef' ref (\table -> (update (fun_id x) (Just y) table, ()))
      return y
    Just y -> return y
