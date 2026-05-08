-- | Support for sharing in Data.Serialize.

{-# LANGUAGE ConstraintKinds, FlexibleContexts, FlexibleInstances, UndecidableInstances, GADTs, DeriveGeneric, DeriveAnyClass, BangPatterns, RecordWildCards, RankNTypes, ScopedTypeVariables #-}
module Data.Serialize.Sharing(Serialize, WithSharing, putWithSharing, getWithSharing, Shared(..)) where

import Data.Serialize
import Data.Typeable
import qualified Data.IntMap.Strict as IntMap
import Data.IntMap(IntMap)
import qualified Data.HashMap.Strict as HashMap
import Data.HashMap.Strict(HashMap)
import System.IO.Unsafe
import Data.IORef
import Data.Reflection
import Data.Maybe
import GHC.Generics
import Data.Hashable
import Control.Parallel
import Control.Monad
import Twee.Utils

type WithSharing = Given (IORef Store)

putWithSharing :: (WithSharing => Put) -> Put
putWithSharing = withStore

getWithSharing :: (WithSharing => Get a) -> Get a
getWithSharing = withStore

newtype Shared a = Shared { getShared :: a }

data SharedEncoding a = New a | Old CompactWord deriving (Generic, Serialize)

unsafeLiftIO :: Monad m => IO a -> m a
unsafeLiftIO act = do
  res <- return (unsafePerformIO act)
  res `pseq` return res

instance (WithSharing, Typeable a, Eq a, Hashable a, Serialize a) => Serialize (Shared a) where
  put (Shared x) = do
    mkey <- unsafeLiftIO (lookupValue x)
    case mkey of
      Just key ->
        put (Old (Compact key) :: SharedEncoding a)
      Nothing -> do
        put (New x :: SharedEncoding a)
        unsafeLiftIO (addValue x)

  get = Shared <$> do
    value <- get
    case value of
      New x -> do
        unsafeLiftIO (addValue x)
        return x
      Old (Compact n) ->
        unsafeLiftIO (lookupKey n)

data Store =
  Store {
    store_keys :: IntMap Value,
    store_values :: HashMap Value Int,
    store_next_key :: Int }

data Value where
  Value :: (Eq a, Hashable a, Typeable a) => a -> Value

instance Eq Value where
  Value x == Value y =
    case cast x of
      Just x' -> x' == y
      Nothing -> error "type error"

instance Hashable Value where
  hashWithSalt s (Value x) = hashWithSalt s (typeOf x, x)

{-# NOINLINE withStore #-}
withStore :: (WithSharing => a) -> a
withStore x = unsafePerformIO $ do { store <- newIORef empty; return (give store x) }
  where
    empty = Store IntMap.empty HashMap.empty 0

lookupValue :: (WithSharing, Eq a, Hashable a, Typeable a) => a -> IO (Maybe Word)
lookupValue x = do
  let value = Value x
  Store{..} <- readIORef given
  return (fromIntegral <$> HashMap.lookup value store_values)

addValue :: (WithSharing, Eq a, Hashable a, Typeable a) => a -> IO ()
addValue x = do
  let value = Value x
  store@Store{..} <- readIORef given
  when (HashMap.member value store_values) $ error "value already found"
  writeIORef given store{
    store_keys = IntMap.insert store_next_key value store_keys,
    store_values = HashMap.insert value store_next_key store_values,
    store_next_key = store_next_key + 1 }

lookupKey :: (WithSharing, Typeable a) => Word -> IO a
lookupKey key = do
  Store{..} <- readIORef given
  case IntMap.lookup (fromIntegral key) store_keys of
    Just (Value x) -> return (fromJust (cast x))
    Nothing -> error ("invalid value " ++ show key ++ " " ++ show store_next_key)
