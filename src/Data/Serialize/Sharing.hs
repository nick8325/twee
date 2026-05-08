-- | Support for sharing in Data.Serialize.

{-# LANGUAGE ConstraintKinds, FlexibleInstances, UndecidableInstances, GADTs, DeriveGeneric, DeriveAnyClass, RankNTypes #-}
module Data.Serialize.Sharing(Serialize, WithSharing, withSharing, Shared(..)) where

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

-- | A newtype wrapper which uses sharing on serialization.
-- If the same 'Shared' value is 'put' multiple times, only the first
-- occurrence will be serialized in full and the later ones will
-- instead serialize as a "pointer" to the first one. The test for
-- whether a value is the same as a previous one uses '(==)'.
newtype Shared a = Shared { getShared :: a }

-- | A context which is used by the @'Serialize' ('Shared' a)@ instance.
type WithSharing = Given (IORef Store)

-- | Create a 'WithSharing' context. For example:
--
-- > serializedData = withSharing encode value
-- > Right value' = withSharing decode serializedData
--
-- Typically this goes around 'encode'/'decode'. It can go elsewhere,
-- but note that:
--
-- 1. Encoding and decoding must match up, i.e. 'withSharing' needs to go
--    in the same place on both.
-- 2. Values are only shared if they occur within the same 'withSharing'.
{-# NOINLINE withSharing #-}
withSharing :: (WithSharing => a) -> a
withSharing x = unsafePerformIO $ do { store <- newIORef empty; return (give store x) }
  where
    empty = Store IntMap.empty HashMap.empty 0

-- Implementation idea:
-- 1. Both get and put maintain a store of shared values we have
--    already read/written. Each value is assigned an ID number.
--    Morally the store should be some kind of StateT over Get/PutM,
--    but for ease of use we use an IORef and unsafePerformIO...
-- 2. We serialise a shared value as either its ID number (if it's
--    already been written) or its value (if this is the first time
--    it's been tagged). In the second case we don't write out the ID
--    number since it will always be the next available one.

-- The binary format for a "Shared a".
data SharedEncoding a = New a | Old CompactWord deriving (Generic, Serialize)

instance (WithSharing, Typeable a, Eq a, Hashable a, Serialize a) => Serialize (Shared a) where
  put (Shared x) = do
    mkey <- unsafeLiftIO (lookupValue x)
    case mkey of
      Just key ->
        put (Old (Compact key) :: SharedEncoding a)
      Nothing -> do
        put (New x :: SharedEncoding a)
        -- Important to do this only after putting the value, in case
        -- the call to 'put' ends up putting shared values of its own
        -- (so that the order of addValues in get and put matches up)
        unsafeLiftIO (addValue x)

  get = Shared <$> do
    value <- get
    case value of
      New x -> do
        unsafeLiftIO (addValue x)
        return x
      Old (Compact n) ->
        unsafeLiftIO (lookupKey n)

-- The store of previously-seen values.
data Store =
  Store {
    -- Maps between values and ID numbers.
    store_keys :: IntMap Value,
    store_values :: HashMap Value Int,
    -- The next available ID number.
    store_next_key :: Int }

-- Useful for making heterogeneous maps.
data Value where
  Value :: (Eq a, Hashable a, Typeable a) => a -> Value

instance Eq Value where
  Value x == Value y =
    case cast x of
      Just x' -> x' == y
      Nothing -> error "type error"

instance Hashable Value where
  hashWithSalt s (Value x) = hashWithSalt s (typeOf x, x)

-- Check if an existing value exists in the store.
lookupValue :: (WithSharing, Eq a, Hashable a, Typeable a) => a -> IO (Maybe Word)
lookupValue x = do
  let value = Value x
  Store{..} <- readIORef given
  return (fromIntegral <$> HashMap.lookup value store_values)

-- Add a new value to the store.
addValue :: (WithSharing, Eq a, Hashable a, Typeable a) => a -> IO ()
addValue x = do
  let value = Value x
  store@Store{..} <- readIORef given
  when (HashMap.member value store_values) $ error "value already found"
  writeIORef given store{
    store_keys = IntMap.insert store_next_key value store_keys,
    store_values = HashMap.insert value store_next_key store_values,
    store_next_key = store_next_key + 1 }

-- Find a value by ID number.
lookupKey :: (WithSharing, Typeable a) => Word -> IO a
lookupKey key = do
  Store{..} <- readIORef given
  case IntMap.lookup (fromIntegral key) store_keys of
    Just (Value x) -> return (fromJust (cast x))
    Nothing -> error ("invalid value " ++ show key ++ " " ++ show store_next_key)

-- Lift IO into an arbitrary monad, in a very suspect manner.
unsafeLiftIO :: Monad m => IO a -> m a
unsafeLiftIO act = do
  res <- return (unsafePerformIO act)
  res `pseq` return res
