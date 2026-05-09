-- | A serialisation library with support for sharing. Built on top of binary.

{-# LANGUAGE ConstraintKinds, GADTs, DerivingVia, TypeSynonymInstances, FlexibleInstances, DefaultSignatures, DeriveAnyClass, DeriveFunctor, TupleSections #-}
module Data.Binary.Sharing(Binary(..), Shared(..), Put, PutM, encode, runPut, liftPut, unliftPut, Get, decode, runGet, liftGet, unliftGet, putList, getList, putWord8, getWord8, putInt8, getInt8, putIntegral, getIntegral, ReadShowBinary(..)) where
import qualified Data.Binary as S
import qualified Data.Binary.Get as S
import qualified Data.Binary.Put as S
import Data.Typeable
import qualified Data.HashMap.Strict as HashMap
import Data.HashMap.Strict(HashMap)
import Data.Maybe
import GHC.Generics
import Data.Hashable
import Control.Monad
import Data.Bits
import Data.Word
import Data.Int
import Data.Char
import qualified Data.ByteString.Lazy as BS
import qualified Data.ByteString as BSS
import Control.Monad.Trans.State.Strict hiding (get, put)
import qualified Control.Monad.Trans.State.Strict as State
import qualified Data.Primitive.SmallArray as SmallArray
import qualified Data.Foldable as Foldable
import qualified Data.Map as Map
import qualified Data.IntMap as IntMap
import qualified Data.Set as Set
import qualified Data.IntSet as IntSet
import qualified Data.HashSet as HashSet

----------------------------------------------------------------------
-- The basic serialiser/deserialiser types.
--
-- The idea is that both serialisation and deserialisation maintain a
-- store of shared values we have already seen (each associated with an
-- ID). When we emit a value we have already seen, we instead just emit
-- its ID. This is handled in the "Binary (Shared a)" instance.
----------------------------------------------------------------------

-- | A serialiser.
newtype PutM a = PutM { unPutM :: Store -> S.PutM (a, Store) } deriving Functor
-- Note we can't use StateT because then generalised newtype deriving doesn't work
instance Applicative PutM where
  pure x = PutM $ \store -> pure (x, store)
  mf <*> mx = mf >>= \f -> mx >>= \x -> pure (f x)
instance Monad PutM where
  mx >>= f =
    PutM $ \store -> do
      (x, store) <- unPutM mx store
      unPutM (f x) store
type Put = PutM ()

instance Semigroup Put where
  mx <> my = do { mx; my }

instance Monoid Put where
  mempty = pure mempty

-- Lift a state-monadic computation into Put.
liftStatePut :: State Store a -> PutM a
liftStatePut act = PutM $ \store -> return (runState act store)

-- | Lift a binary serialiser into Put.
liftPut :: S.PutM a -> PutM a
liftPut putter = PutM $ \store -> (, store) <$> putter

-- | Convert a 'Put' back into a binary serialiser.
unliftPut :: PutM a -> S.PutM a
unliftPut (PutM putter) = fst <$> putter emptyStore

-- | Serialise a value.
runPut :: Put -> BS.ByteString
runPut = S.runPut . unliftPut

-- | Serialise a value.
encode :: Binary a => a -> BS.ByteString
encode = runPut . put

-- | A deserialiser.
newtype Get a = Get { unGet :: Store -> S.Get (a, Store) } deriving Functor
instance Applicative Get where
  pure x = Get $ \store -> pure (x, store)
  mf <*> mx = mf >>= \f -> mx >>= \x -> pure (f x)
instance Monad Get where
  mx >>= f =
    Get $ \store -> do
      (x, store) <- unGet mx store
      unGet (f x) store

-- Lift a state-monadic computation into Get.
liftStateGet :: State Store a -> Get a
liftStateGet act = Get $ \store -> return (runState act store)

-- | Lift a binary serialiser into Get.
liftGet :: S.Get a -> Get a
liftGet getter = Get $ \store -> (, store) <$> getter

-- | Convert a 'Get' back into a binary serialiser.
unliftGet :: Get a -> S.Get a
unliftGet (Get getter) = fst <$> getter emptyStore

-- | Deserialise a value.
runGet :: Get a -> BS.ByteString -> a
runGet = S.runGet . unliftGet

-- | Deserialise a value.
decode :: Binary a => BS.ByteString -> a
decode = runGet get

----------------------------------------------------------------------
-- The sharing primitive.
----------------------------------------------------------------------

-- | A newtype wrapper which uses sharing on serialisation.
-- If the same 'Shared' value is 'put' multiple times, only the first
-- occurrence will be serialised in full and the later ones will
-- instead serialise as a "pointer" to the first one. The test for
-- whether a value is the same as a previous one uses '(==)'.
newtype Shared a = Shared { getShared :: a } deriving (Eq, Show)

-- The binary format for a "Shared a".
-- The first time a given Shared value appears, we allocate a key (ID) for
-- it and emit it as a 'Let'; if it reoccurs, we emit a 'Ref' to the existing ID.
data SharedEncoding a = Let Key a | Ref Key

instance Binary a => Binary (SharedEncoding a) where
  put (Let key x) = do
    put (key `unsafeShiftL` 1)
    put x
  put (Ref key) = do
    put (key `unsafeShiftL` 1 + 1)

  get = do
    keyTag <- get
    let key = keyTag `unsafeShiftR` 1
    case testBit keyTag 0 of
      False -> do -- Let
        x <- get
        return (Let key x)
      True -> -- Ref
        return (Ref key)

instance (Typeable a, Eq a, Hashable a, Binary a) => Binary (Shared a) where
  put (Shared x) = do
    mkey <- liftStatePut (lookupValue x)
    case mkey of
      Just key ->
        put (Ref key :: SharedEncoding a)
      Nothing -> do
        key <- liftStatePut reserveKey
        put (Let key x)
        liftStatePut (addValue key x)

  get = Shared <$> do
    value <- get
    case value of
      Let key x -> do
        liftStateGet (addValue key x)
        return x
      Ref key ->
        liftStateGet (lookupKey key)

----------------------------------------------------------------------
-- The store of previously-seen values.
----------------------------------------------------------------------

data Store =
  Store {
    -- Maps between values and ID numbers.
    store_keys :: HashMap Key Value,
    store_values :: HashMap Value Key,
    -- The next available ID number.
    store_next_key :: Key }
type Key = Integer

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

emptyStore :: Store
emptyStore = Store HashMap.empty HashMap.empty 0

-- Check if an existing value exists in the store.
lookupValue :: (Eq a, Hashable a, Typeable a) => a -> State Store (Maybe Key)
lookupValue x = do
  let value = Value x
  Store{..} <- State.get
  return (fromIntegral <$> HashMap.lookup value store_values)

-- Allocate a new key.
reserveKey :: Monad m => StateT Store m Key
reserveKey = do
  store@Store{..} <- State.get
  State.put store{store_next_key = store_next_key+1}
  return (fromIntegral store_next_key)

-- Add a new value to the store.
addValue :: (Eq a, Hashable a, Typeable a) => Key -> a -> State Store ()
addValue key x = do
  let value = Value x
  store@Store{..} <- State.get
  when (HashMap.member key store_keys) $ error "key already found"
  when (HashMap.member value store_values) $ error "value already found"
  State.put store{
    store_keys = HashMap.insert key value store_keys,
    store_values = HashMap.insert value key store_values }

-- Find a value by ID number.
lookupKey :: Typeable a => Key -> State Store a
lookupKey key = do
  Store{..} <- State.get
  case HashMap.lookup key store_keys of
    Just (Value x) -> return (fromJust (cast x))
    Nothing -> error ("invalid value " ++ show key ++ " " ++ show store_next_key)

----------------------------------------------------------------------
-- Primitive serialisers.
----------------------------------------------------------------------

putWord8 = liftPut . S.putWord8
getWord8 = liftGet S.getWord8
putInt8 = liftPut . S.putInt8
getInt8 = liftGet S.getInt8

putIntegral :: (Integral a, Bits a) => a -> Put
putIntegral n
  | toInteger n >= -1 && toInteger n < 126 =
    putWord8 (clearBit (fromIntegral n) 7)
  | otherwise = do
    putWord8 (setBit (fromIntegral n) 7)
    putIntegral (n `shiftR` 7)

getIntegral :: (Integral a, Bits a) => Get a
getIntegral = getIntegral' 0 0

getIntegral' :: (Integral a, Bits a) => Int -> a -> Get a
getIntegral' !k !n = do
  x <- getWord8
  let !n' = n + fromIntegral (clearBit x 7) `shiftL` k
  if testBit x 7 then getIntegral' (k+7) n'
    else if x == 127 then return (n' - (1 `shiftL` (k+7)))
    else return n'

-- QuickCheck property:
-- quickCheck (withNumTests 1000000 (withMaxSize 100000 (\x -> runGet getIntegral (runPut (putIntegral (x :: Int))) === Right x)))
-- TODO: add to test suite

putList :: (a -> Put) -> [a] -> Put
putList putter xs = do
  put (length xs)
  mapM_ putter xs

getList :: Get a -> Get [a]
getList getter = do
  len <- get
  replicateM len getter

----------------------------------------------------------------------
-- A class for serialisation/deserialisation.
----------------------------------------------------------------------

class Binary a where
  put :: a -> Put
  get :: Get a

  default put :: (Generic a, GBinary (Rep a)) => a -> Put
  put x = gput (from x)

  default get :: (Generic a, GBinary (Rep a)) => Get a
  get = to <$> gget

instance Binary Int where { put = putIntegral; get = getIntegral }
instance Binary Int8 where { put = putInt8; get = getInt8 }
instance Binary Int16 where { put = putIntegral; get = getIntegral }
instance Binary Int32 where { put = putIntegral; get = getIntegral }
instance Binary Int64 where { put = putIntegral; get = getIntegral }
instance Binary Word where { put = putIntegral; get = getIntegral }
instance Binary Word8 where { put = putWord8; get = getWord8 }
instance Binary Word16 where { put = putIntegral; get = getIntegral }
instance Binary Word32 where { put = putIntegral; get = getIntegral }
instance Binary Word64 where { put = putIntegral; get = getIntegral }
instance Binary Integer where { put = putIntegral; get = getIntegral }
instance Binary Char where { put = putIntegral . ord; get = chr <$> getIntegral }
instance Binary BS.ByteString where { put = liftPut . S.put; get = liftGet S.get }
instance Binary BSS.ByteString where { put = liftPut . S.put; get = liftGet S.get }
instance Binary Float where { put = liftPut. S.put; get = liftGet S.get }
instance Binary Double where { put = liftPut . S.put; get = liftGet S.get }
deriving instance Binary Bool
deriving instance Binary ()
deriving instance (Binary a, Binary b) => Binary (a, b)
deriving instance (Binary a, Binary b, Binary c) => Binary (a, b, c)
deriving instance (Binary a, Binary b, Binary c, Binary d) => Binary (a, b, c, d)
deriving instance (Binary a, Binary b, Binary c, Binary d, Binary e) => Binary (a, b, c, d, e)
deriving instance Binary a => Binary (Maybe a)
deriving instance (Binary a, Binary b) => Binary (Either a b)
instance Binary a => Binary (SmallArray.SmallArray a) where
  put = put . Foldable.toList
  get = SmallArray.smallArrayFromList <$> get

-- | Serialise a value via read/show.
newtype ReadShowBinary a = ReadShowBinary { getReadShowBinary :: a }
instance (Show a, Read a) => Binary (ReadShowBinary a) where
  put = put . show . getReadShowBinary
  get = ReadShowBinary . read <$> get

instance Binary a => Binary [a] where
  put = putList put
  get = getList get

instance (Binary k, Binary v, Ord k) => Binary (Map.Map k v) where
  put = put . Map.toList
  get = Map.fromList <$> get

instance (Binary k, Binary v, Hashable k) => Binary (HashMap k v) where
  put = put . HashMap.toList
  get = HashMap.fromList <$> get

instance Binary v => Binary (IntMap.IntMap v) where
  put = put . IntMap.toList
  get = IntMap.fromList <$> get

instance (Binary k, Ord k) => Binary (Set.Set k) where
  put = put . Set.toList
  get = Set.fromList <$> get

instance (Binary k, Hashable k) => Binary (HashSet.HashSet k) where
  put = put . HashSet.toList
  get = HashSet.fromList <$> get

instance Binary IntSet.IntSet where
  put = put . IntSet.toList
  get = IntSet.fromList <$> get

----------------------------------------------------------------------
-- Generic instances.
----------------------------------------------------------------------

class GBinary f where
  gput :: f a -> Put
  gget :: Get (f a)

  gconstructors :: proxy (f a) -> Int
  gconstructors _ = 1

  gconstructor :: f a -> Int
  gconstructor _ = 0

  gputConstructor :: f a -> Put
  gputConstructor = gput

  ggetConstructor :: Int -> Get (f a)
  ggetConstructor 0 = gget
  ggetConstructor _ = error "ggetConstructor: out of bounds"

instance (GBinary f, GBinary g) => GBinary (f :*: g) where
  gput (x :*: y) = do
    gput x
    gput y
  gget = liftM2 (:*:) gget gget

instance (GBinary f, GBinary g) => GBinary (f :+: g) where
  gput x = do
    put (gconstructor x)
    gputConstructor x

  gget = do
    tag <- get
    ggetConstructor tag

  gconstructors _ =
    gconstructors (Proxy :: Proxy (f a)) + gconstructors (Proxy :: Proxy (g a))

  gconstructor (L1 x) = gconstructor x
  gconstructor (R1 x) = gconstructor x + gconstructors (Proxy :: Proxy (f a))

  gputConstructor (L1 x) = gputConstructor x
  gputConstructor (R1 x) = gputConstructor x

  ggetConstructor n
    | n < m = L1 <$> ggetConstructor n
    | otherwise = R1 <$> ggetConstructor (n-m)
    where
      m = gconstructors (Proxy :: Proxy (f a))

instance GBinary f => GBinary (M1 i c f) where
  gput (M1 x) = gput x
  gget = M1 <$> gget
  gconstructors _ = gconstructors (Proxy :: Proxy (f a))
  gconstructor (M1 x) = gconstructor x
  gputConstructor (M1 x) = gputConstructor x
  ggetConstructor n = M1 <$> ggetConstructor n

instance Binary a => GBinary (K1 i a) where
  gput (K1 x) = put x
  gget = K1 <$> get

instance GBinary U1 where
  gput U1 = return ()
  gget = return U1

instance GBinary V1 where
  gput _ = error "gput: void"
  gget = error "gget: void"
  gconstructors _ = 0
  gconstructor _ = error "gconstructor: void"
  gputConstructor = error "gputConstructor: void"
  ggetConstructor _ = error "ggetConstructor: void"
