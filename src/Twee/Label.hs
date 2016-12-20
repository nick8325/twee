-- | Assignment of unique IDs to values.
-- Inspired by the 'intern' package.

{-# LANGUAGE RecordWildCards, ScopedTypeVariables #-}
module Twee.Label(label) where

import Data.IORef
import System.IO.Unsafe
import qualified Data.Map.Strict as Map
import Data.Map.Strict(Map)
import Twee.Term
import Data.Typeable
import GHC.Exts
import Unsafe.Coerce

data Cache a =
  Cache {
    cache_nextId :: {-# UNPACK #-} !Int,
    cache_from   :: !(Map a Int) }
  deriving Show

{-# NOINLINE caches #-}
caches :: IORef (Map TypeRep (Cache Any))
caches = unsafePerformIO (newIORef Map.empty)

toAny :: Cache a -> Cache Any
toAny = unsafeCoerce

fromAny :: Cache Any -> Cache a
fromAny = unsafeCoerce

{-# INLINE withCache #-}
withCache :: forall a b. Typeable a => (Cache a -> (Maybe (Cache a), b)) -> b
withCache update =
  unsafeDupablePerformIO $
    atomicModifyIORef' caches $ \caches ->
      let
        emptyCache = Cache 0 Map.empty
        ty = typeOf (undefined :: a)
        cache = Map.findWithDefault emptyCache ty caches
        (mcache, res) = update (fromAny cache)
      in
        case mcache of
          Nothing -> (caches, res)
          Just cache ->
            (Map.insert ty (toAny cache) caches, res)

label :: (Typeable a, Ord a) => a -> Int
label x =
  compare x x `seq`
  withCache $ \Cache{..} ->
    case Map.lookup x cache_from of
      Nothing ->
        (Just $ Cache
           (cache_nextId+1)
           (Map.insert x cache_nextId cache_from),
         cache_nextId)
      Just n -> (Nothing, n)
