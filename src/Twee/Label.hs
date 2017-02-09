-- | Assignment of unique IDs to values.
-- Inspired by the 'intern' package.

{-# LANGUAGE RecordWildCards, ScopedTypeVariables, BangPatterns #-}
module Twee.Label(Label, unsafeMkLabel, labelNum, label, find) where

import Data.IORef
import System.IO.Unsafe
import qualified Data.Map.Strict as Map
import Data.Map.Strict(Map)
import qualified Data.IntMap.Strict as IntMap
import Data.IntMap.Strict(IntMap)
import Data.Typeable
import GHC.Exts
import Unsafe.Coerce

newtype Label a = Label { labelNum :: Int }
  deriving (Eq, Ord, Show)
unsafeMkLabel :: Int -> Label a
unsafeMkLabel = Label

type Cache a = Map a Int

data Caches =
  Caches {
    caches_nextId :: {-# UNPACK #-} !Int,
    caches_from   :: !(Map TypeRep (Cache Any)),
    caches_to     :: !(IntMap Any) }

{-# NOINLINE caches #-}
caches :: IORef Caches
caches = unsafePerformIO (newIORef (Caches 0 Map.empty IntMap.empty))

toAnyCache :: Cache a -> Cache Any
toAnyCache = unsafeCoerce

fromAnyCache :: Cache Any -> Cache a
fromAnyCache = unsafeCoerce

toAny :: a -> Any
toAny = unsafeCoerce

fromAny :: Any -> a
fromAny = unsafeCoerce

{-# NOINLINE label #-}
label :: forall a. (Typeable a, Ord a) => a -> Label a
label x =
  compare x x `seq`
  unsafeDupablePerformIO $
    atomicModifyIORef' caches $ \caches@Caches{..} ->
    let
      ty = typeOf x
      cache =
        fromAnyCache $
        Map.findWithDefault Map.empty ty caches_from
    in
      case Map.lookup x cache of
        Just n -> (caches, Label n)
        Nothing ->
          let n = caches_nextId in
          (Caches {
             caches_nextId = n+1,
             caches_to = IntMap.insert n (toAny x) caches_to,
             caches_from = Map.insert ty (toAnyCache (Map.insert x n cache)) caches_from },
           Label n)

find :: Label a -> a
-- N.B. must force n before calling readIORef, otherwise a call of
-- the form
--   find (label x)
-- doesn't work.
find (Label !n) = unsafeDupablePerformIO $ do
  Caches{..} <- readIORef caches
  return (fromAny (IntMap.findWithDefault undefined n caches_to))
