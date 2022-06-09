-- | Assignment of unique IDs to values.
-- Inspired by the 'intern' package.

{-# LANGUAGE RecordWildCards, ScopedTypeVariables, BangPatterns, MagicHash, RoleAnnotations #-}
module Data.Label(Label, unsafeMkLabel, labelNum, label, find) where

import Data.IORef
import System.IO.Unsafe
import qualified Data.Map.Strict as Map
import Data.Map.Strict(Map)
import qualified Data.DynamicArray as DynamicArray
import Data.DynamicArray(Array)
import Data.Typeable
import GHC.Exts
import GHC.Int
import Unsafe.Coerce

-- | A value of type @a@ which has been given a unique ID.
newtype Label a =
  Label {
    -- | The unique ID of a label.
    labelNum :: Int32 }
  deriving (Eq, Ord, Show)

type role Label nominal

-- | Construct a @'Label' a@ from its unique ID, which must be the 'labelNum' of
-- an already existing 'Label'. Extremely unsafe!
unsafeMkLabel :: Int32 -> Label a
unsafeMkLabel = Label

-- The global cache of labels.
{-# NOINLINE cachesRef #-}
cachesRef :: IORef Caches
cachesRef = unsafePerformIO (newIORef (Caches 0 Map.empty DynamicArray.newArray))

data Caches =
  Caches {
    -- The next id number to assign.
    caches_nextId :: {-# UNPACK #-} !Int32,
    -- A map from values to labels.
    caches_from   :: !(Map TypeRep (Cache Any)),
    -- The reverse map from labels to values.
    caches_to     :: !(Array Any) }

type Cache a = Map a Int32

atomicModifyCaches :: (Caches -> (Caches, a)) -> IO a
atomicModifyCaches f = do
  -- N.B. atomicModifyIORef' ref f evaluates f ref *after* doing the
  -- compare-and-swap. This causes bad things to happen when 'label'
  -- is used reentrantly (i.e. the Ord instance itself calls label).
  -- This function only lets the swap happen if caches_nextId didn't
  -- change (i.e., no new values were inserted).
  !caches <- readIORef cachesRef
  -- First compute the update.
  let !(!caches', !x) = f caches
  -- Now see if anyone else updated the cache in between
  -- (can happen if f called 'label', or in a concurrent setting).
  ok <- atomicModifyIORef' cachesRef $ \cachesNow ->
    if caches_nextId caches == caches_nextId cachesNow
    then (caches', True)
    else (cachesNow, False)
  if ok then return x else atomicModifyCaches f

-- Versions of unsafeCoerce with slightly more type checking
toAnyCache :: Cache a -> Cache Any
toAnyCache = unsafeCoerce

fromAnyCache :: Cache Any -> Cache a
fromAnyCache = unsafeCoerce

toAny :: a -> Any
toAny = unsafeCoerce

fromAny :: Any -> a
fromAny = unsafeCoerce

-- | Assign a label to a value.
{-# NOINLINE label #-}
label :: forall a. (Typeable a, Ord a) => a -> Label a
label x =
  unsafeDupablePerformIO $ do
    -- Common case: label is already there.
    caches <- readIORef cachesRef
    case tryFind caches of
      Just l -> return l
      Nothing -> do
        -- Rare case: label was not there.
        x <- atomicModifyCaches $ \caches ->
          case tryFind caches of
            Just l -> (caches, l)
            Nothing ->
              insert caches
        return x

  where
    ty = typeOf x

    tryFind :: Caches -> Maybe (Label a)
    tryFind Caches{..} =
      Label <$> (Map.lookup ty caches_from >>= Map.lookup x . fromAnyCache)

    insert :: Caches -> (Caches, Label a)
    insert caches@Caches{..} =
      if n < 0 then error "label overflow" else
      (caches {
         caches_nextId = n+1,
         caches_from = Map.insert ty (toAnyCache (Map.insert x n cache)) caches_from,
         caches_to = DynamicArray.updateWithDefault undefined (fromIntegral n) (toAny x) caches_to },
       Label n)
      where
        n = caches_nextId
        cache =
          fromAnyCache $
          Map.findWithDefault Map.empty ty caches_from

-- | Recover the underlying value from a label.
find :: Label a -> a
-- N.B. must force n before calling readIORef, otherwise a call of
-- the form
--   find (label x)
-- doesn't work.
find (Label !(I32# n#)) = findWorker n#

{-# NOINLINE findWorker #-}
findWorker :: Int32# -> a
findWorker n# =
  unsafeDupablePerformIO $ do
    let n = I32# n#
    Caches{..} <- readIORef cachesRef
    x <- return $! fromAny (DynamicArray.getWithDefault undefined (fromIntegral n) caches_to)
    return x
