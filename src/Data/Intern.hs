-- | Interning, annotating values with unique IDs.

{-# LANGUAGE RecordWildCards, ScopedTypeVariables, BangPatterns, MagicHash, RoleAnnotations, CPP, PatternSynonyms, ViewPatterns, ConstraintKinds #-}
module Data.Intern(Intern, Sym, pattern Sym, intern, unintern, unsafeMkSym, symId) where

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

-- | Type class constraints for a value to be internable.
type Intern a = (Typeable a, Ord a)

-- | An interned value of type @a@.
newtype Sym a = MkSym Int32
  deriving (Eq, Ord, Show)

-- | The unique ID of a symbol.
symId :: Sym a -> Int
symId (MkSym x) = fromIntegral x

type role Sym nominal -- no coercions please

-- | Construct a @'Sym' a@ from its unique ID, which must be the 'symId' of
-- an already existing 'Sym'. Extremely unsafe!
unsafeMkSym :: Int -> Sym a
unsafeMkSym = MkSym . fromIntegral

-- The global cache of interned values.
{-# NOINLINE cachesRef #-}
cachesRef :: IORef Caches
cachesRef = unsafePerformIO (newIORef (Caches 0 Map.empty DynamicArray.newArray))

data Caches =
  Caches {
    -- The next id number to assign.
    caches_nextId :: {-# UNPACK #-} !Int32,
    -- A map from values to IDs.
    caches_from   :: !(Map TypeRep (Cache Any)),
    -- The reverse map from IDs to values.
    caches_to     :: !(Array Any) }

type Cache a = Map a Int32

atomicModifyCaches :: (Caches -> (Caches, a)) -> IO a
atomicModifyCaches f = do
  -- N.B. atomicModifyIORef' ref f evaluates f ref *after* doing the
  -- compare-and-swap. This causes bad things to happen when 'intern'
  -- is used reentrantly (i.e. the Ord instance itself calls intern).
  -- This function only lets the swap happen if caches_nextId didn't
  -- change (i.e., no new values were inserted).
  !caches <- readIORef cachesRef
  -- First compute the update.
  let !(!caches', !x) = f caches
  -- Now see if anyone else updated the cache in between
  -- (can happen if f called 'intern', or in a concurrent setting).
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

-- | Intern a value.
{-# NOINLINE intern #-}
intern :: forall a. Intern a => a -> Sym a
intern x =
  unsafeDupablePerformIO $ do
    -- Common case: symbol is already interned.
    caches <- readIORef cachesRef
    case tryFind caches of
      Just s -> return s
      Nothing -> do
        -- Rare case: symbol has not yet been interned.
        x <- atomicModifyCaches $ \caches ->
          case tryFind caches of
            Just s -> (caches, s)
            Nothing ->
              insert caches
        return x

  where
    ty = typeOf x

    tryFind :: Caches -> Maybe (Sym a)
    tryFind Caches{..} =
      MkSym <$> (Map.lookup ty caches_from >>= Map.lookup x . fromAnyCache)

    insert :: Caches -> (Caches, Sym a)
    insert caches@Caches{..} =
      if n < 0 then error "label overflow" else
      (caches {
         caches_nextId = n+1,
         caches_from = Map.insert ty (toAnyCache (Map.insert x n cache)) caches_from,
         caches_to = DynamicArray.updateWithDefault undefined (fromIntegral n) (toAny x) caches_to },
       MkSym n)
      where
        n = caches_nextId
        cache =
          fromAnyCache $
          Map.findWithDefault Map.empty ty caches_from

-- | Recover the underlying value from a 'Sym'.
unintern :: Sym a -> a
-- N.B. must force n before calling readIORef, otherwise a call of
-- the form
--   unintern (intern x)
-- doesn't work.
unintern (MkSym !(I32# n#)) = uninternWorker n#

{-# NOINLINE uninternWorker #-}
#if __GLASGOW_HASKELL__ >= 902
uninternWorker :: Int32# -> a
#else
uninternWorker :: Int# -> a
#endif
uninternWorker n# =
  unsafeDupablePerformIO $ do
    let n = I32# n#
    Caches{..} <- readIORef cachesRef
    x <- return $! fromAny (DynamicArray.getWithDefault undefined (fromIntegral n) caches_to)
    return x

pattern Sym :: Intern a => a -> Sym a
pattern Sym x <- (unintern -> x) where
  Sym x = intern x
