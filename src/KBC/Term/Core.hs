-- Terms and substitutions, implemented using flatterms.
-- This module contains all the low-level icky bits
-- and provides primitives for building higher-level stuff.
{-# LANGUAGE BangPatterns, CPP, PatternGuards, PatternSynonyms, ViewPatterns, RecordWildCards, GeneralizedNewtypeDeriving, RankNTypes, MagicHash, UnboxedTuples #-}
module KBC.Term.Core where

#include "errors.h"
import Data.Primitive
import Control.Monad
import Control.Monad.ST.Strict
import Data.Bits
import Data.Int
import Data.Word
import Data.List hiding (lookup)
import GHC.Types(Int(..))
import GHC.Prim
import GHC.ST hiding (liftST)

--------------------------------------------------------------------------------
-- Symbols. A symbol is a single function or variable in a flatterm.
--------------------------------------------------------------------------------

data Symbol =
  Symbol {
    -- Is it a function?
    isFun :: Bool,
    -- What is its number?
    index :: Int,
    -- What is the size of the term rooted at this symbol?
    size  :: Int }

instance Show Symbol where
  show Symbol{..}
    | isFun = show (MkFun index) ++ "=" ++ show size
    | otherwise = show (MkVar index)

-- Convert symbols to/from Int64 for storage in flatterms.
-- The encoding:
--   * bits 0-31:  size
--   * bits 32-63: index (variable) or ~index (function)
{-# INLINE toSymbol #-}
toSymbol :: Int64 -> Symbol
toSymbol n =
  Symbol (n < 0)
    (if n < 0 then
       complement (fromIntegral (n `unsafeShiftR` 32))
     else
       fromIntegral (n `unsafeShiftR` 32))
    (fromIntegral n .&. 0xffffffff)

{-# INLINE fromSymbol #-}
fromSymbol :: Symbol -> Int64
fromSymbol Symbol{..}
  | isFun =
    fromIntegral (complement index) `unsafeShiftL` 32 +
    fromIntegral size
  | otherwise =
    fromIntegral index `unsafeShiftL` 32 +
    fromIntegral size

--------------------------------------------------------------------------------
-- Flatterms, or rather lists of terms.
--------------------------------------------------------------------------------

-- A TermList is a slice of an unboxed array of symbols.
data TermList f =
  TermList {
    low   :: {-# UNPACK #-} !Int,
    high  :: {-# UNPACK #-} !Int,
    array :: {-# UNPACK #-} !ByteArray }

{-# INLINE len #-}
-- The length (number of symbols in) a flatterm.
len :: TermList f -> Int
len (TermList low high _) = high - low

-- A term is a special case of a termlist.
-- We store it as the termlist together with the root symbol.
data Term f =
  Term {
    root     :: {-# UNPACK #-} !Int64,
    termlist :: {-# UNPACK #-} !(TermList f) }

instance Eq (Term f) where
  x == y = termlist x == termlist y

-- Pattern synonyms for termlists:
-- * Empty :: TermList f
--   Empty is the empty termlist.
-- * Cons t ts :: Term f -> TermList f -> TermList f
--   Cons t ts is the termlist t:ts.
-- * ConsSym t ts :: Term f -> TermList f -> TermList f
--   ConsSym t ts is like Cons t ts but ts also includes t's children
--   (operationally, ts seeks one term to the right in the termlist).
-- * UnsafeCons/UnsafeConsSym: like Cons and ConsSym but don't check
--   that the termlist is non-empty.
pattern Empty <- (patHead -> Nothing)
pattern Cons t ts <- (patHead -> Just (t, _, ts))
pattern ConsSym t ts <- (patHead -> Just (t, ts, _))
pattern UnsafeCons t ts <- (unsafePatHead -> Just (t, _, ts))
pattern UnsafeConsSym t ts <- (unsafePatHead -> Just (t, ts, _))

{-# INLINE unsafePatHead #-}
unsafePatHead :: TermList f -> Maybe (Term f, TermList f, TermList f)
unsafePatHead TermList{..} =
  Just (Term x (TermList low (low+size) array),
        TermList (low+1) high array,
        TermList (low+size) high array)
  where
    x = indexByteArray array low
    Symbol{..} = toSymbol x

{-# INLINE patHead #-}
patHead :: TermList f -> Maybe (Term f, TermList f, TermList f)
patHead t@TermList{..}
  | low == high = Nothing
  | otherwise = unsafePatHead t

-- Pattern synonyms for single terms.
-- * Var :: Var -> Term f
-- * Fun :: Fun f -> TermList f -> Term f
newtype Fun f = MkFun Int deriving (Eq, Ord)
newtype Var   = MkVar Int deriving (Eq, Ord, Enum)
instance Show (Fun f) where show (MkFun x) = "f" ++ show x
instance Show Var     where show (MkVar x) = "x" ++ show x

pattern Var x <- Term (patRoot -> Left x) _
pattern Fun f ts <- Term (patRoot -> Right f) (patNext -> ts)

{-# INLINE patRoot #-}
patRoot :: Int64 -> Either Var (Fun f)
patRoot root
  | isFun     = Right (MkFun index)
  | otherwise = Left (MkVar index)
  where
    Symbol{..} = toSymbol root

{-# INLINE patNext #-}
patNext :: TermList f -> TermList f
patNext (TermList lo hi array) = TermList (lo+1) hi array

-- Convert a term to a termlist.
{-# INLINE singleton #-}
singleton :: Term f -> TermList f
singleton Term{..} = termlist

-- We can implement equality almost without access to the
-- internal representation of the termlists, but we cheat by
-- comparing Int64s instead of Symbols.
instance Eq (TermList f) where
  {-# INLINE (==) #-}
  t == u = len t == len u && eqSameLength t u

eqSameLength :: TermList f -> TermList f -> Bool
eqSameLength Empty !_ = True
eqSameLength (ConsSym s1 t) (UnsafeConsSym s2 u) =
  root s1 == root s2 && eqSameLength t u

--------------------------------------------------------------------------------
-- Building terms imperatively.
--------------------------------------------------------------------------------

-- A monad for building terms.
newtype BuildM s f a =
  BuildM {
    unBuildM ::
      -- Takes: the term array, and current position in the term.
      -- Returns the final position.
      MutableByteArray# s -> Int# -> State# s -> (# State# s, Int#, a #) }

instance Functor (BuildM s f) where
  {-# INLINE fmap #-}
  fmap f (BuildM m) =
    BuildM $ \array i s ->
      case m array i s of
        (# s, j, x #) -> (# s, j, f x #)

instance Applicative (BuildM s f) where
  pure = return
  (<*>) = ap
instance Monad (BuildM s f) where
  {-# INLINE return #-}
  return x = BuildM (\_ i s -> (# s, i, x #))
  {-# INLINE (>>=) #-}
  BuildM m >>= f =
    BuildM $ \array i s ->
      case m array i s of
        (# s, j, x #) -> unBuildM (f x) array j s

{-# INLINE getArray #-}
getArray :: BuildM s f (MutableByteArray s)
getArray = BuildM $ \array n s -> (# s, n, MutableByteArray array #)

{-# INLINE getIndex #-}
getIndex :: BuildM s f Int
getIndex = BuildM $ \_ n s -> (# s, n, I# n #)

{-# INLINE putIndex #-}
putIndex :: Int -> BuildM s f ()
putIndex (I# n) = BuildM $ \_ _ s -> (# s, n, () #)

{-# INLINE liftST #-}
liftST :: ST s a -> BuildM s f a
liftST (ST m) =
  BuildM $ \_ n s ->
  case m s of
    (# s, x #) -> (# s, n, x #)

-- Construct a term, given its size and a builder for it.
{-# INLINE buildTermList #-}
buildTermList :: Int -> (forall s. BuildM s f a) -> a
buildTermList size m =
  runST $ do
    MutableByteArray array <- newByteArray (size * sizeOf (fromSymbol __))
    ST $ \s ->
      case unBuildM m array 0# s of
        (# s, _, x #) -> (# s, x #)

-- Freeze a term that's been built.
{-# INLINE freezeTermList #-}
freezeTermList :: BuildM s f (TermList f)
freezeTermList = do
  marray <- getArray
  n <- getIndex
  !array <- liftST $ unsafeFreezeByteArray marray
  return (TermList 0 n array)

-- Emit a single symbol (for internal use mostly).
{-# INLINE emitSymbol #-}
emitSymbol :: Symbol -> BuildM s f () -> BuildM s f ()
emitSymbol x inner = do
  array <- getArray
  n <- getIndex
  putIndex (n+1)
  inner
  m <- getIndex
  liftST $ writeByteArray array n (fromSymbol x { size = m - n })

-- Emit the root of a term.
-- The second argument is called to emit the children.
{-# INLINE emitRoot #-}
emitRoot :: Term f -> BuildM s f () -> BuildM s f ()
emitRoot t inner = emitSymbol (toSymbol (root t)) inner

-- Emit a function symbol.
-- The second argument is called to emit the function's arguments.
{-# INLINE emitFun #-}
emitFun :: Fun f -> BuildM s f () -> BuildM s f ()
emitFun (MkFun f) inner = emitSymbol (Symbol True f 0) inner

-- Emit a variable.
{-# INLINE emitVar #-}
emitVar :: Var -> BuildM s f ()
emitVar (MkVar x) = emitSymbol (Symbol False x 1) (return ())

-- Emit a whole termlist.
{-# INLINE emitTermList #-}
emitTermList :: TermList f -> BuildM s f ()
emitTermList (TermList lo hi array) = do
  marray <- getArray
  n <- getIndex
  let k = sizeOf (fromSymbol __)
  liftST $ copyByteArray marray (n*k) array (lo*k) ((hi-lo)*k)
  putIndex (n + hi-lo)

--------------------------------------------------------------------------------
-- Substitutions.
--------------------------------------------------------------------------------

-- Substitutions are optimised for matching, where all of the bindings
-- are subterms of a single term (the one we are matching against).
-- A substitution consists of:
-- * A term, the backing term. All of the bindings are subterms of this.
-- * An array, mapping variable numbers to slices of the backing term
--   (pairs of positions).
data Subst f =
  Subst {
    -- The backing term.
    term  :: {-# UNPACK #-} !ByteArray,
    -- The number of variables in the bindings array.
    vars  :: {-# UNPACK #-} !Int,
    -- The bindings: an unboxed array of (Int, Int) pairs.
    subst :: {-# UNPACK #-} !ByteArray }

-- The number of variables in the domain of a substitution.
substSize :: Subst f -> Int
substSize = vars

-- Convert between slices and Word64s for storage.
{-# INLINE toSlice #-}
toSlice :: Word64 -> Maybe (Int, Int)
toSlice 0 = Nothing
toSlice n = Just (fromIntegral n .&. 0xffffffff, fromIntegral (n `unsafeShiftR` 32))

{-# INLINE fromSlice #-}
fromSlice :: (Int, Int) -> Word64
fromSlice (lo, hi) =
  fromIntegral lo .&. 0xffffffff +
  fromIntegral hi `unsafeShiftL` 32

-- Look up a variable.
{-# INLINE lookupList #-}
lookupList :: Subst f -> Var -> Maybe (TermList f)
lookupList Subst{..} (MkVar x)
  | x >= vars = Nothing
  | otherwise = do
    (lo, hi) <- toSlice (indexByteArray subst x)
    return (TermList lo hi term)

-- Mutable substitutions, used for building substitutions.
data MutableSubst s f =
  MutableSubst {
    mterm  :: {-# UNPACK #-} !ByteArray,
    mvars  :: {-# UNPACK #-} !Int,
    msubst :: {-# UNPACK #-} !(MutableByteArray s) }

-- Create an empty substitution, given the backing term
-- and the number of variables required.
{-# INLINE newMutableSubst #-}
newMutableSubst :: TermList f -> Int -> ST s (MutableSubst s f)
newMutableSubst TermList{..} vars = do
  subst <- newByteArray (vars * sizeOf (fromSlice __))
  setByteArray subst 0 vars (0 `asTypeOf` fromSlice __)
  return (MutableSubst array vars subst)

-- Freeze a mutable substitution.
{-# INLINE freezeSubst #-}
freezeSubst :: MutableSubst s f -> ST s (Subst f)
freezeSubst MutableSubst{..} = do
  subst <- unsafeFreezeByteArray msubst
  return (Subst mterm mvars subst)

-- Look up a variable in a mutable substitution.
{-# INLINE mutableLookupList #-}
mutableLookupList :: MutableSubst s f -> Var -> ST s (Maybe (TermList f))
mutableLookupList MutableSubst{..} (MkVar x)
  | x >= mvars = return Nothing
  | otherwise = do
    slice <- readByteArray msubst x
    return $ do
      (lo, hi) <- toSlice slice
      return (TermList lo hi mterm)

-- Add a new binding to a substitution.
-- Returns Just () on success or Nothing if an incompatible
-- binding already existed.
{-# INLINE extendList #-}
extendList :: MutableSubst s f -> Var -> TermList f -> ST s (Maybe ())
extendList MutableSubst{..} (MkVar x) (TermList lo hi _) = do
  rng <- fmap toSlice (readByteArray msubst x)
  case rng of
    Nothing -> do
      writeByteArray msubst x (fromSlice (lo, hi))
      return (Just ())
    Just (lo', hi')
      | TermList lo hi mterm == TermList lo' hi' mterm ->
        return (Just ())
      | otherwise ->
        return Nothing
