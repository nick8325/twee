-- Terms and substitutions, implemented using flatterms.
-- This module contains all the low-level icky bits
-- and provides primitives for building higher-level stuff.
{-# LANGUAGE BangPatterns, CPP, PatternGuards, PatternSynonyms, ViewPatterns, RecordWildCards, GeneralizedNewtypeDeriving, RankNTypes, MagicHash, UnboxedTuples, MultiParamTypeClasses, FlexibleInstances, FunctionalDependencies, ScopedTypeVariables #-}
module KBC.Term.Flat.Core where

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
import Data.Primitive.ArrayArray

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

{-# INLINE lenList #-}
-- The length (number of symbols in) a flatterm.
lenList :: TermList f -> Int
lenList (TermList low high _) = high - low

{-# INLINE sharedList #-}
-- Do two termlists share the same array?
-- Sometimes useful when generating substitutions (see below).
sharedList :: TermList f -> TermList f -> Bool
sharedList t u = sameArray (array t) (array u)

{-# INLINE sameArray #-}
sameArray :: ByteArray -> ByteArray -> Bool
sameArray (ByteArray array1#) (ByteArray array2#) =
  tagToEnum# (reallyUnsafePtrEquality# addr1# addr2#)
  where
    addr1# = unsafeCoerce# array1#
    addr2# = unsafeCoerce# array2#

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
pattern Fun f ts <- Term (patRoot -> Right (f :: Fun f)) (patNext -> (ts :: TermList f))

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
  t == u = lenList t == lenList u && eqSameLength t u

eqSameLength :: TermList f -> TermList f -> Bool
eqSameLength Empty !_ = True
eqSameLength (ConsSym s1 t) (UnsafeConsSym s2 u) =
  root s1 == root s2 && eqSameLength t u

--------------------------------------------------------------------------------
-- Building terms imperatively.
--------------------------------------------------------------------------------

class Monad m => Builder f m | m -> f where
  -- Emit the root of a term.
  -- The second argument is called to emit the children.
  emitRoot :: Term f -> m () -> m ()
  -- Emit a function symbol.
  -- The second argument is called to emit the function's arguments.
  emitFun :: Fun f -> m () -> m ()
  -- Emit a variable.
  emitVar :: Var -> m ()
  -- Emit a whole termlist.
  emitTermList :: TermList f -> m ()

-- A monad for building terms.
newtype BuildM s f a =
  BuildM {
    unBuildM ::
      -- Takes: the term array, and current position in the term.
      -- Returns the final position.
      MutableByteArray# s -> Int# -> State# s -> (# State# s, Int#, a #) }

{-# INLINE runBuildM #-}
runBuildM :: BuildM s f a -> MutableByteArray s -> ST s Int
runBuildM (BuildM m) (MutableByteArray array) =
  ST $ \s ->
    case m array 0# s of
      (# s, n#, _ #) -> (# s, I# n# #)

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

instance Builder f (BuildM s f) where
  emitRoot     = emitRootBuildM
  emitFun      = emitFunBuildM
  emitVar      = emitVarBuildM
  emitTermList = emitTermListBuildM

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

{-# INLINE emitSymbolBuildM #-}
emitSymbolBuildM :: Symbol -> BuildM s f () -> BuildM s f ()
emitSymbolBuildM x inner = do
  array <- getArray
  n <- getIndex
  putIndex (n+1)
  inner
  m <- getIndex
  liftST $ writeByteArray array n (fromSymbol x { size = m - n })

{-# INLINE emitRootBuildM #-}
emitRootBuildM :: Term f -> BuildM s f () -> BuildM s f ()
emitRootBuildM t inner = emitSymbolBuildM (toSymbol (root t)) inner

{-# INLINE emitFunBuildM #-}
emitFunBuildM :: Fun f -> BuildM s f () -> BuildM s f ()
emitFunBuildM (MkFun f) inner = emitSymbolBuildM (Symbol True f 0) inner

{-# INLINE emitVarBuildM #-}
emitVarBuildM :: Var -> BuildM s f ()
emitVarBuildM (MkVar x) = emitSymbolBuildM (Symbol False x 1) (return ())

{-# INLINE emitTermListBuildM #-}
emitTermListBuildM :: TermList f -> BuildM s f ()
emitTermListBuildM (TermList lo hi array) = do
  marray <- getArray
  n <- getIndex
  let k = sizeOf (fromSymbol __)
  liftST $ copyByteArray marray (n*k) array (lo*k) ((hi-lo)*k)
  putIndex (n + hi-lo)

newtype CountM f a =
  CountM {
    unCountM :: Int# -> (# Int#, a #) }

{-# INLINE runCountM #-}
runCountM :: CountM f a -> Int
runCountM (CountM m) =
  case m 0# of
    (# n#, _ #) -> I# n#

instance Functor (CountM f) where
  {-# INLINE fmap #-}
  fmap f (CountM m) =
    CountM $ \i ->
      case m i of
        (# j, x #) -> (# j, f x #)

instance Applicative (CountM f) where
  pure  = return
  (<*>) = ap

instance Monad (CountM f) where
  {-# INLINE return #-}
  return x = CountM $ \i -> (# i, x #)
  {-# INLINE (>>=) #-}
  CountM m >>= f =
    CountM $ \i ->
      case m i of
        (# j, x #) -> unCountM (f x) j

instance Builder f (CountM f) where
  {-# INLINE emitRoot #-}
  emitRoot _ inner = do
    advance 1
    inner
  {-# INLINE emitFun #-}
  emitFun _ inner = do
    advance 1
    inner
  {-# INLINE emitVar #-}
  emitVar _ = advance 1
  {-# INLINE emitTermList #-}
  emitTermList t = advance (lenList t)

{-# INLINE advance #-}
advance :: Int -> CountM f ()
advance (I# n) = CountM $ \i -> (# i +# n, () #)

-- Construct a term, given a builder for it.
{-# INLINE buildTermList #-}
buildTermList :: (forall m. Builder f m => m ()) -> TermList f
buildTermList m =
  runST $ do
    let !size = runCountM m
    !marray <- newByteArray (size * sizeOf (fromSymbol __))
    !n <- runBuildM m marray
    !array <- unsafeFreezeByteArray marray
    return (TermList 0 n array)

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
    -- The backing terms
    terms :: {-# UNPACK #-} !ArrayArray,
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
    return (TermList lo hi (indexByteArrayArray terms x))

-- Mutable substitutions, used for building substitutions.
data MutableSubst s f =
  MutableSubst {
    mterms :: {-# UNPACK #-} !(MutableArrayArray s),
    mvars  :: {-# UNPACK #-} !Int,
    msubst :: {-# UNPACK #-} !(MutableByteArray s) }

-- Create an empty substitution, given the backing term
-- and the number of variables required.
{-# INLINE newMutableSubst #-}
newMutableSubst :: Int -> ST s (MutableSubst s f)
newMutableSubst vars = do
  terms <- newArrayArray vars
  subst <- newByteArray (vars * sizeOf (fromSlice __))
  setByteArray subst 0 vars (0 `asTypeOf` fromSlice __)
  return (MutableSubst terms vars subst)

-- Freeze a mutable substitution.
{-# INLINE unsafeFreezeSubst #-}
unsafeFreezeSubst :: MutableSubst s f -> ST s (Subst f)
unsafeFreezeSubst MutableSubst{..} = do
  terms <- unsafeFreezeArrayArray mterms
  subst <- unsafeFreezeByteArray msubst
  return (Subst terms mvars subst)

-- Look up a variable in a mutable substitution.
{-# INLINE mutableLookupList #-}
mutableLookupList :: MutableSubst s f -> Var -> ST s (Maybe (TermList f))
mutableLookupList MutableSubst{..} (MkVar x)
  | x >= mvars = return Nothing
  | otherwise = do
    slice <- readByteArray msubst x
    term <- readByteArrayArray mterms x
    return $ do
      (lo, hi) <- toSlice slice
      return (TermList lo hi term)

-- Add a new binding to a substitution.
-- Returns Just () on success or Nothing if an incompatible
-- binding already existed.
{-# INLINE extendList #-}
extendList :: MutableSubst s f -> Var -> TermList f -> ST s (Maybe ())
extendList MutableSubst{..} (MkVar x) (TermList lo hi arr)
  | x >= mvars = __
  | otherwise = do
    rng <- fmap toSlice (readByteArray msubst x)
    case rng of
      Nothing -> do
        writeByteArray msubst x (fromSlice (lo, hi))
        writeByteArrayArray mterms x arr
        return (Just ())
      Just (lo', hi') -> do
        arr' <- readByteArrayArray mterms x
        if TermList lo hi arr == TermList lo' hi' arr' then
          return (Just ())
        else
          return Nothing

-- Remove a binding from a substitution.
{-# INLINE retract #-}
retract :: MutableSubst s f -> Var -> ST s ()
retract MutableSubst{..} (MkVar x)
  | x >= mvars = __
  | otherwise = do
      writeByteArray msubst x (0 `asTypeOf` fromSlice __)
      writeMutableArrayArrayArray mterms x mterms

-- Add a new binding to a substitution.
-- Doesn't check bounds and overwrites any existing binding.
{-# INLINE unsafeExtendList #-}
unsafeExtendList :: MutableSubst s f -> Var -> TermList f -> ST s ()
unsafeExtendList MutableSubst{..} (MkVar x) (TermList lo hi arr) = do
  writeByteArray msubst x (fromSlice (lo, hi))
  writeByteArrayArray mterms x arr

-- Remove a binding from a substitution. Doesn't check bounds.
{-# INLINE unsafeRetract #-}
unsafeRetract :: MutableSubst s f -> Var -> ST s ()
unsafeRetract MutableSubst{..} (MkVar x) = do
  writeByteArray msubst x (0 `asTypeOf` fromSlice __)
  writeMutableArrayArrayArray mterms x mterms
