-- Terms and substitutions, implemented using flatterms.
-- This module contains all the low-level icky bits
-- and provides primitives for building higher-level stuff.
{-# LANGUAGE BangPatterns, CPP, PatternGuards, PatternSynonyms, ViewPatterns, RecordWildCards, GeneralizedNewtypeDeriving, RankNTypes, MagicHash, UnboxedTuples, MultiParamTypeClasses, FlexibleInstances, FunctionalDependencies, ScopedTypeVariables #-}
module Twee.Term.Core where

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
import Data.Ord

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

at :: Int -> TermList f -> Term f
at n (TermList lo hi arr)
  | n < 0 || n + lo >= hi = ERROR("term index out of bounds")
  | otherwise =
    case TermList (lo+n) hi arr of
      Cons t _ -> t

{-# INLINE lenList #-}
-- The length (number of symbols in) a flatterm.
lenList :: TermList f -> Int
lenList (TermList low high _) = high - low

-- A term is a special case of a termlist.
-- We store it as the termlist together with the root symbol.
data Term f =
  Term {
    root     :: {-# UNPACK #-} !Int64,
    termlist :: {-# UNPACK #-} !(TermList f) }

instance Eq (Term f) where
  x == y = termlist x == termlist y

instance Ord (Term f) where
  compare = comparing termlist

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
newtype Fun f = MkFun Int deriving Eq
newtype Var   = MkVar Int deriving (Eq, Ord, Enum)
instance Show (Fun f) where show (MkFun x) = "f" ++ show x
instance Show Var     where show (MkVar x) = "x" ++ show x

class OrdFun f where compareFun :: Fun f -> Fun f -> Ordering
instance OrdFun f => Ord (Fun f) where compare = compareFun

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

instance Ord (TermList f) where
  {-# INLINE compare #-}
  compare t u =
    case compare (lenList t) (lenList u) of
      EQ -> compareContents t u
      x  -> x

compareContents :: TermList f -> TermList f -> Ordering
compareContents Empty !_ = EQ
compareContents (ConsSym s1 t) (UnsafeConsSym s2 u) =
  case compare (root s1) (root s2) of
    EQ -> compareContents t u
    x  -> x

--------------------------------------------------------------------------------
-- Building terms imperatively.
--------------------------------------------------------------------------------

-- A monad for building terms.
newtype BuildM s f a =
  BuildM {
    unBuildM ::
      -- Takes: the term array and size, and current position in the term.
      -- Returns the final position, which may be out of bounds.
      State# s -> MutableByteArray# s -> Int# -> Int# -> (# State# s, Int#, a #) }

instance Functor (BuildM s f) where
  {-# INLINE fmap #-}
  fmap f (BuildM m) =
    BuildM $ \s array n i ->
      case m s array n i of
        (# s, j, x #) -> (# s, j, f x #)

instance Applicative (BuildM s f) where
  pure = return
  (<*>) = ap

instance Monad (BuildM s f) where
  {-# INLINE return #-}
  return x = BuildM (\s _ _ i -> (# s, i, x #))
  {-# INLINE (>>=) #-}
  BuildM m >>= f =
    BuildM $ \s array n i ->
      case m s array n i of
        (# s, j, x #) -> unBuildM (f x) s array n j

{-# INLINE buildTermList #-}
buildTermList :: Int -> (forall s. BuildM s f ()) -> TermList f
buildTermList n0 builder = runST $ do
  let
    BuildM m = builder
    loop n@(I# n#) = do
      MutableByteArray marray# <-
        newByteArray (n * sizeOf (fromSymbol __))
      n' <-
        ST $ \s ->
          case m s marray# n# 0# of
            (# s, n#, _ #) -> (# s, I# n# #)
      if n' <= n then do
        !array <- unsafeFreezeByteArray (MutableByteArray marray#)
        return (TermList 0 n' array)
       else loop (n'*2)
  loop n0

{-# INLINE getArray #-}
getArray :: BuildM s f (MutableByteArray s)
getArray = BuildM $ \s array _ i -> (# s, i, MutableByteArray array #)

{-# INLINE getSize #-}
getSize :: BuildM s f Int
getSize = BuildM $ \s _ n i -> (# s, i, I# n #)

{-# INLINE getIndex #-}
getIndex :: BuildM s f Int
getIndex = BuildM $ \s _ _ i -> (# s, i, I# i #)

{-# INLINE putIndex #-}
putIndex :: Int -> BuildM s f ()
putIndex (I# i) = BuildM $ \s _ _ _ -> (# s, i, () #)

{-# INLINE liftST #-}
liftST :: ST s a -> BuildM s f a
liftST (ST m) =
  BuildM $ \s _ _ i ->
  case m s of
    (# s, x #) -> (# s, i, x #)

{-# INLINE checked #-}
checked :: Int -> BuildM s f () -> BuildM s f ()
checked j m = do
  n <- getSize
  i <- getIndex
  if i + j <= n then m else putIndex (i + j)

{-# INLINE emitSymbolBuildM #-}
emitSymbolBuildM :: Symbol -> BuildM s f () -> BuildM s f ()
emitSymbolBuildM x inner = checked 1 $ do
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
emitRoot t inner = emitSymbolBuildM (toSymbol (root t)) inner

-- Emit a function symbol.
-- The second argument is called to emit the function's arguments.
{-# INLINE emitFun #-}
emitFun :: Fun f -> BuildM s f () -> BuildM s f ()
emitFun (MkFun f) inner = emitSymbolBuildM (Symbol True f 0) inner

-- Emit a variable.
{-# INLINE emitVar #-}
emitVar :: Var -> BuildM s f ()
emitVar (MkVar x) = emitSymbolBuildM (Symbol False x 1) (return ())

-- Emit a whole termlist.
{-# INLINE emitTermList #-}
emitTermList :: TermList f -> BuildM s f ()
emitTermList (TermList lo hi array) = checked (hi-lo) $ do
  marray <- getArray
  n <- getIndex
  let k = sizeOf (fromSymbol __)
  liftST $ copyByteArray marray (n*k) array (lo*k) ((hi-lo)*k)
  putIndex (n + hi-lo)

--------------------------------------------------------------------------------
-- Substitutions.
--------------------------------------------------------------------------------

-- A substitution is an array of terms, where term number i is the
-- term bound to variable i, or the empty termlist if the variable
-- is unbound. For efficiency we unpack this array into two components:
-- * An ArrayArray containing the ByteArray for each term
-- * A ByteArray containing the (lo, hi) indices for each term
data Subst f =
  Subst {
    -- The number of variables in the term array.
    vars  :: {-# UNPACK #-} !Int,
    -- The ByteArray for each term in the substitution.
    terms :: {-# UNPACK #-} !ArrayArray,
    -- The (lo, hi) pair for each term in the substitution.
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
    mvars  :: {-# UNPACK #-} !Int,
    mterms :: {-# UNPACK #-} !(MutableArrayArray s),
    msubst :: {-# UNPACK #-} !(MutableByteArray s) }

-- Create an empty substitution, given the backing term
-- and the number of variables required.
{-# INLINE newMutableSubst #-}
newMutableSubst :: Int -> ST s (MutableSubst s f)
newMutableSubst vars = do
  terms <- newArrayArray vars
  subst <- newByteArray (vars * sizeOf (fromSlice __))
  setByteArray subst 0 vars (0 `asTypeOf` fromSlice __)
  return (MutableSubst vars terms subst)

-- Freeze a mutable substitution.
{-# INLINE unsafeFreezeSubst #-}
unsafeFreezeSubst :: MutableSubst s f -> ST s (Subst f)
unsafeFreezeSubst MutableSubst{..} = do
  terms <- unsafeFreezeArrayArray mterms
  subst <- unsafeFreezeByteArray msubst
  return (Subst mvars terms subst)

-- Copy a mutable substitution.
{-# INLINE copySubst #-}
copySubst :: MutableSubst s f -> ST s (MutableSubst s f)
copySubst MutableSubst{..} = do
  terms <- newArrayArray mvars
  subst <- newByteArray (mvars * sizeOf (fromSlice __))
  copyMutableByteArray subst 0 msubst 0 (mvars * sizeOf (fromSlice __))
  copyMutableArrayArray terms 0 mterms 0 mvars
  return (MutableSubst mvars terms subst)

-- Freeze a mutable substitution, making a copy.
{-# INLINE freezeSubst #-}
freezeSubst :: MutableSubst s f -> ST s (Subst f)
freezeSubst msub = copySubst msub >>= unsafeFreezeSubst

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
