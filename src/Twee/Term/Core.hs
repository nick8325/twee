-- Terms and substitutions, implemented using flatterms.
-- This module contains all the low-level icky bits
-- and provides primitives for building higher-level stuff.
{-# LANGUAGE CPP, PatternSynonyms, ViewPatterns,
    MagicHash, UnboxedTuples, BangPatterns,
    RankNTypes, RecordWildCards, GeneralizedNewtypeDeriving #-}
module Twee.Term.Core where

#include "errors.h"
import Data.Primitive
import Control.Monad.ST.Strict
import Data.Bits
import Data.Int
import GHC.Types(Int(..))
import GHC.Prim
import GHC.ST hiding (liftST)
import Data.Ord
import Twee.Label
import Data.Typeable

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
    | isFun = show (F index) ++ "=" ++ show size
    | otherwise = show (V index)

-- Convert symbols to/from Int64 for storage in flatterms.
-- The encoding:
--   * bits 0-30: size
--   * bit  31: 0 (variable) or 1 (function)
--   * bits 32-63: index
{-# INLINE toSymbol #-}
toSymbol :: Int64 -> Symbol
toSymbol n =
  Symbol (testBit n 31)
    (fromIntegral (n `unsafeShiftR` 32))
    (fromIntegral (n .&. 0x7fffffff))

{-# INLINE fromSymbol #-}
fromSymbol :: Symbol -> Int64
fromSymbol Symbol{..} | index < 0 = ERROR("negative symbol index")
fromSymbol Symbol{..} =
  fromIntegral size +
  fromIntegral index `unsafeShiftL` 32 +
  fromIntegral (fromEnum isFun) `unsafeShiftL` 31

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
  | n < 0 || lo+n >= hi = ERROR("term index out of bounds")
  | otherwise =
    case TermList (lo+n) hi arr of
      UnsafeCons t _ -> t

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
    !x = indexByteArray array low
    Symbol{..} = toSymbol x

{-# INLINE patHead #-}
patHead :: TermList f -> Maybe (Term f, TermList f, TermList f)
patHead t@TermList{..}
  | low == high = Nothing
  | otherwise = unsafePatHead t

-- Pattern synonyms for single terms.
-- * Var :: Var -> Term f
-- * App :: Fun f -> TermList f -> Term f

newtype Fun f = F { fun_id :: Int }
instance Eq (Fun f) where
  f == g = fun_id f == fun_id g
instance Ord (Fun f) where
  compare = comparing fun_id

fun :: (Ord f, Typeable f) => f -> Fun f
fun f = F (labelNum (label f))

fun_value :: Fun f -> f
fun_value f = find (unsafeMkLabel (fun_id f))

newtype Var = V { var_id :: Int } deriving (Eq, Ord, Enum)
instance Show (Fun f) where show f = "f" ++ show (fun_id f)
instance Show Var     where show x = "x" ++ show (var_id x)

pattern Var x <- (patTerm -> Left x)
pattern App f ts <- (patTerm -> Right (f, ts))

{-# INLINE patTerm #-}
patTerm :: Term f -> Either Var (Fun f, TermList f)
patTerm t@Term{..}
  | isFun     = Right (F index, ts)
  | otherwise = Left (V index)
  where
    Symbol{..} = toSymbol root
    !(UnsafeConsSym _ ts) = singleton t

-- Convert a term to a termlist.
{-# INLINE singleton #-}
singleton :: Term f -> TermList f
singleton Term{..} = termlist

-- We can implement equality almost without access to the
-- internal representation of the termlists, but we cheat by
-- comparing Int64s instead of Symbols.
instance Eq (TermList f) where
  -- Manual worker-wrapper to prevent too much from being inlined.
  t == u = eqTermList t u

{-# INLINE eqTermList #-}
eqTermList :: TermList f -> TermList f -> Bool
eqTermList
  (TermList (I# low1) (I# high1) (ByteArray array1))
  (TermList (I# low2) (I# high2) (ByteArray array2)) =
    weqTermList low1 high1 array1 low2 high2 array2

{-# NOINLINE weqTermList #-}
weqTermList ::
  Int# -> Int# -> ByteArray# ->
  Int# -> Int# -> ByteArray# ->
  Bool
weqTermList low1 high1 array1 low2 high2 array2 =
  lenList t == lenList u && eqSameLength t u
  where
    t = TermList (I# low1) (I# high1) (ByteArray array1)
    u = TermList (I# low2) (I# high2) (ByteArray array2)
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
newtype Builder f =
  Builder {
    unBuilder ::
      -- Takes: the term array and size, and current position in the term.
      -- Returns the final position, which may be out of bounds.
      forall s. Builder1 s f }

type Builder1 s f = State# s -> MutableByteArray# s -> Int# -> Int# -> (# State# s, Int# #)

instance Monoid (Builder f) where
  {-# INLINE mempty #-}
  mempty = Builder built
  {-# INLINE mappend #-}
  Builder m1 `mappend` Builder m2 = Builder (m1 `then_` m2)

{-# INLINE buildTermList #-}
buildTermList :: Builder f -> TermList f
buildTermList builder = runST $ do
  let
    Builder m = builder
    loop n@(I# n#) = do
      MutableByteArray mbytearray# <-
        newByteArray (n * sizeOf (fromSymbol __))
      n' <-
        ST $ \s ->
          case m s mbytearray# n# 0# of
            (# s, n# #) -> (# s, I# n# #)
      if n' <= n then do
        !bytearray <- unsafeFreezeByteArray (MutableByteArray mbytearray#)
        return (TermList 0 n' bytearray)
       else loop (n'*2)
  loop 32

{-# INLINE getByteArray #-}
getByteArray :: (MutableByteArray s -> Builder1 s f) -> Builder1 s f
getByteArray k = \s bytearray n i -> k (MutableByteArray bytearray) s bytearray n i

{-# INLINE getSize #-}
getSize :: (Int -> Builder1 s f) -> Builder1 s f
getSize k = \s bytearray n i -> k (I# n) s bytearray n i

{-# INLINE getIndex #-}
getIndex :: (Int -> Builder1 s f) -> Builder1 s f
getIndex k = \s bytearray n i -> k (I# i) s bytearray n i

{-# INLINE putIndex #-}
putIndex :: Int -> Builder1 s f
putIndex (I# i) = \s _ _ _ -> (# s, i #)

{-# INLINE liftST #-}
liftST :: ST s () -> Builder1 s f
liftST (ST m) =
  \s _ _ i ->
  case m s of
    (# s, () #) -> (# s, i #)

{-# INLINE built #-}
built :: Builder1 s f
built = \s _ _ i -> (# s, i #)

{-# INLINE then_ #-}
then_ :: Builder1 s f -> Builder1 s f -> Builder1 s f
then_ m1 m2 =
  \s bytearray n i ->
    case m1 s bytearray n i of
      (# s, i #) -> m2 s bytearray n i

{-# INLINE checked #-}
checked :: Int -> Builder1 s f -> Builder1 s f
checked j m =
  getSize $ \n ->
  getIndex $ \i ->
  if i + j <= n then m else putIndex (i + j)

{-# INLINE emitSymbolBuilder #-}
emitSymbolBuilder :: Symbol -> Builder f -> Builder f
emitSymbolBuilder x inner =
  Builder $ checked 1 $
    getByteArray $ \bytearray ->
    getIndex $ \n ->
    putIndex (n+1) `then_`
    unBuilder inner `then_`
    getIndex (\m ->
      liftST $ writeByteArray bytearray n (fromSymbol x { size = m - n }))

-- Emit a function application.
{-# INLINE emitApp #-}
emitApp :: Fun f -> Builder f -> Builder f
emitApp (F n) inner = emitSymbolBuilder (Symbol True n 0) inner

-- Emit a variable.
{-# INLINE emitVar #-}
emitVar :: Var -> Builder f
emitVar x = emitSymbolBuilder (Symbol False (var_id x) 1) mempty

-- Emit a whole termlist.
{-# INLINE emitTermList #-}
emitTermList :: TermList f -> Builder f
emitTermList (TermList lo hi array) =
  Builder $ checked (hi-lo) $
    getByteArray $ \mbytearray ->
    getIndex $ \n ->
    let k = sizeOf (fromSymbol __) in
    liftST (copyByteArray mbytearray (n*k) array (lo*k) ((hi-lo)*k)) `then_`
    putIndex (n + hi-lo)
