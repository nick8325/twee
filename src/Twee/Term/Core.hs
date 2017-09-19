-- Terms and substitutions, implemented using flatterms.
-- This module contains all the low-level icky bits
-- and provides primitives for building higher-level stuff.
{-# LANGUAGE CPP, PatternSynonyms, ViewPatterns,
    MagicHash, UnboxedTuples, BangPatterns,
    RankNTypes, RecordWildCards, GeneralizedNewtypeDeriving #-}
module Twee.Term.Core where

import Data.Primitive(sizeOf)
#ifdef BOUNDS_CHECKS
import Data.Primitive.ByteArray.Checked
#else
import Data.Primitive.ByteArray
#endif
import Control.Monad.ST.Strict
import Data.Bits
import Data.Int
import GHC.Int(Int(..))
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
fromSymbol Symbol{..} =
  fromIntegral size +
  fromIntegral index `unsafeShiftL` 32 +
  fromIntegral (fromEnum isFun) `unsafeShiftL` 31

--------------------------------------------------------------------------------
-- Flatterms, or rather lists of terms.
--------------------------------------------------------------------------------

-- | @'TermList' f@ is a list of terms whose function symbols have type @f@.
-- It is either a 'Cons' or an 'Empty'. You can turn it into a @['Term' f]@
-- with 'Twee.Term.unpack'.

-- A TermList is a slice of an unboxed array of symbols.
data TermList f =
  TermList {
    low   :: {-# UNPACK #-} !Int,
    high  :: {-# UNPACK #-} !Int,
    array :: {-# UNPACK #-} !ByteArray }

-- | Index into a termlist.
at :: Int -> TermList f -> Term f
at n (TermList lo hi arr)
  | n < 0 || lo+n >= hi = error "term index out of bounds"
  | otherwise =
    case TermList (lo+n) hi arr of
      UnsafeCons t _ -> t

{-# INLINE lenList #-}
-- | The length of (number of symbols in) a termlist.
lenList :: TermList f -> Int
lenList (TermList low high _) = high - low

-- | @'Term' f@ is a term whose function symbols have type @f@.
-- It is either a 'Var' or an 'App'.

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

-- | Matches the empty termlist.
pattern Empty :: TermList f
pattern Empty <- (patHead -> Nothing)

-- | Matches a non-empty termlist, unpacking it into head and tail.
pattern Cons :: Term f -> TermList f -> TermList f
pattern Cons t ts <- (patHead -> Just (t, _, ts))

-- | Like 'Cons', but does not check that the termlist is non-empty. Use only if
-- you are sure the termlist is non-empty.
pattern UnsafeCons :: Term f -> TermList f -> TermList f
pattern UnsafeCons t ts <- (unsafePatHead -> Just (t, _, ts))

-- | Matches a non-empty termlist, unpacking it into head and
-- /everything except the root symbol of the head/.
-- Useful for iterating through terms one symbol at a time.
--
-- For example, if @ts@ is the termlist @[f(x,y), g(z)]@,
-- then @let ConsSym u us = ts@ results in the following bindings:
--
-- > u  = f(x,y)
-- > us = [x, y, g(z)]
pattern ConsSym :: Term f -> TermList f -> TermList f
pattern ConsSym t ts <- (patHead -> Just (t, ts, _))

-- | Like 'ConsSym', but does not check that the termlist is non-empty. Use only
-- if you are sure the termlist is non-empty.
pattern UnsafeConsSym :: Term f -> TermList f -> TermList f
pattern UnsafeConsSym t ts <- (unsafePatHead -> Just (t, ts, _))

-- A helper for UnsafeCons/UnsafeConsSym.
{-# INLINE unsafePatHead #-}
unsafePatHead :: TermList f -> Maybe (Term f, TermList f, TermList f)
unsafePatHead TermList{..} =
  Just (Term x (TermList low (low+size) array),
        TermList (low+1) high array,
        TermList (low+size) high array)
  where
    !x = indexByteArray array low
    Symbol{..} = toSymbol x

-- A helper for Cons/ConsSym.
{-# INLINE patHead #-}
patHead :: TermList f -> Maybe (Term f, TermList f, TermList f)
patHead t@TermList{..}
  | low == high = Nothing
  | otherwise = unsafePatHead t

-- Pattern synonyms for single terms.
-- * Var :: Var -> Term f
-- * App :: Fun f -> TermList f -> Term f

-- | A function symbol. @f@ is the underlying type of function symbols defined
-- by the user; @'Fun' f@ is an @f@ together with an automatically-generated unique number.
newtype Fun f =
  F {
    -- | The unique number of a 'Fun'.
    fun_id :: Int }
instance Eq (Fun f) where
  f == g = fun_id f == fun_id g
instance Ord (Fun f) where
  compare = comparing fun_id

-- | Construct a 'Fun' from a function symbol.
fun :: (Ord f, Typeable f) => f -> Fun f
fun f = F (fromIntegral (labelNum (label f)))

-- | The underlying function symbol of a 'Fun'.
fun_value :: Fun f -> f
fun_value f = find (unsafeMkLabel (fromIntegral (fun_id f)))

-- | A variable.
newtype Var =
  V {
    -- | The variable's number.
    -- Must be non-negative; this is not currently checked!
    var_id :: Int } deriving (Eq, Ord, Enum)
instance Show (Fun f) where show f = "f" ++ show (fun_id f)
instance Show Var     where show x = "x" ++ show (var_id x)

-- | Matches a variable.
pattern Var :: Var -> Term f
pattern Var x <- (patTerm -> Left x)

-- | Matches a function application.
pattern App :: Fun f -> TermList f -> Term f
pattern App f ts <- (patTerm -> Right (f, ts))

-- A helper function for Var and App.
{-# INLINE patTerm #-}
patTerm :: Term f -> Either Var (Fun f, TermList f)
patTerm t@Term{..}
  | isFun     = Right (F index, ts)
  | otherwise = Left (V index)
  where
    Symbol{..} = toSymbol root
    !(UnsafeConsSym _ ts) = singleton t

-- | Convert a term to a termlist.
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

-- Manually worker-wrapper transform the thing, ugh...
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
-- Building terms.
--------------------------------------------------------------------------------

-- | A monoid for building terms.
-- 'mempty' represents the empty termlist, while 'mappend' appends two termlists.
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

-- Build a termlist from a Builder.
-- Works by guessing an appropriate size, and retrying if that was too small.
{-# INLINE buildTermList #-}
buildTermList :: Builder f -> TermList f
buildTermList builder = runST $ do
  let
    Builder m = builder
    loop n@(I# n#) = do
      MutableByteArray mbytearray# <-
        newByteArray (n * sizeOf (fromSymbol undefined))
      n' <-
        ST $ \s ->
          case m s mbytearray# n# 0# of
            (# s, n# #) -> (# s, I# n# #)
      if n' <= n then do
        !bytearray <- unsafeFreezeByteArray (MutableByteArray mbytearray#)
        return (TermList 0 n' bytearray)
       else loop (n'*2)
  loop 32

-- Get at the term array.
{-# INLINE getByteArray #-}
getByteArray :: (MutableByteArray s -> Builder1 s f) -> Builder1 s f
getByteArray k = \s bytearray n i -> k (MutableByteArray bytearray) s bytearray n i

-- Get at the array size.
{-# INLINE getSize #-}
getSize :: (Int -> Builder1 s f) -> Builder1 s f
getSize k = \s bytearray n i -> k (I# n) s bytearray n i

-- Get at the current array index.
{-# INLINE getIndex #-}
getIndex :: (Int -> Builder1 s f) -> Builder1 s f
getIndex k = \s bytearray n i -> k (I# i) s bytearray n i

-- Change the current array index.
{-# INLINE putIndex #-}
putIndex :: Int -> Builder1 s f
putIndex (I# i) = \s _ _ _ -> (# s, i #)

-- Lift an ST computation into a builder.
{-# INLINE liftST #-}
liftST :: ST s () -> Builder1 s f
liftST (ST m) =
  \s _ _ i ->
  case m s of
    (# s, () #) -> (# s, i #)

-- Finish building.
{-# INLINE built #-}
built :: Builder1 s f
built = \s _ _ i -> (# s, i #)

-- Sequence two builder operations.
{-# INLINE then_ #-}
then_ :: Builder1 s f -> Builder1 s f -> Builder1 s f
then_ m1 m2 =
  \s bytearray n i ->
    case m1 s bytearray n i of
      (# s, i #) -> m2 s bytearray n i

-- checked j m executes m only if the array has room for j more symbols.
{-# INLINE checked #-}
checked :: Int -> Builder1 s f -> Builder1 s f
checked j m =
  getSize $ \n ->
  getIndex $ \i ->
  if i + j <= n then m else putIndex (i + j)

-- Emit an arbitrary symbol, with given arguments.
{-# INLINE emitSymbolBuilder #-}
emitSymbolBuilder :: Symbol -> Builder f -> Builder f
emitSymbolBuilder x inner =
  Builder $ checked 1 $
    getByteArray $ \bytearray ->
    -- Skip the symbol itself, then fill it in at the end, when we know the size
    -- of the symbol's arguments.
    getIndex $ \n ->
    putIndex (n+1) `then_`
    unBuilder inner `then_`
    -- Fill in the symbol.
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
    let k = sizeOf (fromSymbol undefined) in
    liftST (copyByteArray mbytearray (n*k) array (lo*k) ((hi-lo)*k)) `then_`
    putIndex (n + hi-lo)

----------------------------------------------------------------------
-- Efficient subterm testing.
----------------------------------------------------------------------

-- | Is a term contained as a subterm in a given termlist?
{-# INLINE isSubtermOfList #-}
isSubtermOfList :: Term f -> TermList f -> Bool
isSubtermOfList t u =
  isSubArrayOf (singleton t) u

-- N.B. this one should not be exported from Twee.Term
-- because subarray is not the same as subterm if t is not
-- a singleton
isSubArrayOf :: TermList f -> TermList f -> Bool
isSubArrayOf t u =
  lenList t <= lenList u && (here t u || next t u)
  where
    here Empty _ = True
    here (ConsSym s1 t) (UnsafeConsSym s2 u) =
      root s1 == root s2 && here t u

    -- This is safe because lenList t <= lenList u
    -- so if u = Empty, then t = Empty and here t u = True.
    next t (UnsafeConsSym _ u) = isSubArrayOf t u

-- | Check if a variable occurs in a termlist.
{-# INLINE occursList #-}
occursList :: Var -> TermList f -> Bool
occursList (V x) t = symbolOccursList (fromSymbol (Symbol False x 1)) t

symbolOccursList :: Int64 -> TermList f -> Bool
symbolOccursList !_ Empty = False
symbolOccursList n (ConsSym t ts) = root t == n || symbolOccursList n ts
