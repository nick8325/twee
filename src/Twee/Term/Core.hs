-- Terms and substitutions, implemented using flatterms.
-- This module contains all the low-level icky bits
-- and provides primitives for building higher-level stuff.
{-# LANGUAGE CPP, PatternSynonyms, ViewPatterns,
    MagicHash, UnboxedTuples, BangPatterns,
    RankNTypes, RecordWildCards, GeneralizedNewtypeDeriving #-}
module Twee.Term.Core where

#include "errors.h"
import Data.Primitive
import Data.Primitive.SmallArray
import Control.Monad.ST.Strict
import Data.Bits
import Data.Int
import GHC.Types(Int(..))
import GHC.Prim
import GHC.ST hiding (liftST)
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
    | isFun = show (F index ()) ++ "=" ++ show size
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
    array :: {-# UNPACK #-} !ByteArray,
    funs  :: {-# UNPACK #-} !(SmallArray f) }

at :: Int -> TermList f -> Term f
at n (TermList lo hi arr funs)
  | n < 0 || n + lo >= hi = ERROR("term index out of bounds")
  | otherwise =
    case TermList (lo+n) hi arr funs of
      Cons t _ -> t

{-# INLINE lenList #-}
-- The length (number of symbols in) a flatterm.
lenList :: TermList f -> Int
lenList (TermList low high _ _) = high - low

-- A term is a special case of a termlist.
-- We store it as the termlist together with the root symbol.
data Term f =
  Term {
    root     :: {-# UNPACK #-} !Int64,
    rootFun  :: f,
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
  Just (Term x f (TermList low (low+size) array funs),
        TermList (low+1) high array funs,
        TermList (low+size) high array funs)
  where
    !x = indexByteArray array low
    f  = indexSmallArray funs low
    Symbol{..} = toSymbol x

{-# INLINE patHead #-}
patHead :: TermList f -> Maybe (Term f, TermList f, TermList f)
patHead t@TermList{..}
  | low == high = Nothing
  | otherwise = unsafePatHead t

-- Pattern synonyms for single terms.
-- * Var :: Var -> Term f
-- * Fun :: Fun f -> TermList f -> Term f

data Fun f = F { fun_id :: {- UNPACK #-} !Int, fun_value :: !f }
instance Eq (Fun f) where
  f == g = fun_id f == fun_id g
instance Ord (Fun f) where
  compare = comparing fun_id

newtype Var = V { var_id :: Int } deriving (Eq, Ord, Enum)
instance Show (Fun f) where show f = "f" ++ show (fun_id f)
instance Show Var     where show x = "x" ++ show (var_id x)

pattern Var x <- (patTerm -> Left x)
pattern Fun f ts <- (patTerm -> Right (f, ts))

{-# INLINE patTerm #-}
patTerm :: Term f -> Either Var (Fun f, TermList f)
patTerm t@Term{..}
  | isFun     = Right (F index rootFun, ts)
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
newtype Builder f =
  Builder {
    unBuilder ::
      -- Takes: the term array and size, and current position in the term.
      -- Returns the final position, which may be out of bounds.
      forall s. Builder1 s f }

type Builder1 s f = State# s -> MutableByteArray# s -> SmallMutableArray# s f -> Int# -> Int# -> (# State# s, Int# #)

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
      SmallMutableArray marray# <- newSmallArray n __
      n' <-
        ST $ \s ->
          case m s mbytearray# marray# n# 0# of
            (# s, n# #) -> (# s, I# n# #)
      if n' <= n then do
        !bytearray <- unsafeFreezeByteArray (MutableByteArray mbytearray#)
        !array <- unsafeFreezeSmallArray (SmallMutableArray marray#)
        return (TermList 0 n' bytearray array)
       else loop (n'*2)
  loop 32

{-# INLINE getByteArray #-}
getByteArray :: (MutableByteArray s -> Builder1 s f) -> Builder1 s f
getByteArray k = \s bytearray array n i -> k (MutableByteArray bytearray) s bytearray array n i

{-# INLINE getArray #-}
getArray :: (SmallMutableArray s f -> Builder1 s f) -> Builder1 s f
getArray k = \s bytearray array n i -> k (SmallMutableArray array) s bytearray array n i

{-# INLINE getSize #-}
getSize :: (Int -> Builder1 s f) -> Builder1 s f
getSize k = \s bytearray array n i -> k (I# n) s bytearray array n i

{-# INLINE getIndex #-}
getIndex :: (Int -> Builder1 s f) -> Builder1 s f
getIndex k = \s bytearray array n i -> k (I# i) s bytearray array n i

{-# INLINE putIndex #-}
putIndex :: Int -> Builder1 s f
putIndex (I# i) = \s _ _ _ _ -> (# s, i #)

{-# INLINE liftST #-}
liftST :: ST s () -> Builder1 s f
liftST (ST m) =
  \s _ _ _ i ->
  case m s of
    (# s, () #) -> (# s, i #)

{-# INLINE built #-}
built :: Builder1 s f
built = \s _ _ _ i -> (# s, i #)

{-# INLINE then_ #-}
then_ :: Builder1 s f -> Builder1 s f -> Builder1 s f
then_ m1 m2 =
  \s bytearray array n i ->
    case m1 s bytearray array n i of
      (# s, i #) -> m2 s bytearray array n i

{-# INLINE checked #-}
checked :: Int -> Builder1 s f -> Builder1 s f
checked j m =
  getSize $ \n ->
  getIndex $ \i ->
  if i + j <= n then m else putIndex (i + j)

{-# INLINE emitSymbolBuilder #-}
emitSymbolBuilder :: (Int -> Builder f) -> Symbol -> Builder f -> Builder f
emitSymbolBuilder aux x inner =
  Builder $ checked 1 $
    getByteArray $ \bytearray ->
    getIndex $ \n ->
    unBuilder (aux n) `then_`
    putIndex (n+1) `then_`
    unBuilder inner `then_`
    getIndex (\m ->
      liftST $ writeByteArray bytearray n (fromSymbol x { size = m - n }))

-- Emit a function symbol.
-- The second argument is called to emit the function's arguments.
{-# INLINE emitFun #-}
emitFun :: Fun f -> Builder f -> Builder f
emitFun (F n f) inner = emitSymbolBuilder aux (Symbol True n 0) inner
  where
    aux n =
      Builder $
        getArray $ \array ->
        liftST $ writeSmallArray array n f

-- Emit a variable.
{-# INLINE emitVar #-}
emitVar :: Var -> Builder f
emitVar x = emitSymbolBuilder (\_ -> Builder built) (Symbol False (var_id x) 1) mempty

-- Emit a whole termlist.
{-# INLINE emitTermList #-}
emitTermList :: TermList f -> Builder f
emitTermList (TermList lo hi array funs) =
  Builder $ checked (hi-lo) $
    getByteArray $ \mbytearray ->
    getArray $ \marray ->
    getIndex $ \n ->
    let k = sizeOf (fromSymbol __) in
    liftST (copyByteArray mbytearray (n*k) array (lo*k) ((hi-lo)*k)) `then_`
    liftST (copySmallArray funs lo marray n (hi-lo)) `then_`
    putIndex (n + hi-lo)
