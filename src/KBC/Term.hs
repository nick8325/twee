{-# LANGUAGE BangPatterns, CPP, PatternGuards, PatternSynonyms, ViewPatterns, RecordWildCards, GeneralizedNewtypeDeriving, RankNTypes, MagicHash, UnboxedTuples #-}
module KBC.Term where

#include "errors.h"
import Data.Primitive
import Control.Monad
import Control.Monad.ST.Strict
import Data.Bits
import Data.Int
import Data.Word
import Data.List
import GHC.Types
import GHC.Prim
import GHC.ST hiding (liftST)

newtype Fun f = MkFun Int deriving (Eq, Ord)
newtype Var   = MkVar Int deriving (Eq, Ord, Enum)

data Symbol =
  Symbol {
    isFun :: Bool,
    index :: Int,
    size  :: Int }
instance Show Symbol where
  show Symbol{..}
    | isFun = "f" ++ show index ++ "=" ++ show size
    | otherwise = "x" ++ show index

{-# INLINE toSymbol #-}
toSymbol :: Int64 -> Symbol
toSymbol n =
  Symbol (n < 0)
    (if n < 0 then
       negate (fromIntegral n `unsafeShiftR` 32)
     else
       fromIntegral n `unsafeShiftR` 32)
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

data Term f =
  Term {
    root     :: {-# UNPACK #-} !Int64,
    children :: {-# UNPACK #-} !(TermList f) }
  deriving Eq

instance Show (Term f) where
  show = show . singleton

data TermList f =
  TermList {
    low   :: {-# UNPACK #-} !Int,
    high  :: {-# UNPACK #-} !Int,
    array :: {-# UNPACK #-} !ByteArray }

instance Show (TermList f) where
  show (TermList lo hi arr) =
    "<" ++ show lo ++ "," ++ show hi ++ ">[" ++
      intercalate "," [show (toSymbol (indexByteArray arr n)) | n <- [lo..hi-1]] ++ "]"

{-# INLINE nsymbols #-}
nsymbols :: TermList f -> Int
nsymbols (TermList low high _) = high - low

instance Eq (TermList f) where
  {-# INLINE (==) #-}
  t == u = nsymbols t == nsymbols u && eqSameLength t u

eqSameLength :: TermList f -> TermList f -> Bool
eqSameLength Empty !_ = True
eqSameLength (ConsSym s1 t) (UnsafeConsSym s2 u) =
  root s1 == root s2 && eqSameLength t u

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

pattern Empty <- (patHead -> Nothing)
pattern Cons t ts <- (patHead -> Just (t, _, ts))
pattern ConsSym t ts <- (patHead -> Just (t, ts, _))
pattern UnsafeCons t ts <- (unsafePatHead -> Just (t, _, ts))
pattern UnsafeConsSym t ts <- (unsafePatHead -> Just (t, ts, _))

{-# INLINE patRoot #-}
patRoot :: Int64 -> Either Var (Fun f)
patRoot root
  | isFun     = Right (MkFun index)
  | otherwise = Left (MkVar index)
  where
    Symbol{..} = toSymbol root

pattern Var x <- Term (patRoot -> Left x) _
pattern Fun f ts <- Term (patRoot -> Right f) ts

{-# INLINE singleton #-}
singleton :: Term f -> TermList f
singleton Term{children = TermList{..}} =
  TermList low high array

data Subst f =
  Subst {
    term  :: {-# UNPACK #-} !ByteArray,
    vars  :: {-# UNPACK #-} !Int,
    subst :: {-# UNPACK #-} !ByteArray }

toSubst :: Subst f -> [(Int, Term f)]
toSubst (Subst arr n sub) =
  [(i, t)
  | i <- [0..n-1],
    Just (lo, hi) <- [toRange (indexByteArray sub i)],
    let Cons t Empty = TermList lo hi arr]

instance Show (Subst f) where
  show = show . toSubst

data MSubst s f =
  MSubst {
    mterm  :: {-# UNPACK #-} !ByteArray,
    mvars  :: {-# UNPACK #-} !Int,
    msubst :: {-# UNPACK #-} !(MutableByteArray s) }

{-# INLINE toRange #-}
toRange :: Word64 -> Maybe (Int, Int)
toRange 0 = Nothing
toRange n = Just (fromIntegral n .&. 0xffffffff, fromIntegral (n `unsafeShiftR` 32))

{-# INLINE fromRange #-}
fromRange :: (Int, Int) -> Word64
fromRange (lo, hi) =
  fromIntegral lo .&. 0xffffffff +
  fromIntegral hi `unsafeShiftL` 32

-- Note to self: have KBC.Term.Unsafe which exports raw versions of functions,
-- KBC.Term which exports checked versions.
{-# INLINE extend #-}
extend :: MSubst s f -> Var -> Term f -> ST s (Maybe ())
extend MSubst{..} (MkVar x) t = do
  let TermList lo hi _ = singleton t
  rng <- fmap toRange (readByteArray msubst x)
  case rng of
    Nothing -> do
      writeByteArray msubst x (fromRange (lo, hi))
      return (Just ())
    Just (lo', hi')
      | TermList lo hi mterm == TermList lo' hi' mterm ->
        return (Just ())
      | otherwise ->
        return Nothing

{-# INLINE freezeSubst #-}
freezeSubst :: MSubst s f -> ST s (Subst f)
freezeSubst MSubst{..} = do
  subst <- unsafeFreezeByteArray msubst
  return (Subst mterm mvars subst)

{-# INLINE newMSubst #-}
newMSubst :: TermList f -> Int -> ST s (MSubst s f)
newMSubst TermList{..} vars = do
  subst <- newByteArray (vars * sizeOf (fromRange __))
  return (MSubst array vars subst)

{-# INLINE bound #-}
bound :: TermList f -> Int
bound t = aux 0 t
  where
    aux n Empty = n
    aux n (ConsSym Fun{} t) = aux n t
    aux n (ConsSym (Var (MkVar x)) t)
      | x >= n = aux (x+1) t
      | otherwise = aux n t

match :: Term f -> Term f -> Maybe (Subst f)
match pat t = matchTerms (singleton pat) (singleton t)

matchTerms :: TermList f -> TermList f -> Maybe (Subst f)
matchTerms !pat !t = runST $ do
  subst <- newMSubst t (bound pat)
  let loop !_ !_ | False = __
      loop Empty _ = fmap Just (freezeSubst subst)
      loop _ Empty = __
      loop (ConsSym (Fun f _) pat) (ConsSym (Fun g _) t)
        | f == g = loop pat t
      loop (ConsSym (Var x) pat) (Cons t u) = do
        res <- extend subst x t
        case res of
          Nothing -> return Nothing
          Just () -> loop pat u
      loop _ _ = return Nothing
  loop pat t

newtype BuildTermListM s f a =
  BuildM {
    unBuildM ::
      MutableByteArray# s -> Int# -> State# s -> (# State# s, Int#, a #) }

instance Functor (BuildTermListM s f) where
  {-# INLINE fmap #-}
  fmap f (BuildM m) =
    BuildM $ \array i s ->
      case m array i s of
        (# s, j, x #) -> (# s, j, f x #)
instance Applicative (BuildTermListM s f) where
  pure = return
  (<*>) = ap
instance Monad (BuildTermListM s f) where
  {-# INLINE return #-}
  return x = BuildM (\_ i s -> (# s, i, x #))
  {-# INLINE (>>=) #-}
  BuildM m >>= f =
    BuildM $ \array i s ->
      case m array i s of
        (# s, j, x #) -> unBuildM (f x) array j s

{-# INLINE getArray #-}
getArray :: BuildTermListM s f (MutableByteArray s)
getArray = BuildM $ \array n s -> (# s, n, MutableByteArray array #)

{-# INLINE getIndex #-}
getIndex :: BuildTermListM s f Int
getIndex = BuildM $ \_ n s -> (# s, n, I# n #)

{-# INLINE putIndex #-}
putIndex :: Int -> BuildTermListM s f ()
putIndex (I# n) = BuildM $ \_ _ s -> (# s, n, () #)

{-# INLINE liftST #-}
liftST :: ST s a -> BuildTermListM s f a
liftST (ST m) =
  BuildM $ \_ n s ->
  case m s of
    (# s, x #) -> (# s, n, x #)

{-# INLINE freezeTermList #-}
freezeTermList :: BuildTermListM s f (TermList f)
freezeTermList = do
  marray <- getArray
  n <- getIndex
  !array <- liftST $ unsafeFreezeByteArray marray
  return (TermList 0 n array)

{-# INLINE buildTermList #-}
buildTermList :: Int -> (forall s. BuildTermListM s f a) -> a
buildTermList size m =
  runST $ do
    MutableByteArray array <- newByteArray (size * sizeOf (fromSymbol __))
    ST $ \s ->
      case unBuildM m array 0# s of
        (# s, _, x #) -> (# s, x #)

{-# INLINE appendPrim #-}
appendPrim :: Symbol -> BuildTermListM s f () -> BuildTermListM s f ()
appendPrim x inner = do
  array <- getArray
  n <- getIndex
  putIndex (n+1)
  inner
  m <- getIndex
  liftST $ writeByteArray array n (fromSymbol x { size = m - n })

{-# INLINE appendRoot #-}
appendRoot :: Term f -> BuildTermListM s f () -> BuildTermListM s f ()
appendRoot t inner = appendPrim (toSymbol (root t)) inner

{-# INLINE appendFun #-}
appendFun :: Fun f -> BuildTermListM s f () -> BuildTermListM s f ()
appendFun (MkFun f) inner = appendPrim (Symbol True f 0) inner

{-# INLINE appendVar #-}
appendVar :: Var -> BuildTermListM s f ()
appendVar (MkVar x) = appendPrim (Symbol False x 1) (return ())

{-# INLINE appendTermList #-}
appendTermList :: TermList f -> BuildTermListM s f ()
appendTermList (TermList lo hi array) = do
  marray <- getArray
  n <- getIndex
  liftST $ copyByteArray marray n array lo (hi-lo)
  putIndex (n + hi-lo)

{-# INLINE appendTerm #-}
appendTerm :: Term f -> BuildTermListM s f ()
appendTerm t = appendTermList (singleton t)

data CompoundTerm f =
    CFlat (Term f)
  | CFun  (Fun f) [CompoundTerm f]
  | CVar  Var

flattenTerm :: CompoundTerm f -> Term f
flattenTerm t =
  case flattenTerms [t] of
    Cons u Empty -> u

flattenTerms :: [CompoundTerm f] -> TermList f
flattenTerms ts =
  buildTermList (sum (map len ts)) $ do
    let
      loop [] = return ()
      loop (CFlat t:ts) = do
        appendTerm t
        loop ts
      loop (CFun f ts:us) = do
        appendFun f (loop ts)
        loop us
      loop (CVar x:ts) = do
        appendVar x
        loop ts
    loop ts
    freezeTermList
  where
    len (CFlat t) = nsymbols (singleton t)
    len (CFun _ ts) = 1 + sum (map len ts)
    len (CVar _) = 1
