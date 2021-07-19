-- | Miscellaneous utility functions.

{-# LANGUAGE CPP, MagicHash, GeneralizedNewtypeDeriving #-}
module Twee.Utils where

import Control.Arrow((&&&))
import Control.Exception
import Data.List(groupBy, sortBy)
import Data.Ord(comparing)
import System.IO
import GHC.Prim
import GHC.Types
import Data.Bits
import System.Random
import Data.Serialize
--import Test.QuickCheck hiding ((.&.))

repeatM :: Monad m => m a -> m [a]
repeatM = sequence . repeat

partitionBy :: Ord b => (a -> b) -> [a] -> [[a]]
partitionBy value =
  map (map fst) .
  groupBy (\x y -> snd x == snd y) .
  sortBy (comparing snd) .
  map (id &&& value)

collate :: Ord a => ([b] -> c) -> [(a, b)] -> [(a, c)]
collate f = map g . partitionBy fst
  where
    g xs = (fst (head xs), f (map snd xs))

isSorted :: Ord a => [a] -> Bool
isSorted xs = and (zipWith (<=) xs (tail xs))

isSortedBy :: Ord b => (a -> b) -> [a] -> Bool
isSortedBy f xs = isSorted (map f xs)

usort :: Ord a => [a] -> [a]
usort = usortBy compare

usortBy :: (a -> a -> Ordering) -> [a] -> [a]
usortBy f = map head . groupBy (\x y -> f x y == EQ) . sortBy f

sortBy' :: Ord b => (a -> b) -> [a] -> [a]
sortBy' f = map snd . sortBy (comparing fst) . map (\x -> (f x, x))

usortBy' :: Ord b => (a -> b) -> [a] -> [a]
usortBy' f = map snd . usortBy (comparing fst) . map (\x -> (f x, x))

orElse :: Ordering -> Ordering -> Ordering
EQ `orElse` x = x
x  `orElse` _ = x

unbuffered :: IO a -> IO a
unbuffered x = do
  buf <- hGetBuffering stdout
  bracket_
    (hSetBuffering stdout NoBuffering)
    (hSetBuffering stdout buf)
    x

labelM :: Monad m => (a -> m b) -> [a] -> m [(a, b)]
labelM f = mapM (\x -> do { y <- f x; return (x, y) })

#if __GLASGOW_HASKELL__ < 710
isSubsequenceOf :: Ord a => [a] -> [a] -> Bool
[] `isSubsequenceOf` ys = True
(x:xs) `isSubsequenceOf` [] = False
(x:xs) `isSubsequenceOf` (y:ys)
  | x == y = xs `isSubsequenceOf` ys
  | otherwise = (x:xs) `isSubsequenceOf` ys
#endif

fixpoint :: Eq a => (a -> a) -> a -> a
fixpoint = fixpointOn id

{-# INLINE fixpoint #-}
fixpointOn :: Eq b => (a -> b) -> (a -> a) -> a -> a
fixpointOn key f x = fxp x
  where
    fxp x
      | key x == key y = x
      | otherwise = fxp y
      where
        y = f x

-- From "Bit twiddling hacks": branchless min and max
{-# INLINE intMin #-}
intMin :: Int -> Int -> Int
intMin x y =
  y `xor` ((x `xor` y) .&. negate (x .<. y))
  where
    I# x .<. I# y = I# (x <# y)

{-# INLINE intMax #-}
intMax :: Int -> Int -> Int
intMax x y =
  x `xor` ((x `xor` y) .&. negate (x .<. y))
  where
    I# x .<. I# y = I# (x <# y)

-- Split an interval (inclusive bounds) into a particular number of blocks
splitInterval :: Integral a => a -> (a, a) -> [(a, a)]
splitInterval k (lo, hi) =
  [ (lo+i*blockSize, (lo+(i+1)*blockSize-1) `min` hi)
  | i <- [0..k-1] ]
  where
    size = (hi-lo+1)
    blockSize = (size + k - 1) `div` k -- division rounding up
{-
prop_split_1 (Positive k) (lo, hi) =
  -- Check that all elements occur exactly once
  concat [[x..y] | (x, y) <- splitInterval k (lo, hi)] === [lo..hi]

-- Check that we have the correct number and distribution of blocks
prop_split_2 (Positive k) (lo, hi) =
  counterexample (show splits) $ conjoin
    [counterexample "Reason: too many splits" $
       length splits <= k,
     counterexample "Reason: too few splits" $
       length [lo..hi] >= k ==> length splits == k,
     counterexample "Reason: uneven distribution" $
      not (null splits) ==>
       minimum (map length splits) + 1 >= maximum (map length splits)]
  where
    splits = splitInterval k (lo, hi)
-}

reservoir :: Int -> [(Integer, Int)]
reservoir k =
  zip (map fromIntegral prefix) prefix ++
  zip (map (+fromIntegral k) (scanl1 (+) is)) ks
  where
    xs, ys :: [Double]
    xs = randomRs (0, 1) (mkStdGen 314159265)
    ys = randomRs (0, 1) (mkStdGen 358979323)
    ks = randomRs (0, k-1) (mkStdGen 846264338)

    ws = scanl1 (*) [ x ** (1 / fromIntegral k) | x <- xs ]
    is = zipWith gen ws ys
    gen w y = floor (log y / log (1-w)) + 1
    prefix = [0..k-1]

data Sample a = Sample Integer [(Integer, Int)] [a]

emptySample :: Int -> Sample a
emptySample k = Sample 0 (reservoir k) []

addSample :: (Int, [a]) -> Sample a -> Sample a
addSample (m, xs) (Sample total ((n, pos):ps) sample)
  | idx < fromIntegral m =
    addSample (m, xs) $
      Sample total ps $
        take pos sample ++
        [xs !! fromIntegral idx] ++
        drop (pos+1) sample
  where
    idx = n - total
addSample (m, _) (Sample total ps sample) =
  Sample (total+fromIntegral m) ps sample

sampleValue :: Sample a -> [a]
sampleValue (Sample _ _ sample) = sample

mapSample :: (a -> b) -> Sample a -> Sample b
mapSample f (Sample total ps sample) =
  Sample total ps (map f sample)

-- A combined inits/tails.
splits :: [a] -> [([a], [a])]
splits [] = [([], [])]
splits (x:xs) =
  [([], x:xs)] ++
  [(x:ys, zs) | (ys, zs) <- splits xs]

-- Fold over the natural numbers.
foldn :: (a -> a) -> a -> Int -> a
foldn _ e 0 = e
foldn op e n | n > 0 = op (foldn op e (n-1))

newtype U8 = U8 Int deriving (Eq, Ord, Num, Real, Enum, Integral)

-- Untested!
instance Serialize U8 where
  put (U8 n)
    | n < 0x80 = putWord8 (fromIntegral n)
    | n < 0x4000 = do
      putWord16be (fromIntegral n + 0x8000)
    | otherwise = do
      putWord32be (fromIntegral n + 0xc0000000)
  get = do
    x <- lookAhead getWord8
    if x < 0x80 then fromIntegral <$> getWord8
    else if x < 0xc0 then do
      n <- getWord16be
      return (fromIntegral (n - 0x8000))
    else do
      n <- getWord32be
      return (fromIntegral (n - 0xc0000000))

-- Untested!
newtype U16 = U16 Int deriving (Eq, Ord, Num, Real, Enum, Integral)
instance Serialize U16 where
  put (U16 n)
    | n < 0x8000 = do
      putWord16be (fromIntegral n)
    | otherwise = do
      putWord32be (fromIntegral n + 0x80000000)
  get = do
    x <- lookAhead getWord8
    if x < 0x80 then fromIntegral <$> getWord16be
    else do
      n <- getWord32be
      return (fromIntegral (n - 0x80000000))

-- Can be used to write strictness annotations e.g.
-- f !_ !_ | never = undefined
-- which otherwise trigger a spurious warning from GHC.
{-# INLINE never #-}
never :: Bool
never = False
