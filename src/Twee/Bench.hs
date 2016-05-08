-- Basic support for benchmarking.
{-# LANGUAGE BangPatterns #-}
module Twee.Bench(stamp, stampM, profile) where

import System.IO.Unsafe
import Data.IORef
import System.CPUTime.Rdtsc
import Data.List
import Twee.Utils
import Data.Ord
import Text.Printf
import Control.Parallel
import Data.Word
import Control.Monad.IO.Class

data Event = Enter !String !Word64 | Exit !String !Word64 deriving Show
data Call = Call { callName :: String, callTime :: Word64, callSub :: [Call] } deriving Show

{-# NOINLINE eventLog #-}
eventLog :: IORef [Event]
eventLog = unsafePerformIO (newIORef [])

newEvent :: (Word64 -> Event) -> IO ()
newEvent e = do
  time <- rdtsc
  let !ev = e time
  atomicModifyIORef' eventLog (\evs -> (ev:evs, ()))

stamp :: String -> a -> a
stamp str x =
  unsafePerformIO $ do
    newEvent (Enter str)
    x `pseq` newEvent (Exit $! str)
    return x

stampM :: MonadIO m => String -> m a -> m a
stampM str mx = do
  liftIO (newEvent (Enter str))
  x <- mx
  liftIO (newEvent (Exit $! str))
  return x

getLog :: IO [Event]
getLog = fmap reverse (readIORef eventLog)

getCalls :: IO [Call]
getCalls = do
  time <- rdtsc
  fmap (toCalls time) getLog

toCalls :: Word64 -> [Event] -> [Call]
toCalls t xs = ys
  where
    (ys, []) = toCalls1 t xs

toCalls1 t (Enter str m:xs) =
  case toCalls1 t xs of
    (ys, Exit str' n:zs) | str == str' ->
      let (as, bs) = toCalls1 t zs in
      (Call str (n-m) ys:as, bs)

    (ys, []) ->
      ([Call str (t-m) ys], [])

toCalls1 _ xs = ([], xs)

type Timing = ([String], Word64)

timings :: [String] -> Call -> [Timing]
timings funcs call =
  (funcs', callTime call - sum (map callTime (callSub call))):
  concatMap (timings funcs') (callSub call)
  where
    funcs' = callName call:funcs

total :: ([String] -> [String]) -> [Timing] -> [(String, Word64)]
total f ts =
  sortBy (comparing ord)
  [ (fst y, sum (map snd ys))
  | ys@(y:_) <- partitionBy fst xs ]
  where
    xs = [(str, n) | (funcs, n) <- ts, str <- usort (f funcs)]
    ord (str, n) = (-n, str)

cumulative, individual :: [Timing] -> [(String, Word64)]
cumulative = total id
individual = total (take 1)

report :: ([Timing] -> [(String, Word64)]) -> [Call] -> IO ()
report f cs = mapM_ pr ts
  where
    ts = filter ((>= tot `div` 100) . snd) (f (concatMap (timings []) cs))
    tot = sum (map callTime cs)
    pr (str, n) =
      printf "%10.2f Mclocks (%6.2f%% of total): %s\n"
        (fromIntegral n / 10^6 :: Double)
        (100 * fromIntegral n / fromIntegral tot :: Double)
        str

profile :: IO ()
profile = do
  calls <- getCalls
  putStrLn "Individual time:"
  report individual calls
  putStrLn ""
  putStrLn "Cumulative time:"
  report cumulative calls
