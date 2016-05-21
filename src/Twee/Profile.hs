-- Basic support for profiling.
{-# LANGUAGE BangPatterns, RecordWildCards, CPP #-}
module Twee.Profile(stamp, stampM, profile) where

#include "errors.h"
import System.IO.Unsafe
import Data.IORef
import System.CPUTime.Rdtsc
import Data.List
import Data.Ord
import Text.Printf
import GHC.Conc.Sync
import Data.Word
import Control.Monad.IO.Class
import qualified Data.Map.Strict as Map
import Data.Map(Map)

data Record =
  Record {
    rec_individual :: {-# UNPACK #-} !Word64,
    rec_cumulative :: {-# UNPACK #-} !Word64 }

plus :: Record -> Record -> Record
x `plus` y =
  Record
    (rec_individual x + rec_individual y)
    (rec_cumulative x + rec_cumulative y)

data Running =
  Running {
    run_started  :: {-# UNPACK #-} !Word64,
    run_skipped  :: {-# UNPACK #-} !Word64,
    run_overhead :: {-# UNPACK #-} !Word64 }

data State =
  State {
    st_map      :: !(Map String Record),
    st_overhead :: {-# UNPACK #-} !Word64,
    st_running  :: {-# UNPACK #-} !Running,
    st_stack    :: [Running] }

{-# NOINLINE eventLog #-}
eventLog :: IORef State
eventLog = unsafePerformIO (newIORef (State Map.empty 0 (Running 0 0 0) []))

enter :: IO ()
enter = do
  State{..} <- readIORef eventLog
  tsc <- rdtsc
  let !running = Running tsc 0 0
  writeIORef eventLog (State st_map st_overhead running (st_running:st_stack))

exit :: String -> IO ()
exit str = do
  State st_map st_overhead Running{..} st_stack <- readIORef eventLog
  tsc <- rdtsc
  length str `pseq` do
    let cumulative = tsc - run_started - run_overhead
        individual = cumulative - run_skipped
        rec = Record individual cumulative
        m = Map.insertWith plus str rec st_map
    case st_stack of
      [] -> ERROR("mismatched enter/exit")
      Running{..}:st_stack -> m `pseq` do
        tsc' <- rdtsc
        let overhead = tsc' - tsc
            run =
              Running run_started
                (run_skipped+cumulative)
                (run_overhead+overhead)
        writeIORef eventLog $! State m (st_overhead + overhead) run st_stack

stamp :: String -> a -> a
stamp str x =
  unsafePerformIO $ do
    enter
    x `pseq` exit str
    return x

stampM :: MonadIO m => String -> m a -> m a
stampM str mx = do
  liftIO enter
  x <- mx
  liftIO (exit str)
  return x

report :: (Record -> Word64) -> Map String Record -> IO ()
report f cs = mapM_ pr ts
  where
    ts =
      sortBy (comparing (negate . snd)) $
      sortBy (comparing fst) $
      Map.toList $
      Map.filter (>= tot `div` 100) (fmap f cs)
    tot = sum (map rec_individual (Map.elems cs))
    pr (str, n) =
      printf "%10.2f Mclocks (%6.2f%% of total): %s\n"
        (fromIntegral n / 10^6 :: Double)
        (100 * fromIntegral n / fromIntegral tot :: Double)
        str

profile :: IO ()
profile = do
  State{..} <- readIORef eventLog
  let log = Map.insert "OVERHEAD" (Record st_overhead st_overhead) st_map
  putStrLn "Individual time:"
  report rec_individual log
  putStrLn ""
  putStrLn "Cumulative time:"
  report rec_cumulative log
