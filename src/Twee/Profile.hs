-- Basic support for profiling.
{-# LANGUAGE BangPatterns, RecordWildCards, CPP, OverloadedStrings #-}
module Twee.Profile(stamp, stampWith, stampM, profile) where

#ifdef PROFILE
import System.IO.Unsafe
import Data.IORef
import System.CPUTime.Rdtsc
import Data.List
import Data.Ord
import Text.Printf
import GHC.Conc.Sync
import Data.Word
import Control.Monad.IO.Class
import qualified Data.HashMap.Strict as HashMap
import Data.HashMap.Strict(HashMap)
import Data.Symbol
import Data.Symbol.Unsafe
import Data.Hashable

instance Hashable Symbol where
  hashWithSalt s (Symbol n _) = hashWithSalt s n

data Record =
  Record {
    rec_individual :: {-# UNPACK #-} !Word64,
    rec_cumulative :: {-# UNPACK #-} !Word64,
    rec_count      :: {-# UNPACK #-} !Word64 }

data Running =
  Running {
    run_started  :: {-# UNPACK #-} !Word64,
    run_skipped  :: {-# UNPACK #-} !Word64,
    run_overhead :: {-# UNPACK #-} !Word64 }

data State =
  State {
    st_map      :: !(HashMap Symbol Record),
    st_overhead :: {-# UNPACK #-} !Word64,
    st_running  :: {-# UNPACK #-} !Running,
    st_stack    :: [Running] }

{-# NOINLINE eventLog #-}
eventLog :: IORef State
eventLog = unsafePerformIO (newIORef (State HashMap.empty 0 (Running 0 0 0) []))

{-# NOINLINE enter #-}
enter :: IO (HashMap Symbol Record)
enter = do
  State{..} <- readIORef eventLog
  tsc <- rdtsc
  let !running = Running tsc 0 0
  writeIORef eventLog (State st_map st_overhead running (st_running:st_stack))
  return st_map

{-# NOINLINE exit #-}
exit :: HashMap Symbol Record -> Symbol -> IO ()
exit old_st str = do
  tsc <- rdtsc
  State st_map st_overhead Running{..} st_stack <- readIORef eventLog
  str `pseq` do
    let cumulative = tsc - run_started - run_overhead
        individual = cumulative - run_skipped
        -- To make sure recursive functions are accounted for properly,
        -- we reset cumulative time to what it was on entry
        Record _ c2 _ = HashMap.lookupDefault (Record 0 0 0) str old_st
        plus (Record i1 c1 m) (Record i2 _ n) =
          Record (i1+i2) (c1+c2) (m+n)
        rec = Record individual cumulative 1
        m = HashMap.insertWith plus str rec st_map
    case st_stack of
      [] -> error "mismatched enter/exit"
      Running{..}:st_stack -> m `pseq` do
        tsc' <- rdtsc
        let overhead = tsc' - tsc
            run =
              Running run_started
                (run_skipped+cumulative)
                (run_overhead+overhead)
        writeIORef eventLog $! State m (st_overhead + overhead) run st_stack

{-# NOINLINE stamp #-}
stamp :: Symbol -> a -> a
stamp str x =
  unsafePerformIO $ do
    m <- enter
    x `pseq` exit m str
    return x

stampWith :: Symbol -> (a -> b) -> a -> a
stampWith str f x = stamp str (f x) `pseq` x

stampM :: MonadIO m => Symbol -> m a -> m a
stampM str mx = do
  m <- liftIO enter
  x <- mx
  liftIO (exit m str)
  return x

report :: (Record -> Word64) -> HashMap Symbol Record -> IO ()
report f cs = mapM_ pr ts
  where
    ts =
      sortBy (comparing (negate . f . snd)) $
      sortBy (comparing fst) $
      HashMap.toList $
      {-HashMap.filter ((>= tot `div` 200) . f)-} cs
    tot = sum (map rec_individual (HashMap.elems cs))
    pr (str, rec) =
      printf "%10.2f Mclocks (%6.2f%% of total): %s, %d calls\n"
        (fromIntegral n / 10^6 :: Double)
        (100 * fromIntegral n / fromIntegral tot :: Double)
        (unintern str)
        (rec_count rec)
      where
        n = f rec

profile :: IO ()
profile = do
  State{..} <- readIORef eventLog
  let log = HashMap.insert "OVERHEAD" (Record st_overhead st_overhead 0) st_map
  putStrLn "Individual time:"
  report rec_individual log
  putStrLn ""
  putStrLn "Cumulative time:"
  report rec_cumulative log
#else
import Control.Monad.IO.Class

stamp :: symbol -> a -> a
stamp _ = id

stampWith :: symbol -> (a -> b) -> a -> a
stampWith _ _ = id

stampM :: MonadIO m => symbol -> m a -> m a
stampM _ = id

profile :: IO ()
profile = return ()
#endif
