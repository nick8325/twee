-- A module which can run housekeeping tasks every so often.
{-# LANGUAGE RecordWildCards #-}
module Twee.Task where

import System.CPUTime
import Data.IORef
import Control.Monad.IO.Class

data TaskData m a =
  Task {
    -- When was the task created?
    task_start :: !Integer,
    -- When was the task last run?
    task_last :: !Integer,
    -- How long have we spent on this task so far?
    task_spent :: !Integer,
    -- How often should we run this task at most, in seconds?
    task_frequency :: !Double,
    -- What proportion of our time should we spend on the task?
    task_budget :: !Double,
    -- The task itself
    task_what :: m a }
type Task m a = IORef (TaskData m a)

-- Create a new task that should be run a certain proportion
-- of the time.
newTask :: MonadIO m => Double -> Double -> m a -> m (Task m a)
newTask freq budget what = liftIO $ do
  now <- getCPUTime
  newIORef (Task now now 0 freq budget what)

-- Run a task if it's time to run it.
checkTask :: MonadIO m => Task m a -> m (Maybe a)
checkTask ref = do
  task@Task{..} <- liftIO $ readIORef ref
  now <- liftIO getCPUTime
  if not (taskDue now task) then return Nothing else do
    res <- task_what
    after <- liftIO getCPUTime
    liftIO $ writeIORef ref task {
      task_last = after,
      task_spent = task_spent + (after-now) }
    return (Just res)

-- Check if a task should be run now.
taskDue :: Integer -> TaskData m a -> Bool
taskDue now Task{..} =
  -- Don't run more than the frequency says.
  fromInteger (now - task_last) >= task_frequency * 10^12 &&
  -- Run if we spent less than task_budget proportion of the total time so far.
  -- Use > rather than >= so that tasks with zero budget never get run.
  fromInteger (now - task_start) * task_budget > fromInteger task_spent
