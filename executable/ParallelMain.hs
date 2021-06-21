{-# LANGUAGE ForeignFunctionInterface #-}
import System.IO
import Control.Concurrent.Async hiding (link)
import System.Posix
import System.Environment
import qualified SequentialMain
import Control.Monad

foreign import ccall "link_to_parent" link :: CPid -> IO ()

raceMany :: [IO a] -> IO a
raceMany [x] = x
raceMany (x:xs) = do
  result <- race x (raceMany xs)
  case result of
    Left res  -> return res
    Right res -> return res

raceStdout :: [IO ()] -> IO ()
raceStdout xs = do
  action <- raceMany (map waitForStdout xs)
  action
  where
    end = "*** END OF OUTPUT"
    waitForStdout p = do
      (fdIn, fdOut) <- createPipe
      pid <- getProcessID
      forkProcess $ do
        link (fromIntegral pid)
        dupTo fdOut stdOutput
        hSetBuffering stdout LineBuffering
        p
        putStrLn end

      hIn <- fdToHandle fdIn
      hSetBuffering hIn LineBuffering
      line <- hGetLine hIn
      return $ do
        putStrLn line
        let
          loop = do
            line <- hGetLine hIn
            unless (line == end) $ do
              putStrLn line
              loop
        loop

variants :: [[String]]
variants =
  map words
  ["--lhs-weight 1 --flip-ordering --normalise-queue-percent 10 --cp-renormalise-threshold 10",
   "--no-flatten-goal",
   "--lhs-weight 5 --flip-ordering --normalise-queue-percent 10 --cp-renormalise-threshold 10",
   "--lhs-weight 9 --no-flatten-goal --normalise-queue-percent 10 --cp-renormalise-threshold 10",
   "--complete-subsets --kbo-weight0 --lhs-weight 1 --flip-ordering --flatten",
   "--flip-ordering --lhs-weight 1 --depth-weight 60 --kbo-weight0",
   "--flip-ordering --lhs-weight 1 --dup-cost 0 --dup-factor 7",
   "--no-flatten-goal --dup-cost 0 --dup-factor 7"]

main = do
  hSetBuffering stdout LineBuffering
  (n:args) <- getArgs
  raceStdout [withArgs (args ++ variant) SequentialMain.main | variant <- take (read n) variants]
