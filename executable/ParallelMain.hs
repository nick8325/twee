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
  concat $ repeat
  [["--lhs-weight", "3"],
   ["--lhs-weight", "4", "--flip-ordering"]]

main = do
  hSetBuffering stdout LineBuffering
  (n:args) <- getArgs
  raceStdout [withArgs (args ++ variant) SequentialMain.main | variant <- take (read n) variants]
