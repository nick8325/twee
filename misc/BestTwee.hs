{-# LANGUAGE TemplateHaskell #-}
module Main where

import MaxCover
import System.FilePath
import System.FilePath.Glob
import System.Directory
import Control.Monad
import Data.Ord
import Data.List
import Data.Maybe
import Data.Time.Clock
import qualified Data.Map as Map
import Data.Map(Map)
import Data.FileEmbed

solvedInTime :: NominalDiffTime -> FilePath -> String -> IO Bool
solvedInTime timeLimit dir prob = do
  let
    stdout = dir </> prob ++ ".p.stdout"
    stderr = dir </> prob ++ ".p.stderr"
  outTime <- getModificationTime stdout
  errTime <- getModificationTime stderr
  return (diffUTCTime outTime errTime <= timeLimit)

notE :: [(String, Double)]
notE = filter (\(x, _) -> '+' `notElem` x) [
  ("GRP702+1", 0.06), ("GRP715+1", 0.06), ("GRP660+2", 0.12), ("GRP660+3", 0.12),
  ("GRP665+1", 0.12), ("GRP700+1", 0.12), ("GRP658+1", 0.18), ("GRP659+1", 0.18),
  ("GRP656+1", 0.24), ("GRP657+1", 0.24), ("GRP660+1", 0.24), ("GRP682+1", 0.24),
  ("GRP683+1", 0.24), ("GRP685+1", 0.24), ("GRP703+1", 0.24), ("GRP704+1", 0.24),
  ("GRP710+1", 0.24), ("GRP777+1", 0.24), ("LCL897+1", 0.29), ("LAT168-1", 0.30),
  ("LAT171-1", 0.43), ("ALG240-1", 0.48), ("GRP654+2", 0.53), ("GRP654+3", 0.53),
  ("GRP655+2", 0.53), ("GRP655+3", 0.53), ("LAT174-1", 0.65), ("LAT142-1", 0.70),
  ("GRP654+1", 0.71), ("GRP655+1", 0.71), ("GRP505-1", 0.74), ("LAT145-1", 0.74),
  ("LAT164-1", 0.74), ("GRP506-1", 0.78), ("GRP507-1", 0.78), ("LAT018-1", 0.78),
  ("LAT148-1", 0.78), ("LAT153-1", 0.78), ("LAT155-1", 0.78), ("GRP508-1", 0.83),
  ("KLE151-10", 0.83), ("LAT162-1", 0.83), ("LAT146-1", 0.87), ("LAT159-1", 0.87),
  ("LAT160-1", 0.87), ("LAT170-1", 0.87), ("LAT177-1", 0.87), ("GRP664+1", 0.88),
  ("ALG441-10", 0.91), ("COL042-10", 0.91), ("GRP196-1", 0.91), ("GRP666-3", 0.91),
  ("GRP666-4", 0.91), ("GRP666-5", 0.91), ("LAT156-1", 0.91), ("LAT169-1", 0.91),
  ("LCL148-10", 0.91), ("GRP164-2", 0.96), ("GRP666-2", 0.96), ("GRP678-1", 0.96),
  ("GRP725-1", 0.96), ("KLE110-10", 0.96), ("LAT072-1", 0.96), ("LAT076-1", 0.96),
  ("LAT140-1", 0.96), ("LAT141-1", 0.96), ("LAT144-1", 0.96), ("LAT147-1", 0.96),
  ("LAT149-1", 0.96), ("LAT151-1", 0.96), ("LAT158-1", 0.96), ("LAT163-1", 0.96),
  ("LAT167-1", 0.96), ("LAT172-1", 0.96), ("LAT173-1", 0.96), ("LAT175-1", 0.96),
  ("LAT176-1", 0.96), ("LCL927-10", 0.96), ("REL040-1", 0.96), ("REL040-3", 0.96),
  ("ALG212+1", 1.00), ("ALG213+1", 1.00), ("GRP724-1", 1.00), ("KLE122-10", 1.00),
  ("LAT074-1", 1.00), ("LAT075-1", 1.00), ("LAT077-1", 1.00), ("LAT078-1", 1.00),
  ("LAT079-1", 1.00), ("LAT139-1", 1.00), ("LAT161-1", 1.00), ("LCL220-10", 1.00),
  ("LCL330-10", 1.00), ("LCL348-10", 1.00), ("REL032-2", 1.00), ("REL038-1", 1.00),
  ("REL039-1", 1.00)]

ratings :: Map String Double
ratings =
  Map.fromList
    [ (name, read rating)
    | [name, rating] <- map words (lines input)]
  where
    input = $(embedStringFile "ratings")

problemBonus :: (Int, Int, Int, Int, Int, Int) -> String -> Int
problemBonus (b0, b1, b2, b3, b4, b5) p =
  ebonus *
  case Map.lookup p ratings of
    Nothing -> b0
    Just x
      | x < 0.7 ->   b1
      | x < 0.8 ->   b2
      | x < 0.9 ->   b3
      | x < 0.95 ->  b4
      | otherwise -> b5
  where
    ebonus =
      case lookup p notE of
        Nothing -> 1
        Just _ -> 1

greatProblemsBonus :: (Int, Int, Int, Int, Int, Int) -> String -> [String]
greatProblemsBonus b p =
  [p ++ "/" ++ show i | i <- [1..problemBonus b p]]

bonuses :: [(String, (Int, Int, Int, Int, Int, Int))]
bonuses =
  [("no bonus", (1, 1, 1, 1, 1, 1)),
   ("low bonus", (1, 2, 3, 4, 5, 6))]
   --("medium bonus", (1, 2, 4, 6, 8, 10)),
   --("high bonus", (0, 1, 2, 3, 4, 5))]
   --("big fish", (0, 0, 0, 0, 1, 1))]

readResults ok = do
  filenames <- glob "/home/nick/writing/twee/times/*-twee-casc-extra-*"
  fmap (filter (\(x, _) -> x `notElem` banned)) $ forM filenames $ \filename -> do
    let name = takeFileName filename
    let unpack xs = (takeBaseName name, read time :: Double) where [name, time] = words xs
    solved <- filter (ok . fst) . map unpack . lines <$> readFile filename
    let solvedInTime t = [name | (name, time) <- solved, time < t]
--    fast <- filterM (solvedInTime 120 directory) solved
--    med  <- filterM (solvedInTime 240 directory) solved
--    slow <- filterM (solvedInTime 600 directory) solved
    let fast = solvedInTime 240
    let med  = solvedInTime 360
    let slow = solvedInTime (1/0)
    
    return (name, (fast, med, slow))

score results cover =
  length (usort (concat [probs | (name, probs) <- results, name `elem` cover]))

levels results name names =
  [ (i, length xs)
  | i <- [0..length names],
    let xs = find name \\ concatMap find (take i names),
    not (null xs) ]
  where
    find x = fromJust (lookup x results)

main = do
  probs <- lines <$> readFile "unsat"
  results <- readResults (`elem` probs)
  let
    options =
      [("fast", \(fast, _, _) -> (fast, [], [])),
       ("med", \(_, med, _) -> ([], med, []))]
       --("slow", \(_, _, slow) -> ([], [], slow))]
       --("fast and slow", id)]

  forM_ bonuses $ \(bonus, b) -> do
    forM_ options $ \(option, f) -> do
      let
        results1 =
          [ (name,
             map (++ "/fast") (concatMap (greatProblemsBonus b) fast) ++
             map (++ "/med")  (concatMap (greatProblemsBonus b) med) ++
             map (++ "/slow") (concatMap (greatProblemsBonus b) slow))
          | (name, res) <- results,
            let (fast, med, slow) = f res ]

        best = greedy results1

      putStrLn (option ++ "/" ++ bonus ++ ":")
      forM_ (take 6 $ zip3 [1..] best (inits best)) $ \(i, name, names) -> do
        putStrLn (show i ++ ". " ++ name ++ " " ++ show (score results1 (name:names)) ++ ", useful at levels " ++ show (drop (length fixed) $ levels results1 name names))

      putStrLn ""

      {-
      putStrLn "\nBest:"
      forM_ [1..6] $ \i -> do
        cover <- maxCover i results1
        putStrLn (show i ++ ": " ++ show (score results1 cover))
        forM_ cover $ \name -> putStrLn ("  " ++ name)
      -}

greedy [] = []
greedy results =
  best:
  greedy (map deleteResults (delete (best, probs) results))
  where
    (best, probs) = maximumBy (comparing f) results
    deleteResults (name, probs') = (name, probs' \\ probs)

    f (name, probs) =
      case elemIndex name fixed of
        Just i -> Right (-i)
        Nothing -> Left (length probs)

fixed :: [String]
fixed = [
  "twee-210619-twee-casc-extra-lhs5-flip-aggrnorm-kbo0",
  "twee-210621-twee-casc-extra-depth-60-kbo0",
  "twee-210619-twee-casc-extra-complete-subsets",
  "twee-210621-twee-casc-extra-flatten-lhs9-kbo0",
  "twee-210619-twee-casc-extra-lhs9-nogoal-aggrnorm",
  "twee-210619-twee-casc-extra-lhs9-flip-nogoal-kbo0"]

{- attempt 1:
  "twee-210621-twee-casc-extra-flatten-lhs9-kbo0",
  "twee-210619-twee-casc-extra-lhs9-nogoal-aggrnorm",
  "twee-210621-twee-casc-extra-depth-60-kbo0",
  "twee-210619-twee-casc-extra-complete-subsets",
  "twee-210619-twee-casc-extra-lhs9-flip-nogoal-kbo0",
  "twee-210619-twee-casc-extra-lhs5-flip-aggrnorm-kbo0"]
-}

banned :: [String]
banned = []
