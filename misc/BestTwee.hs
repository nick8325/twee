{-# LANGUAGE TemplateHaskell #-}
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
  [("no bonus", (1, 1, 1, 1, 1, 1))]
   --("low bonus", (1, 1, 2, 3, 4, 5))]
   --("medium bonus", (1, 2, 4, 6, 8, 10))]
   --("high bonus", (0, 1, 2, 3, 4, 5))]
   --("big fish", (0, 0, 0, 0, 1, 1))]

readResults ok = do
  filenames <- glob "out/*-twee-bench-*/success"
  fmap (filter (\(x, _) -> x `notElem` banned)) $ forM filenames $ \filename -> do
    let directory = takeDirectory filename
    let name = takeFileName directory
    solved <- fmap (filter ok) $ lines <$> readFile filename
    fast <- filterM (solvedInTime 120 directory) solved
    med  <- filterM (solvedInTime 240 directory) solved
    slow <- filterM (solvedInTime 600 directory) solved
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
      [("med", \(_, med, _) -> ([], med, []))]
       --("fast", \(fast, _, _) -> (fast, [], []))]
       --("slow", \(_, slow) -> ([], slow)),
       --("fast and slow", id)]

  forM_ options $ \(option, f) -> do
    forM_ bonuses $ \(bonus, b) -> do
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
      forM_ (take 8 $ zip3 [1..] best (inits best)) $ \(i, name, names) -> do
        putStrLn (show i ++ ". " ++ name ++ " " ++ show (score results1 (name:names)) ++ ", useful at levels " ++ show (drop (length fixed) $ levels results1 name names))

      putStrLn ""

--      putStrLn "\nBest:"
--      forM_ [1..8] $ \i -> do
--        cover <- maxCover i results1
--        putStrLn (show i ++ ": " ++ show (score results1 cover))
--        forM_ cover $ \name -> putStrLn ("  " ++ name)

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
  "twee-210508-twee-bench-lhs1-flip-aggrnorm",
  "twee-210508-twee-bench-lhs4-nogoal",
  "twee-210508-twee-bench-lhs9-flip",
  "twee-210509-twee-bench-flattenlightly-aggrnorm",
  "twee-210509-twee-bench-no-dup",
  "twee-210508-twee-bench-lhs9-nogoal-aggrnorm",
  "twee-210508-twee-bench-lhs9-flip-nogoal",
  "twee-210508-twee-bench-lhs4-aggrnorm"]

fixed1 = [
  "twee-210508-twee-bench-lhs1-flip-aggrnorm",
  "twee-210508-twee-bench-lhs9-nogoal-aggrnorm",
  "twee-210508-twee-bench-lhs5",
  "twee-210509-twee-bench-no-dup",
  "twee-210508-twee-bench-lhs9-flip-nogoal",
  "twee-210508-twee-bench-lhs5-flip-aggrnorm",
  "twee-210508-twee-bench-no-simplify",
  "twee-210509-twee-bench-lhsnormal-flattenlightly-aggrnorm"]

fixed2 = take 2 [
  "twee-210508-twee-bench-lhs1-flip-aggrnorm",
  "twee-210508-twee-bench-lhs4-nogoal",
  "twee-210508-twee-bench-lhs9-flip",
  "twee-210508-twee-bench-lhs9-flip-nogoal",
  "twee-210509-twee-bench-flattenlightly",
  "twee-210509-twee-bench-no-dup",
  "twee-210508-twee-bench-lhs4-aggrnorm",
  "twee-210508-twee-bench-lhs9-nogoal-aggrnorm"]


-- with bonus only for e-unsolvable problems:
-- 1. twee-210508-twee-bench-lhs1-flip-aggrnorm 1059, useful at levels [(0,1059)]
-- 2. twee-210508-twee-bench-lhs9-flip-nogoal 1202, useful at levels [(0,964),(1,143)]
-- 3. twee-210508-twee-bench-lhs5 1248, useful at levels [(0,984),(1,85),(2,46)]
-- 4. twee-210509-twee-bench-no-dup-nogoal 1269, useful at levels [(0,900),(1,93),(2,21),(3,21)]
-- 5. twee-210509-twee-bench-no-dup 1283, useful at levels [(0,1045),(1,25),(2,16),(3,14),(4,14)]
-- 6. twee-210508-twee-bench-lhs5-flip-aggrnorm 1294, useful at levels [(0,992),(1,68),(2,34),(3,11),(4,11),(5,11)]
-- 7. twee-210508-twee-bench-no-simplify 1302, useful at levels [(0,1053),(1,16),(2,8),(3,8),(4,8),(5,8),(6,8)]
-- 8. twee-210508-twee-bench-lhs9-nogoal-aggrnorm 1307, useful at levels [(0,933),(1,93),(2,7),(3,6),(4,5),(5,5),(6,5),(7,5)]

-- without e bonus:
-- 1. twee-210508-twee-bench-lhs1-flip-aggrnorm 1034, useful at levels [(0,1034)]
-- 2. twee-210508-twee-bench-lhs9-nogoal 1131, useful at levels [(0,957),(1,97)]
-- 3. twee-210508-twee-bench-lhs5 1158, useful at levels [(0,970),(1,60),(2,27)]
-- 4. twee-210509-twee-bench-no-dup 1172, useful at levels [(0,1030),(1,32),(2,19),(3,14)]
-- 5. twee-210509-twee-bench-lhsnormal-flattenlightly-aggrnorm 1184, useful at levels [(0,978),(1,75),(2,15),(3,12),(4,12)]
-- 6. twee-210508-twee-bench-lhs9-flip-nogoal 1192, useful at levels [(0,934),(1,93),(2,18),(3,12),(4,12),(5,8)]
-- 7. twee-210508-twee-bench-lhs5-flip-aggrnorm 1200, useful at levels [(0,977),(1,51),(2,26),(3,8),(4,8),(5,8),(6,8)]
-- 8. twee-210508-twee-bench-no-simplify 1207, useful at levels [(0,1022),(1,16),(2,7),(3,7),(4,7),(5,7),(6,7),(7,7)]

-- with e bonus 2:
-- 1. twee-210508-twee-bench-lhs1-flip-aggrnorm 3886, useful at levels [(0,3886)]
-- 2. twee-210508-twee-bench-lhs9-nogoal-aggrnorm 4194, useful at levels [(0,3636),(1,308)]
-- 3. twee-210508-twee-bench-lhs5 4274, useful at levels [(0,3682),(1,184),(2,80)]
-- 4. twee-210509-twee-bench-no-dup 4320, useful at levels [(0,3876),(1,114),(2,54),(3,46)]
-- 5. twee-210508-twee-bench-lhs9-flip-nogoal 4360, useful at levels [(0,3556),(1,266),(2,58),(3,40),(4,40)]
-- 6. twee-210508-twee-bench-lhs5-flip-aggrnorm 4382, useful at levels [(0,3698),(1,158),(2,58),(3,22),(4,22),(5,22)]
-- 7. twee-210508-twee-bench-no-simplify 4404, useful at levels [(0,3836),(1,54),(2,22),(3,22),(4,22),(5,22),(6,22)]
-- 8. twee-210509-twee-bench-lhsnormal-flattenlightly-aggrnorm 4420, useful at levels [(0,3732),(1,216),(2,48),(3,24),(4,24),(5,16),(6,16),(7,16)]

-- with e bonus 3:
-- 1. twee-210508-twee-bench-lhs1-flip-aggrnorm 5704, useful at levels [(0,5704)]
-- 2. twee-210508-twee-bench-lhs9-nogoal-aggrnorm 6136, useful at levels [(0,5380),(1,432)]
-- 3. twee-210508-twee-bench-lhs5 6230, useful at levels [(0,5424),(1,248),(2,94)]
-- 4. twee-210509-twee-bench-no-dup 6294, useful at levels [(0,5692),(1,164),(2,76),(3,64)]
-- 5. twee-210508-twee-bench-lhs9-flip-nogoal 6340, useful at levels [(0,5244),(1,346),(2,64),(3,46),(4,46)]
-- 6. twee-210508-twee-bench-no-simplify 6370, useful at levels [(0,5628),(1,76),(2,30),(3,30),(4,30),(5,30)]
-- 7. twee-210508-twee-bench-lhs5-flip-aggrnorm 6398, useful at levels [(0,5442),(1,214),(2,70),(3,28),(4,28),(5,28),(6,28)]
-- 8. twee-210509-twee-bench-lhsnormal-flattenlightly-aggrnorm 6414

--  "twee-210508-twee-bench-lhs1-flip-aggrnorm",
--  "twee-210508-twee-bench-lhs4-nogoal",
--  "twee-210508-twee-bench-lhs9-flip",
--  "twee-210509-twee-bench-flattenlightly-aggrnorm",
--  "twee-210509-twee-bench-no-dup",
--  "twee-210508-twee-bench-lhs9-flip-nogoal"]

--  "twee-200715-twee-goal-flip-lhs2",
--  "twee-200714-twee-goalagain",
--  "twee-200712-twee-ghc8.10",
--  "twee-200714-twee-goalagain-flip-lhs1",
--  "twee-200715-twee-goal-lhs4-var3",
--  "twee-200715-twee-goal-lhs6-var3",
--  "twee-200715-twee-goal-lhs2-var3",
--  "twee-200611-twee-flip-lhs9"]
--fixed = [
--  "twee-200612-twee-aggressive-renormalise-flip-lhs4",
--  "twee-200612-twee-aggressive-renormalise-flip-lhs9",
--  "twee-200611-twee-flip-lhs1",
--  "twee-200611-twee-lhs4",
--  "twee-200611-twee-lhs5",
--  "twee-200612-twee-aggressive-renormalise-nodup",
--  "twee-200611-twee-nosimp",
--  "twee-200612-twee-aggressive-renormalise-nodepth"]

banned :: [String]
banned = []
--  "twee-200714-twee-goalagain",
--  "twee-200714-twee-goalagain-flip-lhs1",
--  "twee-200714-twee-goalagain-flip-lhs3"]
