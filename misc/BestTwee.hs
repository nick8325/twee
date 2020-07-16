import MaxCover
import System.FilePath
import System.FilePath.Glob
import System.Directory
import Control.Monad
import Data.Ord
import Data.List
import Data.Maybe
import Data.Time.Clock

solvedInTime :: NominalDiffTime -> FilePath -> String -> IO Bool
solvedInTime timeLimit dir prob = do
  let
    stdout = dir </> prob ++ ".p.stdout"
    stderr = dir </> prob ++ ".p.stderr"
  outTime <- getModificationTime stdout
  errTime <- getModificationTime stderr
  return (diffUTCTime outTime errTime <= timeLimit)

notE :: [(String, Double)]
notE = [
  ("LAT168-1", 0.30), ("LAT171-1", 0.43), ("ALG240-1", 0.48), ("LAT174-1", 0.65), ("GRP768-1", 0.70),
  ("LAT142-1", 0.70), ("GRP505-1", 0.74), ("LAT145-1", 0.74), ("LAT164-1", 0.74), ("RNG025-5", 0.74),
  ("GRP506-1", 0.78), ("GRP507-1", 0.78), ("LAT018-1", 0.78), ("LAT148-1", 0.78), ("LAT153-1", 0.78),
  ("LAT155-1", 0.78), ("RNG025-4", 0.78), ("GRP508-1", 0.83), ("KLE151-10", 0.83), ("LAT162-1", 0.83),
  ("ALG246-1", 0.87), ("GRP024-5", 0.87), ("GRP766-1", 0.87), ("LAT146-1", 0.87), ("LAT159-1", 0.87),
  ("LAT160-1", 0.87), ("LAT170-1", 0.87), ("LAT177-1", 0.87), ("REL022-2", 0.87), ("COL042-10", 0.91),
  ("GRP196-1", 0.91), ("GRP666-3", 0.91), ("GRP666-4", 0.91), ("GRP666-5", 0.91), ("LAT156-1", 0.91),
  ("LAT157-1", 0.91), ("LAT169-1", 0.91), ("LCL148-10", 0.91), ("REL020-2", 0.91), ("REL021-1", 0.91),
  ("REL021-2", 0.91), ("REL022-1", 0.91), ("REL029-1", 0.91), ("REL033-1", 0.91), ("REL033-3", 0.91),
  ("REL034-1", 0.91), ("REL034-2", 0.91), ("REL035-1", 0.91), ("REL035-2", 0.91), ("REL036-1", 0.91),
  ("GRP164-1", 0.96), ("GRP164-2", 0.96), ("GRP666-2", 0.96), ("GRP678-1", 0.96), ("GRP721-1", 0.96),
  ("GRP725-1", 0.96), ("KLE110-10", 0.96), ("LAT072-1", 0.96), ("LAT076-1", 0.96), ("LAT140-1", 0.96),
  ("LAT141-1", 0.96), ("LAT144-1", 0.96), ("LAT147-1", 0.96), ("LAT149-1", 0.96), ("LAT151-1", 0.96),
  ("LAT158-1", 0.96), ("LAT163-1", 0.96), ("LAT167-1", 0.96), ("LAT172-1", 0.96), ("LAT173-1", 0.96),
  ("LAT175-1", 0.96), ("LAT176-1", 0.96), ("LAT183-10", 0.96), ("LAT186-10", 0.96), ("LCL927-10", 0.96),
  ("REL020-1", 0.96), ("REL040-1", 0.96), ("REL040-3", 0.96), ("GRP177-1", 1.00), ("GRP724-1", 1.00),
  ("LAT074-1", 1.00), ("LAT075-1", 1.00), ("LAT077-1", 1.00), ("LAT078-1", 1.00), ("LAT079-1", 1.00),
  ("LAT139-1", 1.00), ("LAT161-1", 1.00), ("LCL220-10", 1.00), ("LCL330-10", 1.00), ("LCL348-10", 1.00),
  ("REL032-1", 1.00), ("REL032-2", 1.00), ("REL038-1", 1.00), ("REL039-1", 1.00), ("ROB007-1", 1.00),
  ("ROB033-1", 1.00)]

problemBonus :: (Int, Int, Int, Int, Int, Int) -> String -> Int
problemBonus (b0, b1, b2, b3, b4, b5) p =
  case lookup p notE of
    Nothing -> b0
    Just x
      | x < 0.7 ->   b1
      | x < 0.8 ->   b2
      | x < 0.9 ->   b3
      | x < 0.95 ->  b4
      | otherwise -> b5

greatProblemsBonus :: (Int, Int, Int, Int, Int, Int) -> String -> [String]
greatProblemsBonus b p =
  [p ++ "/" ++ show i | i <- [1..problemBonus b p]]

bonuses :: [(String, (Int, Int, Int, Int, Int, Int))]
bonuses =
  [("no bonus", (1, 1, 1, 1, 1, 1)),
   ("low bonus", (1, 1, 2, 3, 4, 5)),
   ("medium bonus", (1, 2, 4, 6, 8, 10)),
   ("high bonus", (0, 1, 2, 3, 4, 5)),
   ("big fish", (0, 0, 0, 0, 1, 1))]

readResults ok = do
  filenames <- glob "out/twee-*/success"
  fmap (filter (\(x, _) -> x `notElem` banned)) $ forM filenames $ \filename -> do
    let directory = takeDirectory filename
    let name = takeFileName directory
    solved <- fmap (filter ok) $ lines <$> readFile filename
    fast <- filterM (solvedInTime 120 directory) solved
    slow <- filterM (solvedInTime 600 directory) solved
    return (name, (fast, slow))

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
  probs <- lines <$> readFile "casc-j10"
  results <- readResults (`elem` probs)
  let
    options =
      [("fast", \(fast, _) -> (fast, []))]
       --("slow", \(_, slow) -> ([], slow)),
       --("fast and slow", id)]

  forM_ options $ \(option, f) -> do
    forM_ bonuses $ \(bonus, b) -> do
      let
        results1 =
          [ (name,
             map (++ "/fast") (concatMap (greatProblemsBonus b) fast) ++
             map (++ "/slow") (concatMap (greatProblemsBonus b) slow))
          | (name, res) <- results,
            let (fast, slow) = f res ]

        best = greedy results1

      putStrLn (option ++ "/" ++ bonus ++ ":")
      forM_ (zip3 [1..] best (inits best)) $ \(i, name, names) -> do
        putStrLn (show i ++ ". " ++ name ++ " " ++ show (score results1 (name:names)) ++ ", useful at levels " ++ show (levels results1 name names))

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
  "twee-200715-twee-goal-flip-lhs2",
  "twee-200714-twee-goalagain",
  "twee-200712-twee-ghc8.10",
  "twee-200714-twee-goalagain-flip-lhs1",
  "twee-200715-twee-goal-lhs4-var3",
  "twee-200715-twee-goal-lhs6-var3",
  "twee-200715-twee-goal-lhs2-var3",
  "twee-200611-twee-flip-lhs9"]
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
