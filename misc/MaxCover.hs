module MaxCover where

import SAT
import SAT.Optimize
import SAT.Unary hiding (modelValue)
import qualified SAT.Unary as Unary
import Data.List
import qualified Data.Map.Strict as Map
import Control.Monad

usort :: Ord a => [a] -> [a]
usort = map head . group . sort

maxCover :: (Ord label, Ord object) => Int -> [(label, [object])] -> IO [label]
maxCover limit xs = do
  s <- newSolver
  let
    labels = map fst xs
    objects = usort (concatMap snd xs)

  labelLits  <- sequence [newLit s | _ <- labels]
  objectLits <- sequence [newLit s | _ <- objects]

  let
    labelMap = Map.fromList (zip labels labelLits)
    labelInvMap = Map.fromList (zip labelLits labels)
    objectMap = Map.fromList (zip objects objectLits)
    find m x = Map.findWithDefault undefined x m

  lits <-
    maxCover_ s limit
      [ (find labelMap label, map (find objectMap) objects)
      | (label, objects) <- xs ]

  return (map (find labelInvMap) lits)

maxCover_ :: Solver -> Int -> [(Lit, [Lit])] -> IO [Lit]
maxCover_ s limit xs = do
  let
    labels  = map fst xs
    objects = usort (concatMap snd xs)
    occ = Map.fromListWith (++) [(obj, [label]) | (label, objs) <- xs, obj <- objs]

  forM_ xs $ \(label, objs) -> do
    forM_ objs $ \obj -> do
      addClause s [neg label, obj]

  forM_ objects $ \obj -> do
    let labels = Map.findWithDefault undefined obj occ
    addClause s (neg obj:labels)

  numChosen <- count s labels
  numCovered <- count s objects

  -- Maximise #objects while respecting limit
  addClause s [numChosen .<= limit]
  True <- solveMaximize s [] numCovered

  -- Now minimise #labels while preserving #objects
  goal <- Unary.modelValue s numCovered
  addClause s [numCovered .>= goal]
  True <- solveMinimize s [] numChosen
  filterM (modelValue s) labels
