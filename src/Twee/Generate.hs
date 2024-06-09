{-# LANGUAGE OverloadedStrings #-}
module Twee.Generate(generateTerm, generateGoalTerm, permuteVars) where

import Test.QuickCheck hiding (Function)
import Twee.Base
import Twee.Rule
import Data.Maybe
import Twee.Profile
import Twee.Utils
import Debug.Trace

type Pat f = Term f
type LHS f = Term f

-- the generator

generateTerm :: Function f => [LHS f] -> Gen (Term f)
generateTerm lhss = generateTerm' lhss (build (var (V 0)))

generateTerm' :: Function f => [LHS f] -> Pat f -> Gen (Term f)
generateTerm' lhss pat =
  stampGen "generateTerm'" $ do
  sized $ \n -> do
    sub <- gen n lhss pat emptyTriangleSubst
    permuteVars (subst sub pat)

gen :: Function f => Int -> [LHS f] -> Pat f -> TriangleSubst f -> Gen (TriangleSubst f)
gen n lhss p sub =
  -- TODO: play around with frequencies
  frequency $
  [ (1, return sub) ] ++
  -- commit to top-level function...
  [ (n, genList (reduce n (length ps)) lhss ps sub)
  | App f psl <- [p]
  , let ps = unpack psl
  ] ++
  -- ...or use a LHS for inspiration
  [ (n, gen n lhss p' sub')
  | n > 0
  , lhs <- map (renameAvoiding p) lhss
  , Just sub' <- [unifyTriFrom lhs p sub]
  , let p' = subst sub' p
  , n >= (len p' - len p)
  , not (isVariantOf p' p) -- make progress
  ]
  where
    reduce n m
      | m <= 1 = n-1
      | otherwise = n `div` m

-- just a helper function
genList :: Function f => Int -> [LHS f] -> [Pat f] -> TriangleSubst f -> Gen (TriangleSubst f)
genList _n _lhss [] sub =
  do return sub

genList n lhss (p:ps) sub =
  do sub' <- gen n lhss (subst sub p) sub
     sub'' <- genList n lhss ps sub'
     return sub''

-- Generate a term by starting with a goal term and rewriting
-- backwawrds a certain number of times.
generateGoalTerm :: Function f => [Term f] -> [Rule f] -> Gen (Term f, Reduction1 f)
generateGoalTerm goals rules = stampGen "generateGoalTerm" $ sized $ \n -> do
  t <- frequency [(len u, return u) | u <- goals]
  -- () <- traceM ("Goal term: " ++ prettyShow t)
  let ok u = len u <= n
  (u, r) <- loop (n `div` 5 + 1) (rewriteBackwardsWithReduction ok rules) (t, [])
  -- () <- traceM ("intermediate generated " ++ prettyShow u)
  -- fill in any holes with randomly-generated terms
  v <- generateTerm' (map lhs rules) u
  -- () <- traceM ("generated " ++ prettyShow v)
  -- () <- traceM ("proof " ++ prettyShow r)
  return (v, rematchReduction1 v r)

loop :: Monad m => Int -> (a -> m a) -> a -> m a
loop 0 _ x = return x
loop n f x | n > 0 = f x >>= loop (n-1) f

-- Apply a rule backwards at a given position in a term.
-- The goal rhs and the subterm must be unifiable.
tryBackwardsRewrite :: Rule f -> Term f -> Int -> Maybe (Term f, Reduction1 f)
tryBackwardsRewrite rule t n = do
  sub <- unify (rhs rule) (t `at` n)
  return $
    (build (replacePositionSub sub n (singleton (lhs rule)) (singleton t)),
     [(rule, sub, positionToPath t n)])

rewriteBackwardsWithReduction :: Function f => (Term f -> Bool) -> [Rule f] -> (Term f, Reduction1 f) -> Gen (Term f, Reduction1 f)
rewriteBackwardsWithReduction ok rules (t, r) = do
  res <- rewriteBackwards ok rules t
  case res of
    Nothing -> return (t, r)
    Just (u, r') -> return (u, r' `trans1` r)

-- Pick a random rule and rewrite the term backwards using it.
rewriteBackwards :: Function f => (Term f -> Bool) -> [Rule f] -> Term f -> Gen (Maybe (Term f, Reduction1 f))
rewriteBackwards ok rules t0
  | not (ok t0) = return Nothing
  | otherwise = 
    frequency $
      [(1, return Nothing)] ++ -- in case no rules work
      [ -- penalise unification with a variable as it can result in "type-incorrect" terms
        (if isVar (t `at` n) then 1 else 10*(overlap (t `at` n) (rhs rule)+1)*(if n == 0 then 2 else 1),
         return (Just (u, r)))
      | n <- [0..len t-1],
        rule <- rules,
        (u, r) <- maybeToList (tryBackwardsRewrite rule t n),
        ok u ]
  where
    t = renameAvoiding rules t0
    overlap (App f ts) (App g us) | f == g =
      1 + sum (zipWith overlap (unpack ts) (unpack us))
    overlap _ _ = 0

permuteVars :: Term f -> Gen (Term f)
permuteVars t = do
  let vs = usort (vars t)
  ws <- shuffle vs
  let Just sub = listToSubst [(v, build (var w)) | (v, w) <- zip vs ws]
  return (subst sub t)
