{-# LANGUAGE OverloadedStrings #-}
module Twee.Generate(generateTerm, generateGoalTerm, permuteVars) where

import Test.QuickCheck hiding (Function)
import Twee.Base
import Twee.Rule
import Data.Maybe
import Twee.Profile
import Twee.Utils

type Pat f = Term f
type LHS f = Term f

-- the generator

generateTerm :: Function f => [LHS f] -> Gen (Term f)
generateTerm lhss = generateTerm' lhss (build (var (V 0)))

generateTerm' :: Function f => [LHS f] -> Pat f -> Gen (Term f)
generateTerm' lhss pat =
  stampGen "generateTerm'" $ do
  sized $ \n -> do
    (t, _) <- gen n lhss pat
    permuteVars (build t)

gen :: Function f => Int -> [LHS f] -> Pat f -> Gen (Builder f, Subst f) -- a random Term, plus a subst relating it to Pat
gen n lhss p =
  -- TODO: play around with frequencies
  frequency $
  [ (1, return (builder p, emptySubst)) ] ++
  -- commit to top-level function...
  [ (n,
     do (ts,sub) <- genList (reduce n (length ps)) lhss ps
        return (app f ts, sub))
  | App f psl <- [p]
  , let ps = unpack psl
  ] ++
  -- ...or use a LHS for inspiration
  [ (n,
     do (t,sub') <- gen n lhss p'
        return (t,subst sub' sub))
  | n > 0
  , lhs <- map (renameAvoiding p) lhss
  , Just sub <- [unify lhs p]
  , let p' = subst sub p
  , n >= (len p' - len p)
  , not (isVariantOf p' p) -- make progress
  ]
  where
    reduce n m
      | m <= 1 = n-1
      | otherwise = n `div` m

-- just a helper function
genList :: Function f => Int -> [LHS f] -> [Pat f] -> Gen (Builder f, Subst f)
genList _n _lhss [] =
  do return (mempty,emptySubst)

genList n lhss (p:ps) =
  do (t,sub) <- gen n lhss p
     (ts,sub') <- genList n lhss (map (subst sub) ps)
     return (t `mappend` ts,sub `substUnion` sub')

-- Generate a term by starting with a goal term and rewriting
-- backwawrds a certain number of times.
generateGoalTerm :: Function f => [Term f] -> [Rule f] -> Gen (Term f)
generateGoalTerm goals rules = stampGen "generateGoalTerm" $ sized $ \n -> do
  t <- elements goals
  u <- loop (n `div` 5 + 1) (rewriteBackwards n rules) t
  -- fill in any holes with randomly-generated terms
  generateTerm' (map lhs rules) u

loop :: Monad m => Int -> (a -> m a) -> a -> m a
loop 0 _ x = return x
loop n f x | n > 0 = f x >>= loop (n-1) f

-- Apply a rule backwards at a given position in a term.
-- The goal rhs and the subterm must be unifiable.
tryBackwardsRewrite :: Rule f -> Term f -> Int -> Maybe (Term f)
tryBackwardsRewrite rule t n = do
  sub <- unify (rhs rule) (t `at` n)
  return (build (replacePositionSub sub n (singleton (lhs rule)) (singleton t)))

-- Pick a random rule and rewrite the term backwards using it.
rewriteBackwards :: Function f => Int -> [Rule f] -> Term f -> Gen (Term f)
rewriteBackwards maxSize rules t0
  | len t0 >= maxSize = return t0
  | otherwise = 
    frequency $
      [(1, return t0)] ++ -- in case no rules work
      [ -- penalise unification with a variable as it can result in "type-incorrect" terms
        (if isVar (t `at` n) then 1 else 10*len (t `at` n)*(if n == 0 then 2 else 1), return u)
      | n <- [0..len t-1],
        rule <- rules,
        u <- maybeToList (tryBackwardsRewrite rule t n),
        len u <= maxSize ]
  where
    t = renameAvoiding rules t0

permuteVars :: Term f -> Gen (Term f)
permuteVars t = do
  let vs = usort (vars t)
  ws <- shuffle vs
  let Just sub = listToSubst [(v, build (var w)) | (v, w) <- zip vs ws]
  return (subst sub t)
