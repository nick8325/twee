module Twee.Generate(generateTerm, generateGoalTerm) where

import Test.QuickCheck hiding (Function)
import Twee.Base
import Twee.Rule
import Twee.Utils
import Data.Maybe

type Pat f = Term f
type LHS f = Term f

-- the generator

generateTerm :: Function f => [LHS f] -> Gen (Term f)
generateTerm lhss =
  sized $ \n -> do
    (t, _) <- gen n lhss (build (var (V 0)))
    return (build t)

gen :: Function f => Int -> [LHS f] -> Pat f -> Gen (Builder f, Subst f) -- a random Term, plus a subst relating it to Pat
gen n lhss p =
  -- TODO: play around with frequencies
  frequency $
  [ (1, return (builder (ground p), emptySubst)) ] ++
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

generateGoalTerm :: Function f => [Term f] -> [Rule f] -> Gen (Term f)
generateGoalTerm goals rules = sized $ \n -> do
  t <- elements goals
  u <- loop (isqrt n) (rewriteBackwards rules) t
  -- fill in any holes with randomly-generated terms
  let vs = usort (vars u)
  ts <- sequence [resize (isqrt n) (generateTerm (map lhs rules)) | _ <- vs]
  let Just sub = listToSubst (zip vs ts)
  return (subst sub u)

loop :: Monad m => Int -> (a -> m a) -> a -> m a
loop 0 _ x = return x
loop n f x | n > 0 = f x >>= loop (n-1) f

isqrt :: Int -> Int
isqrt n = truncate (sqrt (fromIntegral n))

rewriteBackwards :: Function f => [Rule f] -> Term f -> Gen (Term f)
rewriteBackwards rules t0 =
  frequency $
    [(1, return t0)] ++
    [(if bad then 1 else 10, return u) | (bad, u) <- candidates]
  where
    t = renameAvoiding rules t0
    candidates = [
        (isVar subterm, u)
      | n <- [0..len t-1],
        rule <- rules,
        let subterm = at n (singleton t),
        sub <- maybeToList (unify (rhs rule) subterm),
        let u = build (replacePositionSub sub n (singleton (lhs rule)) (singleton t)),
        len u <= 1000 ]
