-- Tactics for joining critical pairs.
{-# LANGUAGE FlexibleContexts, BangPatterns #-}
module Twee.Join where

import Twee.Base
import Twee.Rule
import Twee.CP
import qualified Twee.Index.Simple as Index
import Twee.Index.Simple(Index)

subsumed :: (Symbolic a, Has a (RuleOf a), Has a (TermOf a)) => Index a -> TermOf a -> TermOf a -> Bool
subsumed idx t u
  | t == u = True
  | or [ rhs (the x) == u | x <- Index.lookup t idx ] = True
subsumed idx (App f ts) (App g us)
  | f == g =
    let
      sub Empty Empty = False
      sub (Cons t ts) (Cons u us) =
        subsumed idx t u && sub ts us
      sub _ _ = error "Function used with multiple arities"
    in
      sub ts us
subsumed _ _ _ = False

joinWith :: (Symbolic a, Function (ConstantOf a), Has a (RuleOf a), Has a (TermOf a)) => Index a -> (TermOf a -> TermOf a) -> OverlapOf a -> Maybe (OverlapOf a)
joinWith idx reduce overlap
  | subsumed idx left right = Nothing
  | otherwise =
      Just overlap {
        overlap_left  = left,
        overlap_right = right }
  where
    left  = reduce (overlap_left overlap)
    right = reduce (overlap_right overlap)

step1, step2, step3 :: (Symbolic a, Function (ConstantOf a), Has a (RuleOf a), Has a (TermOf a)) => Index a -> OverlapOf a -> Maybe (OverlapOf a)
step1 idx = joinWith idx (simplify idx)
step2 idx = joinWith idx (result . normaliseWith (rewrite "cp join 2" reduces idx))
step3 idx overlap = joinWith idx (result . normaliseWith (rewrite "cp join 3" (reducesSub (overlap_top overlap)) idx)) overlap
