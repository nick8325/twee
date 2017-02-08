-- Tactics for joining critical pairs.
{-# LANGUAGE FlexibleContexts, BangPatterns #-}
module Twee.Join where

import Twee.Base
import Twee.Rule
import Twee.CP
import qualified Twee.Index as Index
import Twee.Index(Index)

joinWith ::
  Has a (Rule f) =>
  Index f a -> (Term f -> Term f) -> Overlap f -> Maybe (Overlap f)
joinWith idx reduce overlap
  | subsumed idx eqn = Nothing
  | otherwise = Just overlap { overlap_eqn = eqn }
  where
    eqn = bothSides reduce (overlap_eqn overlap)

subsumed :: Has a (Rule f) => Index f a -> Equation f -> Bool
subsumed idx (t :=: u)
  | t == u = True
  | or [ rhs x == u | x <- Index.lookup t idx ] = True
subsumed idx (App f ts :=: App g us)
  | f == g =
    let
      sub Empty Empty = False
      sub (Cons t ts) (Cons u us) =
        subsumed idx (t :=: u) && sub ts us
      sub _ _ = error "Function used with multiple arities"
    in
      sub ts us
subsumed _ _ = False

step1, step2, step3, step4 ::
  (Function f, Has a (Rule f)) => Index f a -> Overlap f -> Maybe (Overlap f)
step1 idx = joinWith idx (simplify idx)
step2 idx = joinWith idx (result . normaliseWith (rewrite "cp join 2" reduces idx))
