-- Tactics for joining critical pairs.
{-# LANGUAGE FlexibleContexts, BangPatterns #-}
module Twee.Join where

import Twee.Base
import Twee.Rule
import Twee.CP
import Twee.Constraints
import qualified Twee.Index as Index
import Twee.Index(Index)
import Data.Maybe

{-# INLINEABLE joinOverlap #-}
joinOverlap ::
  (Function f, Has a (Rule f)) =>
  Index f (Equation f) -> Index f a ->
  Overlap f -> Either [Equation f] (Overlap f, Model f)
joinOverlap eqns idx overlap =
  case step1 eqns idx overlap >>= step2 eqns idx of
    Just overlap ->
      Right (overlap, modelFromOrder [])
    Nothing ->
      Left []

{-# INLINEABLE step1 #-}
{-# INLINEABLE step2 #-}
step1, step2 ::
  (Function f, Has a (Rule f)) => Index f (Equation f) -> Index f a -> Overlap f -> Maybe (Overlap f)
step1 eqns idx = joinWith eqns idx id
step2 eqns idx = joinWith eqns idx (result . normaliseWith (rewrite reduces idx))

{-# INLINEABLE joinWith #-}
joinWith ::
  Has a (Rule f) =>
  Index f (Equation f) -> Index f a -> (Term f -> Term f) -> Overlap f -> Maybe (Overlap f)
joinWith eqns idx reduce overlap
  | subsumed eqns idx eqn = Nothing
  | otherwise = Just overlap { overlap_eqn = eqn }
  where
    eqn = bothSides reduce (overlap_eqn overlap)

{-# INLINEABLE subsumed #-}
subsumed :: Has a (Rule f) => Index f (Equation f) -> Index f a -> Equation f -> Bool
subsumed eqns idx (t :=: u)
  | t == u = True
  | sub1 t u || sub1 u t = True
  where
    sub1 t u =
      or [ rhs rule == u | rule <- Index.lookup t idx ] ||
      or [ u == subst sub u'
         | t' :=: u' <- Index.approxMatches t eqns,
           sub <- maybeToList (match t' t) ]
subsumed eqns idx (App f ts :=: App g us)
  | f == g =
    let
      sub Empty Empty = False
      sub (Cons t ts) (Cons u us) =
        subsumed eqns idx (t :=: u) && sub ts us
      sub _ _ = error "Function used with multiple arities"
    in
      sub ts us
subsumed _ _ _ = False
