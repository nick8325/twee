-- Tactics for joining critical pairs.
{-# LANGUAGE FlexibleContexts, BangPatterns #-}
module Twee.Join where

import Twee.Base
import Twee.Rule
import Twee.CP
import Twee.Constraints
import qualified Twee.Index as Index
import Twee.Index(Index)
import Twee.Utils
import Data.Maybe
import Data.Either
import Data.List

{-# INLINEABLE joinOverlap #-}
joinOverlap ::
  (Function f, Has a (Rule f)) =>
  Index f (Equation f) -> Index f a ->
  Overlap f -> Either [Equation f] (Overlap f, Model f)
joinOverlap eqns idx overlap =
  case allSteps eqns idx overlap of
    Just overlap ->
      case groundJoin eqns idx (branches (And [])) overlap of
        Left model -> Right (overlap, model)
        Right overlaps ->
          case all (isLeft . joinOverlap eqns idx) overlaps of
            True -> Left [overlap_eqn overlap]
            False -> Right (overlap, modelFromOrder [])
    Nothing ->
      Left []

{-# INLINEABLE step1 #-}
{-# INLINEABLE step2 #-}
{-# INLINEABLE step3 #-}
{-# INLINEABLE allSteps #-}
step1, step2, step3, allSteps ::
  (Function f, Has a (Rule f)) => Index f (Equation f) -> Index f a -> Overlap f -> Maybe (Overlap f)
allSteps eqns idx overlap = step1 eqns idx overlap >>= step2 eqns idx >>= step3 eqns idx
step1 eqns idx = joinWith eqns idx id
step2 eqns idx = joinWith eqns idx (result . normaliseWith (const True) (rewrite reduces idx))
step3 eqns idx overlap =
  case overlap_top overlap of
    Cons top Empty ->
      case (join (overlap, top), join (flipCP (overlap, top))) of
        (Just _, Just _) -> Just overlap
        _ -> Nothing
    _ -> Just overlap
  where
    join (overlap, top) =
      joinWith eqns idx (result . normaliseWith (check top) (rewrite reducesSkolem idx)) overlap

    check top u = lessEq u top && isNothing (unify u top)

    flipCP :: Symbolic a => a -> a
    flipCP t = subst sub t
      where
        n = maximum (0:map fromEnum (vars t))
        sub (V x) = var (V (n - x))


{-# INLINEABLE joinWith #-}
joinWith ::
  Has a (Rule f) =>
  Index f (Equation f) -> Index f a -> (Term f -> Term f) -> Overlap f -> Maybe (Overlap f)
joinWith eqns idx reduce overlap
  | subsumed eqns idx eqn = Nothing
  | otherwise = Just overlap { overlap_eqn = eqn }
  where
    eqn = bothSides reduce (overlap_eqn overlap)

-- N.B.:
-- The subsumption check works *asymmetrically*: rather than check if
-- t = u can be joined, it checks if t can be rewritten to u
-- (ignoring ordering constraints). This is usually the same, because
-- we generate unorientable rules in pairs. But it's important in
-- Twee.consider, where after orienting an equation into a set of rules,
-- we check each rule for subsumption in turn before adding it.
{-# INLINEABLE subsumed #-}
subsumed :: Has a (Rule f) => Index f (Equation f) -> Index f a -> Equation f -> Bool
subsumed eqns idx (t :=: u)
  | t == u = True
  | or [ rhs rule == u | rule <- Index.lookup t idx ] = True
  | or [ u == subst sub u'
       | t' :=: u' <- Index.approxMatches t eqns,
         sub <- maybeToList (match t' t) ] = True
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

groundJoin ::
  (Function f, Has a (Rule f)) =>
  Index f (Equation f) -> Index f a -> [Branch f] -> Overlap f -> Either (Model f) [Overlap f]
groundJoin eqns idx ctx r@Overlap{overlap_top = top, overlap_eqn = t :=: u} =
  case partitionEithers (map (solve (usort (atoms t ++ atoms u))) ctx) of
    ([], instances) ->
      let rs = [ subst sub r | sub <- instances ] in
      Right (usort (map canonicalise rs))
    (model:_, _)
      | isJust (allSteps eqns idx r { overlap_eqn = t' :=: u' }) -> Left model
      | otherwise ->
          let model1 = optimise model weakenModel (\m -> valid m nt && valid m nu)
              model2 = optimise model1 weakenModel (\m -> isNothing (allSteps eqns idx r { overlap_eqn = result (normaliseIn m t) :=: result (normaliseIn m u) }))

              diag [] = Or []
              diag (r:rs) = negateFormula r ||| (weaken r &&& diag rs)
              weaken (LessEq t u) = Less t u
              weaken x = x
              ctx' = formAnd (diag (modelToLiterals model2)) ctx in

          groundJoin eqns idx ctx' r
      where
        normaliseIn m = normaliseWith (const True) (rewrite (reducesInModel m) idx)
        nt = normaliseIn model t
        nu = normaliseIn model u
        t' = result nt
        u' = result nu

valid :: Function f => Model f -> Reduction f -> Bool
valid model red = all valid1 (steps red)
  where
    valid1 (rule, sub) = reducesInModel model rule sub

optimise :: a -> (a -> [a]) -> (a -> Bool) -> a
optimise x f p =
  case filter p (f x) of
    y:_ -> optimise y f p
    _   -> x
