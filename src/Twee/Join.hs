-- Tactics for joining critical pairs.
{-# LANGUAGE FlexibleContexts, BangPatterns, RecordWildCards, TypeFamilies, DeriveGeneric #-}
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
import Data.Ord
import GHC.Generics

-- A critical pair together with information about how it was derived
data CriticalPair f =
  CriticalPair {
    cp_eqn   :: {-# UNPACK #-} !(Equation f),
    cp_top   :: !(Maybe (Term f)),
    cp_proof :: !(Proof f) }
  deriving Generic

instance Symbolic (CriticalPair f) where
  type ConstantOf (CriticalPair f) = f

{-# INLINEABLE makeCriticalPair #-}
makeCriticalPair ::
  (Has a (Rule f), Has a VersionedId) => a -> a -> Overlap f -> CriticalPair f
makeCriticalPair r1 r2 overlap@Overlap{..} =
  CriticalPair overlap_eqn
    (Just overlap_top)
    (overlapProof r1 r2 overlap)

{-# INLINEABLE joinCriticalPair #-}
joinCriticalPair ::
  (Function f, Has a (Rule f), Has a VersionedId) =>
  Index f (Equation f) -> Index f a ->
  CriticalPair f -> ([Equation f], Maybe (CriticalPair f, [Model f]))
joinCriticalPair eqns idx cp =
  case allSteps eqns idx cp of
    Just cp ->
      case groundJoin eqns idx (branches (And [])) cp of
        Left model -> ([], Just (cp, [model]))
        Right cps ->
          let
            (eqnss, mcps) = unzip (map (joinCriticalPair eqns idx) cps)
          in
            case all isNothing mcps of
              True -> (cp_eqn cp:concat eqnss, Nothing)
              False -> (concat eqnss, Just (cp, []))
    Nothing ->
      ([], Nothing)

{-# INLINEABLE step1 #-}
{-# INLINEABLE step2 #-}
{-# INLINEABLE step3 #-}
{-# INLINEABLE allSteps #-}
step1, step2, step3, allSteps ::
  (Function f, Has a (Rule f), Has a VersionedId) =>
  Index f (Equation f) -> Index f a -> CriticalPair f -> Maybe (CriticalPair f)
allSteps eqns idx cp = step1 eqns idx cp >>= step2 eqns idx >>= step3 eqns idx
step1 eqns idx = joinWith eqns idx (normaliseWith (const True) (rewrite reducesOriented idx))
step2 eqns idx = joinWith eqns idx (normaliseWith (const True) (rewrite reduces idx))
step3 eqns idx cp =
  case cp_top cp of
    Just top ->
      case (join (cp, top), join (flipCP (cp, top))) of
        (Just _, Just _) -> Just cp
        _ -> Nothing
    _ -> Just cp
  where
    join (cp, top) =
      joinWith eqns idx (normaliseWith (check top) (rewrite reducesSkolem idx)) cp

    check top u = lessEq u top && isNothing (unify u top)

    flipCP :: Symbolic a => a -> a
    flipCP t = subst sub t
      where
        n = maximum (0:map fromEnum (vars t))
        sub (V x) = var (V (n - x))


{-# INLINEABLE joinWith #-}
joinWith ::
  (Has a (Rule f), Has a VersionedId) =>
  Index f (Equation f) -> Index f a -> (Term f -> Reduction f) -> CriticalPair f -> Maybe (CriticalPair f)
joinWith eqns idx reduce cp@CriticalPair{cp_eqn = lhs :=: rhs, ..}
  | subsumed Symmetric eqns idx eqn = Nothing
  | otherwise =
    Just cp {
      cp_eqn = eqn,
      cp_proof =
        [Backwards lred] ++ cp_proof ++ [Forwards rred] }
  where
    lred = reduce lhs
    rred = reduce rhs
    eqn = result lred :=: result rred

data SubsumptionMode = Symmetric | Asymmetric deriving Eq

{-# INLINEABLE subsumed #-}
subsumed ::
  (Has a (Rule f), Has a VersionedId) =>
  SubsumptionMode -> Index f (Equation f) -> Index f a -> Equation f -> Bool
subsumed mode eqns idx (t :=: u)
  | t == u = True
  | or [ rhs rule == u | rule <- Index.lookup t idx ] = True
  | mode == Symmetric &&
    or [ rhs rule == t | rule <- Index.lookup u idx ] = True
  | subEqn t u || subEqn u t = True
  where
    subEqn t u =
      or [ u == subst sub u'
         | t' :=: u' <- Index.approxMatches t eqns,
           sub <- maybeToList (match t' t) ]
subsumed mode eqns idx (App f ts :=: App g us)
  | f == g =
    let
      sub Empty Empty = False
      sub (Cons t ts) (Cons u us) =
        subsumed mode eqns idx (t :=: u) && sub ts us
      sub _ _ = error "Function used with multiple arities"
    in
      sub ts us
subsumed _ _ _ _ = False

{-# INLINEABLE groundJoin #-}
groundJoin ::
  (Function f, Has a (Rule f), Has a VersionedId) =>
  Index f (Equation f) -> Index f a -> [Branch f] -> CriticalPair f -> Either (Model f) [CriticalPair f]
groundJoin eqns idx ctx r@CriticalPair{cp_eqn = t :=: u} =
  case partitionEithers (map (solve (usort (atoms t ++ atoms u))) ctx) of
    ([], instances) ->
      let rs = [ subst sub r | sub <- instances ] in
      Right (usortBy (comparing (canonicalise . order . cp_eqn)) rs)
    (model:_, _)
      | isJust (allSteps eqns idx r { cp_eqn = t' :=: u' }) -> Left model
      | otherwise ->
          let model1 = optimise model weakenModel (\m -> valid m nt && valid m nu)
              model2 = optimise model1 weakenModel (\m -> isNothing (allSteps eqns idx r { cp_eqn = result (normaliseIn m t) :=: result (normaliseIn m u) }))

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
