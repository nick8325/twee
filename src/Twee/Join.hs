-- | Tactics for joining critical pairs.
{-# LANGUAGE FlexibleContexts, BangPatterns, RecordWildCards, TypeFamilies #-}
module Twee.Join where

import Twee.Base
import Twee.Rule
import Twee.Equation
import Twee.Proof(Proof)
import qualified Twee.Proof as Proof
import Twee.CP hiding (Config)
import Twee.Constraints
import qualified Twee.Index as Index
import Twee.Index(Index)
import Twee.Rule.Index(RuleIndex(..))
import Twee.Utils
import Data.Maybe
import Data.Either
import Data.Ord
import qualified Data.Set as Set

data Config =
  Config {
    cfg_ground_join :: !Bool,
    cfg_use_connectedness :: !Bool,
    cfg_set_join :: !Bool }

defaultConfig :: Config
defaultConfig =
  Config {
    cfg_ground_join = True,
    cfg_use_connectedness = True,
    cfg_set_join = False }

{-# INLINEABLE joinCriticalPair #-}
joinCriticalPair ::
  (Function f, Has a (Rule f), Has a (Proof f)) =>
  Config ->
  Index f (Equation f) -> RuleIndex f a ->
  Maybe (Model f) -> -- A model to try before checking ground joinability
  CriticalPair f ->
  Either
    -- Failed to join critical pair.
    -- Returns simplified critical pair and model in which it failed to hold.
    (CriticalPair f, Model f)
    -- Split critical pair into several instances.
    -- Returns list of instances which must be joined,
    -- and an optional equation which can be added to the joinable set
    -- after successfully joining all instances.
    (Maybe (CriticalPair f), [CriticalPair f])
joinCriticalPair config eqns idx mmodel cp@CriticalPair{cp_eqn = t :=: u} =
  {-# SCC joinCriticalPair #-}
  case allSteps config eqns idx cp of
    Nothing ->
      Right (Nothing, [])
    _ | cfg_set_join config &&
        not (null $ Set.intersection
          (normalForms (rewrite reduces (index_all idx)) (Set.singleton (reduce (Refl t))))
          (normalForms (rewrite reduces (index_all idx)) (Set.singleton (reduce (Refl u))))) ->
      Right (Just cp, [])
    Just cp ->
      case groundJoinFromMaybe config eqns idx mmodel (branches (And [])) cp of
        Left model -> Left (cp, model)
        Right cps -> Right (Just cp, cps)

{-# INLINEABLE step1 #-}
{-# INLINEABLE step2 #-}
{-# INLINEABLE step3 #-}
{-# INLINEABLE allSteps #-}
step1, step2, step3, allSteps ::
  (Function f, Has a (Rule f), Has a (Proof f)) =>
  Config -> Index f (Equation f) -> RuleIndex f a -> CriticalPair f -> Maybe (CriticalPair f)
allSteps config eqns idx cp =
  step1 config eqns idx cp >>=
  step2 config eqns idx >>=
  step3 config eqns idx
step1 _ eqns idx = joinWith eqns idx (\t _ -> normaliseWith (const True) (rewrite reducesOriented (index_oriented idx)) t)
step2 _ eqns idx = joinWith eqns idx (\t _ -> normaliseWith (const True) (rewrite reduces (index_all idx)) t)
step3 Config{..} eqns idx cp
  | not cfg_use_connectedness = Just cp
  | otherwise =
    case cp_top cp of
      Just top ->
        case (join (cp, top), join (flipCP (cp, top))) of
          (Just cp1, Just cp2) ->
            case simplerThan (cp_eqn cp1) (cp_eqn cp2) of
              True -> Just cp1
              False -> Just cp2
          _ -> Nothing
      _ -> Just cp
  where
    join (cp, top) =
      joinWith eqns idx (\t u -> normaliseWith (`lessThan` top) (rewrite (ok t u) (index_all idx)) t) cp

    ok t u rule sub =
      unorient rule `simplerThan` (t :=: u) &&
      reducesSkolem rule sub

    flipCP :: Symbolic a => a -> a
    flipCP t = subst sub t
      where
        n = maximum (0:map fromEnum (vars t))
        sub (V x) = var (V (n - x))


{-# INLINEABLE joinWith #-}
joinWith ::
  (Has a (Rule f), Has a (Proof f)) =>
  Index f (Equation f) -> RuleIndex f a -> (Term f -> Term f -> Resulting f) -> CriticalPair f -> Maybe (CriticalPair f)
joinWith eqns idx reduce cp@CriticalPair{cp_eqn = lhs :=: rhs, ..}
  | subsumed eqns idx eqn = Nothing
  | otherwise =
    Just cp {
      cp_eqn = eqn,
      cp_proof =
        Proof.symm (reductionProof (reduction lred)) `Proof.trans`
        cp_proof `Proof.trans`
        reductionProof (reduction rred) }
  where
    lred = reduce lhs rhs
    rred = reduce rhs lhs
    eqn = result lred :=: result rred

{-# INLINEABLE subsumed #-}
subsumed ::
  (Has a (Rule f), Has a (Proof f)) =>
  Index f (Equation f) -> RuleIndex f a -> Equation f -> Bool
subsumed eqns idx (t :=: u)
  | t == u = True
  | or [ rhs rule == u | rule <- Index.lookup t (index_all idx) ] = True
  | or [ rhs rule == t | rule <- Index.lookup u (index_all idx) ] = True
    -- No need to do this symmetrically because addJoinable adds
    -- both orientations of each equation
  | or [ u == subst sub u'
       | t' :=: u' <- Index.approxMatches t eqns,
         sub <- maybeToList (match t' t) ] = True
subsumed eqns idx (App f ts :=: App g us)
  | f == g =
    let
      sub Empty Empty = True
      sub (Cons t ts) (Cons u us) =
        subsumed eqns idx (t :=: u) && sub ts us
      sub _ _ = error "Function used with multiple arities"
    in
      sub ts us
subsumed _ _ _ = False

{-# INLINEABLE groundJoin #-}
groundJoin ::
  (Function f, Has a (Rule f), Has a (Proof f)) =>
  Config -> Index f (Equation f) -> RuleIndex f a -> [Branch f] -> CriticalPair f -> Either (Model f) [CriticalPair f]
groundJoin config eqns idx ctx cp@CriticalPair{cp_eqn = t :=: u, ..} =
  case partitionEithers (map (solve (usort (atoms t ++ atoms u))) ctx) of
    ([], instances) ->
      let cps = [ subst sub cp | sub <- instances ] in
      Right (usortBy (comparing (canonicalise . order . cp_eqn)) cps)
    (model:_, _) ->
      groundJoinFrom config eqns idx model ctx cp

{-# INLINEABLE groundJoinFrom #-}
groundJoinFrom ::
  (Function f, Has a (Rule f), Has a (Proof f)) =>
  Config -> Index f (Equation f) -> RuleIndex f a -> Model f -> [Branch f] -> CriticalPair f -> Either (Model f) [CriticalPair f]
groundJoinFrom config@Config{..} eqns idx model ctx cp@CriticalPair{cp_eqn = t :=: u, ..}
  | not cfg_ground_join ||
    (modelOK model && isJust (allSteps config eqns idx cp { cp_eqn = t' :=: u' })) = Left model
  | otherwise =
      let model1 = optimise model weakenModel (\m -> not (modelOK m) || (valid m (reduction nt) && valid m (reduction nu)))
          model2 = optimise model1 weakenModel (\m -> not (modelOK m) || isNothing (allSteps config eqns idx cp { cp_eqn = result (normaliseIn m t u) :=: result (normaliseIn m u t) }))

          diag [] = Or []
          diag (r:rs) = negateFormula r ||| (weaken r &&& diag rs)
          weaken (LessEq t u) = Less t u
          weaken x = x
          ctx' = formAnd (diag (modelToLiterals model2)) ctx in

      groundJoin config eqns idx ctx' cp
  where
    normaliseIn m t u = normaliseWith (const True) (rewrite (ok t u m) (index_all idx)) t
    ok t u m rule sub =
      reducesInModel m rule sub &&
      unorient rule `simplerThan` (t :=: u)

    nt = normaliseIn model t u
    nu = normaliseIn model u t
    t' = result nt
    u' = result nu

    -- XXX not safe to exploit the top term if we then add the equation to
    -- the joinable set. (It might then be used to join a CP with an entirely
    -- different top term.)
    modelOK _ = True
{-    modelOK m =
      case cp_top of
        Nothing -> True
        Just top ->
          isNothing (lessIn m top t) && isNothing (lessIn m top u)-}

{-# INLINEABLE groundJoinFromMaybe #-}
groundJoinFromMaybe ::
  (Function f, Has a (Rule f), Has a (Proof f)) =>
  Config -> Index f (Equation f) -> RuleIndex f a -> Maybe (Model f) -> [Branch f] -> CriticalPair f -> Either (Model f) [CriticalPair f]
groundJoinFromMaybe config eqns idx Nothing = groundJoin config eqns idx
groundJoinFromMaybe config eqns idx (Just model) = groundJoinFrom config eqns idx model

{-# INLINEABLE valid #-}
valid :: Function f => Model f -> Reduction f -> Bool
valid model red =
  and [ reducesInModel model rule sub
      | Step _ rule sub <- steps red ]

optimise :: a -> (a -> [a]) -> (a -> Bool) -> a
optimise x f p =
  case filter p (f x) of
    y:_ -> optimise y f p
    _   -> x
