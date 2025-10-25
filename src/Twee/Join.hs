-- | Tactics for joining critical pairs.
{-# LANGUAGE FlexibleContexts, BangPatterns, RecordWildCards, TypeFamilies, ScopedTypeVariables #-}
module Twee.Join where

import Twee.Base
import Twee.Rule
import Twee.Equation
import qualified Twee.Proof as Proof
import Twee.CP hiding (Config)
import Twee.Constraints hiding (funs)
import qualified Twee.Index as Index
import Twee.Index(Index)
import Twee.Rule.Index(RuleIndex(..))
import Twee.Utils
import Data.Maybe
import Data.Either
import Data.Ord
import qualified Data.Map.Strict as Map

data Config =
  Config {
    cfg_ground_join :: !Bool,
    cfg_use_connectedness_standalone :: !Bool,
    cfg_use_connectedness_in_ground_joining :: !Bool,
    cfg_set_join :: !Bool,
    cfg_ground_join_limit :: !Int,
    cfg_ground_join_incomplete_limit :: !Int }

defaultConfig :: Config
defaultConfig =
  Config {
    cfg_ground_join = True,
    cfg_use_connectedness_standalone = True,
    cfg_use_connectedness_in_ground_joining = False,
    cfg_set_join = False,
    cfg_ground_join_limit = maxBound,
    cfg_ground_join_incomplete_limit = maxBound }

{-# INLINEABLE joinCriticalPair #-}
joinCriticalPair ::
  (Function f, Has a (Rule f)) =>
  Config ->
  (Index f (Equation f), Index f (Rule f)) -> RuleIndex f a ->
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
  case allSteps config eqns idx cp of
    Nothing ->
      Right (Nothing, [])
    _ | cfg_set_join config &&
        not (null $ Map.intersection
          (normalForms (rewrite reduces (index_all idx)) (Map.singleton t []))
          (normalForms (rewrite reduces (index_all idx)) (Map.singleton u []))) ->
      Right (Just cp, [])
    Just cp ->
      case groundJoinFromMaybe config 0 eqns idx mmodel (branches (And [])) cp of
        (_, Left model) -> Left (cp, model)
        (_, Right (mcp, cps)) -> Right (mcp, cps)

{-# INLINEABLE step1 #-}
{-# INLINEABLE step2 #-}
{-# INLINEABLE step3 #-}
{-# INLINEABLE allSteps #-}
step1, step2, step3, allSteps ::
  (Function f, Has a (Rule f)) =>
  Config -> (Index f (Equation f), Index f (Rule f)) -> RuleIndex f a -> CriticalPair f -> Maybe (CriticalPair f)
checkOrder :: Function f => CriticalPair f -> Maybe (CriticalPair f)
allSteps config eqns idx cp =
  step1 config eqns idx cp >>=
  step2 config eqns idx >>=
  checkOrder >>=
  step3 config eqns idx
checkOrder cp
  | tooBig cp = Nothing
  | otherwise = Just cp
  where
    tooBig CriticalPair{cp_top = Just top, cp_eqn = t :=: u} =
      lessEq top t || lessEq top u
    tooBig _ = False
step1 cfg eqns idx = joinWith cfg eqns idx (\t u -> normaliseWith (const True) (rewrite (ok t u) (index_oriented idx)) t)
  where
    --ok _ _ = reducesOriented
   ok t u rule sub = reducesOriented rule sub && unorient rule `simplerThan` (t :=: u)
step2 cfg eqns idx = joinWith cfg eqns idx (\t u -> normaliseWith (const True) (rewrite (ok t u) (index_all idx)) t)
  where
    --ok _ _ = reduces
    ok t u rule sub = reduces rule sub && unorient rule `simplerThan` (t :=: u)
step3 cfg@Config{..} eqns idx cp
  | not cfg_use_connectedness_standalone = Just cp
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
      joinWith cfg eqns idx (\t u -> normaliseWith (`lessThan` top) (rewrite (ok t u) (index_all idx)) t) cp

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
  (Function f, Has a (Rule f)) =>
  Config -> (Index f (Equation f), Index f (Rule f)) -> RuleIndex f a -> (Term f -> Term f -> Reduction f) -> CriticalPair f -> Maybe (CriticalPair f)
joinWith Config{..} eqns idx reduce cp@CriticalPair{cp_eqn = lhs :=: rhs, ..}
  | subsumed eqns idx eqn = Nothing
  | otherwise =
    Just cp {
      cp_eqn = eqn,
      cp_proof =
        Proof.symm (reductionProof lhs lred) `Proof.trans`
        cp_proof `Proof.trans`
        reductionProof rhs rred }
  where
    lred = reduce lhs rhs
    rred = reduce rhs lhs
    eqn = result lhs lred :=: result rhs rred

{-# INLINEABLE subsumed #-}
subsumed ::
  (Has a (Rule f), Function f) =>
  (Index f (Equation f), Index f (Rule f)) -> RuleIndex f a -> Equation f -> Bool
subsumed (eqns, complete) idx (t :=: u)
  | t == u = True
  | norm t == norm u = True
  | otherwise = subsumed1 eqns idx (t :=: u)
  where
    norm t
      | Index.null complete = t
      | otherwise = result t $ normaliseWith (const True) (rewrite reducesSkolem complete) t
subsumed1 eqns idx (t :=: u)
  | t == u = True
  | or [ rhs rule == u | rule <- Index.lookup t (index_all idx) ] = True
  | or [ rhs rule == t | rule <- Index.lookup u (index_all idx) ] = True
    -- No need to do this symmetrically because addJoinable adds
    -- both orientations of each equation
  | or [ u == subst sub u'
       | (sub, _ :=: u') <- Index.matches t eqns ] = True
subsumed1 eqns idx (App f ts :=: App g us)
  | f == g =
    let
      sub Nil Nil = True
      sub (Cons t ts) (Cons u us) =
        subsumed1 eqns idx (t :=: u) && sub ts us
      sub _ _ = error "Function used with multiple arities"
    in
      sub ts us
subsumed1 _ _ _ = False

{-# INLINEABLE groundJoin #-}
groundJoin ::
  (Function f, Has a (Rule f)) =>
  Config -> Int -> (Index f (Equation f), Index f (Rule f)) -> RuleIndex f a -> [Branch f] -> CriticalPair f -> (Int, Either (Model f) (Maybe (CriticalPair f), [CriticalPair f]))
groundJoin config ticks _ _ _ cp
  | ticks >= cfg_ground_join_incomplete_limit config =
    (ticks, Right (Just cp, []))
groundJoin config ticks eqns idx ctx cp@CriticalPair{cp_eqn = t :=: u, ..} =
  case partitionEithers (map (solve (usort (atoms t ++ atoms u))) ctx) of
    ([], instances) ->
      let cps = [ subst sub cp | sub <- instances ] in
      (ticks, Right (Just cp, usortBy (comparing (order . cp_eqn)) cps))
    (model:_, _) ->
      groundJoinFrom config (ticks+1) eqns idx model ctx cp

{-# INLINEABLE groundJoinFrom #-}
groundJoinFrom ::
  (Function f, Has a (Rule f)) =>
  Config -> Int -> (Index f (Equation f), Index f (Rule f)) -> RuleIndex f a -> Model f -> [Branch f] -> CriticalPair f -> (Int, Either (Model f) (Maybe (CriticalPair f), [CriticalPair f]))
groundJoinFrom config@Config{..} ticks eqns idx model ctx cp@CriticalPair{cp_eqn = t :=: u, ..}
  | ticks >= cfg_ground_join_limit || not cfg_ground_join = (ticks, Left model)
  | modelOK model && isJust (allSteps config' eqns idx cp { cp_eqn = t' :=: u' }) = (ticks, Left model)
  | otherwise =
      let
        model'
          | modelOK model =
            optimise weakenModel (\m -> modelOK m && isNothing (allSteps config' eqns idx cp { cp_eqn = result t (normaliseIn m t u) :=: result u (normaliseIn m u t) })) $
            optimise weakenModel (\m -> modelOK m && (valid m nt && valid m nu)) model
          | otherwise =
            optimise weakenModel (not . modelOK) model

        diag [] = Or []
        diag (r:rs) = negateFormula r ||| (weaken r &&& diag rs)
        weaken (LessEq t u) = Less t u
        weaken x = x
        ctx' = formAnd (diag (modelToLiterals model')) ctx in

      case groundJoin config ticks eqns idx ctx' cp of
        (ticks', Right (_, cps)) | not (modelOK model) ->
          (ticks', Right (Nothing, cps))
        res -> res
  where
    config' = config{cfg_use_connectedness_standalone = False}
    normaliseIn m t u =
      case cp_top of
        Just top | cfg_use_connectedness_in_ground_joining ->
          normaliseWith (connectedIn m top) (rewrite (ok t u model) (index_all idx)) t
        _ -> normaliseWith (const True) (rewrite (ok t u m) (index_all idx)) t
    ok t u m rule sub =
      case cp_top of
        Just top | cfg_use_connectedness_in_ground_joining ->
          reducesWith lessEqSkolemModel rule sub &&
          unorient rule `simplerThan` (t :=: u)
        _ ->
          reducesInModel m rule sub &&
          unorient rule `simplerThan` (t :=: u)
    connectedIn m top t =
      lessIn m t top == Just Strict
    lessEqSkolemModel t u =
      lessEqSkolem (subst reorderVars t) (subst reorderVars u)
    reorderVars x =
      var $
      case modelVarValue model x of
        Nothing -> V (var_id x + firstUnusedVar)
        Just y -> y
    firstUnusedVar = modelVarMaxBound model

    nt = normaliseIn model t u
    nu = normaliseIn model u t
    t' = result t nt
    u' = result u nu

    modelOK m =
      case cp_top of
        Nothing -> True
        Just top ->
          isNothing (lessIn m top t) && isNothing (lessIn m top u)

{-# INLINEABLE groundJoinFromMaybe #-}
groundJoinFromMaybe ::
  (Function f, Has a (Rule f)) =>
  Config -> Int -> (Index f (Equation f), Index f (Rule f)) -> RuleIndex f a -> Maybe (Model f) -> [Branch f] -> CriticalPair f -> (Int, Either (Model f) (Maybe (CriticalPair f), [CriticalPair f]))
groundJoinFromMaybe config ticks eqns idx Nothing = groundJoin config ticks eqns idx
groundJoinFromMaybe config ticks eqns idx (Just model) = groundJoinFrom config ticks eqns idx model

{-# INLINEABLE valid #-}
valid :: Function f => Model f -> Reduction f -> Bool
valid model red =
  and [ reducesInModel model (subst sub rule) emptySubst
      | (rule, sub) <- red ]

optimise :: (a -> [a]) -> (a -> Bool) -> a -> a
optimise f p x =
  case filter p (f x) of
    y:_ -> optimise f p y
    _   -> x
