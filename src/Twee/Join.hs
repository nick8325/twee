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
import Data.Map(Map)

data Config =
  Config {
    cfg_ground_join :: !Bool,
    cfg_use_connectedness_standalone :: !Bool,
    cfg_use_connectedness_in_ground_joining :: !Bool,
    cfg_ac_handling :: !Bool,
    cfg_set_join :: !Bool }

defaultConfig :: Config
defaultConfig =
  Config {
    cfg_ground_join = True,
    cfg_use_connectedness_standalone = False,
    cfg_use_connectedness_in_ground_joining = True,
    cfg_ac_handling = False,
    cfg_set_join = False }

{-# INLINEABLE joinCriticalPair #-}
{-# SCC joinCriticalPair #-}
joinCriticalPair ::
  (Function f, Has a (Rule f)) =>
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
  case allSteps config eqns idx cp of
    Nothing ->
      Right (Nothing, [])
    _ | cfg_set_join config &&
        not (null $ Map.intersection
          (normalForms (rewrite reduces (index_all idx)) (Map.singleton t []))
          (normalForms (rewrite reduces (index_all idx)) (Map.singleton u []))) ->
      Right (Just cp, [])
    Just cp ->
      case groundJoinFromMaybe config eqns idx mmodel (branches (And [])) cp of
        Left model -> Left (cp, model)
        Right (mcp, cps) -> Right (mcp, cps)

{-# INLINEABLE step1 #-}
{-# INLINEABLE step2 #-}
{-# INLINEABLE step3 #-}
{-# INLINEABLE allSteps #-}
step1, step2, step3, allSteps ::
  (Function f, Has a (Rule f)) =>
  Config -> Index f (Equation f) -> RuleIndex f a -> CriticalPair f -> Maybe (CriticalPair f)
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
  Config -> Index f (Equation f) -> RuleIndex f a -> (Term f -> Term f -> Reduction f) -> CriticalPair f -> Maybe (CriticalPair f)
joinWith Config{..} eqns idx reduce cp@CriticalPair{cp_eqn = lhs :=: rhs, ..}
  | cfg_ac_handling && ac idx eqn = Nothing
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

{-# INLINEABLE ac #-}
ac ::
  forall a f.
  (Function f, Has a (Rule f)) =>
  RuleIndex f a -> Equation f -> Bool
ac idx (t :=: u) =
  not (is commRule t u) && not (is assocRule t u) && not (is assocRule u t) && not (is funnyRule t u) &&
  norm t == norm u
  where
    fs = usort (funs t ++ funs u)
    comm = find commRule
    assoc = find assocRule
    funny = find funnyRule
    all =
      Index.fromListWith (lhs . the) $ concat $ Map.elems $
      Map.intersectionWith (++) (fmap return comm) $
      Map.intersectionWith (++) (fmap return assoc) (fmap return funny)

    commRule f =
      build (app f [var x, var y]) :=:
      build (app f [var y, var x])
    assocRule f =
      build (app f [app f [var x, var y], var z]) :=:
      build (app f [var x, app f [var y, var z]])
    funnyRule f =
      build (app f [var x, app f [var y, var z]]) :=:
      build (app f [var y, app f [var x, var z]])

    is rule t@(App f _) u =
      isJust (matchMany [t0, u0] [t, u]) &&
      isJust (matchMany [t, u] [t0, u0])
      where
        t0 :=: u0 = rule f
    is _ _ _ = False

    find :: (Fun f -> Equation f) -> Map (Fun f) (Rule f)
    find rule =
      Map.fromList
        [ (f, subst sub r)
        | f <- fs,
          let t :=: u = rule f,
          r <- map the (Index.approxMatches t (index_all idx)),
          sub <- maybeToList (matchMany [lhs r, rhs r] [t, u]) ]

    x = V 0
    y = V 1
    z = V 2

    norm t = result t $ normaliseWith (const True) (rewrite reducesSkolem all) t

{-# INLINEABLE subsumed #-}
subsumed ::
  (Has a (Rule f)) =>
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
  (Function f, Has a (Rule f)) =>
  Config -> Index f (Equation f) -> RuleIndex f a -> [Branch f] -> CriticalPair f -> Either (Model f) (Maybe (CriticalPair f), [CriticalPair f])
groundJoin config eqns idx ctx cp@CriticalPair{cp_eqn = t :=: u, ..} =
  case partitionEithers (map (solve (usort (atoms t ++ atoms u))) ctx) of
    ([], instances) ->
      let cps = [ subst sub cp | sub <- instances ] in
      Right (Just cp, usortBy (comparing (canonicalise . order . cp_eqn)) cps)
    (model:_, _) ->
      groundJoinFrom config eqns idx model ctx cp

{-# INLINEABLE groundJoinFrom #-}
groundJoinFrom ::
  (Function f, Has a (Rule f)) =>
  Config -> Index f (Equation f) -> RuleIndex f a -> Model f -> [Branch f] -> CriticalPair f -> Either (Model f) (Maybe (CriticalPair f), [CriticalPair f])
groundJoinFrom config@Config{..} eqns idx model ctx cp@CriticalPair{cp_eqn = t :=: u, ..}
  | not cfg_ground_join = Left model
  | modelOK model && isJust (allSteps config' eqns idx cp { cp_eqn = t' :=: u' }) = Left model
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

      case groundJoin config eqns idx ctx' cp of
        Right (_, cps) | not (modelOK model) ->
          Right (Nothing, cps)
        res -> res
  where
    config' = config{cfg_use_connectedness_standalone = False}
    normaliseIn m t u =
      case cp_top of
        Just top | cfg_use_connectedness_in_ground_joining ->
          normaliseWith (connectedIn m top) (rewrite (ok t u model) (index_all idx)) t
        _ -> normaliseWith (const True) (rewrite (ok t u m) (index_all idx)) t
    ok t u m rule sub =
      reducesInModel m rule sub &&
      unorient rule `simplerThan` (t :=: u)
    connectedIn m top t =
      lessIn m t top == Just Strict

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
  Config -> Index f (Equation f) -> RuleIndex f a -> Maybe (Model f) -> [Branch f] -> CriticalPair f -> Either (Model f) (Maybe (CriticalPair f), [CriticalPair f])
groundJoinFromMaybe config eqns idx Nothing = groundJoin config eqns idx
groundJoinFromMaybe config eqns idx (Just model) = groundJoinFrom config eqns idx model

{-# INLINEABLE valid #-}
valid :: Function f => Model f -> Reduction f -> Bool
valid model red =
  and [ reducesInModel model rule emptySubst
      | rule <- red ]

optimise :: (a -> [a]) -> (a -> Bool) -> a -> a
optimise f p x =
  case filter p (f x) of
    y:_ -> optimise f p y
    _   -> x
