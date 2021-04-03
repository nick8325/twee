-- | The main prover loop.
{-# LANGUAGE RecordWildCards, MultiParamTypeClasses, GADTs, BangPatterns, OverloadedStrings, ScopedTypeVariables, GeneralizedNewtypeDeriving, PatternGuards, TypeFamilies #-}
module Twee where

import Twee.Base
import Twee.Rule hiding (normalForms)
import qualified Twee.Rule as Rule
import Twee.Equation
import qualified Twee.Proof as Proof
import Twee.Proof(Axiom(..), Proof(..), Derivation, ProvedGoal(..), provedGoal, certify, derivation)
import Twee.CP hiding (Config)
import qualified Twee.CP as CP
import Twee.Join hiding (Config, defaultConfig)
import qualified Twee.Join as Join
import qualified Twee.Rule.Index as RuleIndex
import Twee.Rule.Index(RuleIndex(..))
import qualified Twee.Index as Index
import Twee.Index(Index)
import Twee.Constraints
import Twee.Utils
import Twee.Task
import qualified Twee.PassiveQueue as Queue
import Twee.PassiveQueue(Queue, Passive(..))
import qualified Data.IntMap.Strict as IntMap
import Data.IntMap(IntMap)
import Data.Maybe
import Data.List
import Data.Function
import qualified Data.Map.Strict as Map
import Data.Map(Map)
import Data.Int
import Data.Ord
import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import qualified Control.Monad.Trans.State.Strict as StateM
import qualified Data.IntSet as IntSet
import Data.IntSet(IntSet)

----------------------------------------------------------------------
-- * Configuration and prover state.
----------------------------------------------------------------------

-- | The prover configuration.
data Config f =
  Config {
    cfg_accept_term            :: Maybe (Term f -> Bool),
    cfg_max_critical_pairs     :: Int64,
    cfg_max_cp_depth           :: Int,
    cfg_simplify               :: Bool,
    cfg_renormalise_percent    :: Int,
    cfg_cp_sample_size         :: Int,
    cfg_renormalise_threshold  :: Int,
    cfg_set_join_goals         :: Bool,
    cfg_always_simplify        :: Bool,
    cfg_complete_subsets       :: Bool,
    cfg_critical_pairs         :: CP.Config,
    cfg_join                   :: Join.Config,
    cfg_proof_presentation     :: Proof.Config f }

-- | The prover state.
data State f =
  State {
    st_rules          :: !(RuleIndex f (Rule f)),
    st_active_ids     :: !(IntMap (Active f)),
    st_joinable       :: !(Index f (Equation f)),
    st_goals          :: ![Goal f],
    st_queue          :: !(Queue Params),
    st_next_active    :: {-# UNPACK #-} !Id,
    st_considered     :: {-# UNPACK #-} !Int64,
    st_simplified_at  :: {-# UNPACK #-} !Id,
    st_cp_sample      :: ![Maybe (Overlap (Active f) f)],
    st_cp_next_sample :: ![(Integer, Int)],
    st_num_cps        :: !Integer,
    st_not_complete   :: !IntSet,
    st_complete       :: !(Index f (Rule f)),
    st_messages_rev   :: ![Message f] }

-- | The default prover configuration.
defaultConfig :: Config f
defaultConfig =
  Config {
    cfg_accept_term = Nothing,
    cfg_max_critical_pairs = maxBound,
    cfg_max_cp_depth = maxBound,
    cfg_simplify = True,
    cfg_renormalise_percent = 5,
    cfg_renormalise_threshold = 20,
    cfg_cp_sample_size = 100,
    cfg_set_join_goals = True,
    cfg_always_simplify = False,
    cfg_complete_subsets = False,
    cfg_critical_pairs = CP.defaultConfig,
    cfg_join = Join.defaultConfig,
    cfg_proof_presentation = Proof.defaultConfig }

-- | Does this configuration run the prover in a complete mode?
configIsComplete :: Config f -> Bool
configIsComplete Config{..} =
  isNothing (cfg_accept_term) &&
  cfg_max_critical_pairs == maxBound &&
  cfg_max_cp_depth == maxBound

-- | The initial state.
initialState :: Config f -> State f
initialState Config{..} =
  State {
    st_rules = RuleIndex.empty,
    st_active_ids = IntMap.empty,
    st_joinable = Index.empty,
    st_goals = [],
    st_queue = Queue.empty,
    st_next_active = 1,
    st_considered = 0,
    st_simplified_at = 1,
    st_cp_sample = [],
    st_cp_next_sample = reservoir cfg_cp_sample_size,
    st_num_cps = 0,
    st_not_complete = IntSet.empty,
    st_complete = Index.empty,
    st_messages_rev = [] }

----------------------------------------------------------------------
-- * Messages.
----------------------------------------------------------------------

-- | A message which is produced by the prover when something interesting happens.
data Message f =
    -- | A new rule.
    NewActive !(Active f)
    -- | A new joinable equation.
  | NewEquation !(Equation f)
    -- | A rule was deleted.
  | DeleteActive !(Active f)
    -- | The CP queue was simplified.
  | SimplifyQueue
    -- | All except these axioms are complete (with a suitable-chosen subset of the rules).
  | NotComplete !IntSet
    -- | The rules were reduced wrt each other.
  | Interreduce
    -- | Status update: how many queued critical pairs there are.
  | Status !Int

instance Function f => Pretty (Message f) where
  pPrint (NewActive rule) = pPrint rule
  pPrint (NewEquation eqn) =
    text "  (hard)" <+> pPrint eqn
  pPrint (DeleteActive rule) =
    text "  (delete rule " <#> pPrint (active_id rule) <#> text ")"
  pPrint SimplifyQueue =
    text "  (simplifying queued critical pairs...)"
  pPrint (NotComplete ax) =
    case IntSet.toList ax of
      [n] ->
        text "  (axiom" <+> pPrint n <+> "is not completed yet)"
      xs ->
        text "  (axioms" <+> text (show xs) <+> "are not completed yet)"
  pPrint Interreduce =
    text "  (simplifying rules with respect to one another...)"
  pPrint (Status n) =
    text "  (" <#> pPrint n <+> text "queued critical pairs)"

-- | Emit a message.
message :: PrettyTerm f => Message f -> State f -> State f
message !msg state@State{..} =
  state { st_messages_rev = msg:st_messages_rev }

-- | Forget about all emitted messages.
clearMessages :: State f -> State f
clearMessages state@State{..} =
  state { st_messages_rev = [] }

-- | Get all emitted messages.
messages :: State f -> [Message f]
messages state = reverse (st_messages_rev state)

----------------------------------------------------------------------
-- * The CP queue.
----------------------------------------------------------------------

data Params
instance Queue.Params Params where
  type Score Params = Int
  type Id Params = Id
  type PackedId Params = Int32
  type PackedScore Params = Int32
  packScore _ = fromIntegral
  unpackScore _ = fromIntegral
  packId _ = fromIntegral
  unpackId _ = fromIntegral

-- | Compute all critical pairs from a rule.
{-# INLINEABLE makePassives #-}
{-# SCC makePassives #-}
makePassives :: Function f => Config f -> State f -> Active f -> [Passive Params]
makePassives Config{..} State{..} rule =
-- XXX factor out depth calculation
  [ Passive (fromIntegral (score cfg_critical_pairs (succ (the rule1 `max` the rule2)) o)) (active_id rule1) (active_id rule2) (packHow (overlap_how o))
  | ok rule,
    o@Overlap{overlap_rule1 = rule1, overlap_rule2 = rule2} <- overlaps (index_oriented st_rules) (filter ok rules) rule ]
  where
    rules = IntMap.elems st_active_ids
    ok rule = the rule < Depth cfg_max_cp_depth

-- | Turn a Passive back into an overlap.
-- Doesn't try to simplify it.
{-# INLINEABLE findPassive #-}
{-# SCC findPassive #-}
findPassive :: forall f. Function f => State f -> Passive Params -> Maybe (Overlap (Active f) f)
findPassive State{..} Passive{..} = do
  rule1 <- IntMap.lookup (fromIntegral passive_rule1) st_active_ids
  rule2 <- IntMap.lookup (fromIntegral passive_rule2) st_active_ids
  overlapAt (unpackHow passive_pos) rule1 rule2
    (renameAvoiding (the rule2 :: Rule f) (the rule1)) (the rule2)

-- | Renormalise a queued Passive.
{-# INLINEABLE simplifyPassive #-}
{-# SCC simplifyPassive #-}
simplifyPassive :: Function f => Config f -> State f -> Passive Params -> Maybe (Passive Params)
simplifyPassive Config{..} state@State{..} passive = do
  overlap <- findPassive state passive
  overlap <- simplifyOverlap (index_oriented st_rules) overlap
  let r1 = overlap_rule1 overlap
      r2 = overlap_rule2 overlap
  return passive {
    passive_score = fromIntegral $
      fromIntegral (passive_score passive) `intMin`
      -- XXX factor out depth calculation
      score cfg_critical_pairs (succ (the r1 `max` the r2)) overlap }

-- | Check if we should renormalise the queue.
{-# INLINEABLE shouldSimplifyQueue #-}
shouldSimplifyQueue :: Function f => Config f -> State f -> Bool
shouldSimplifyQueue Config{..} State{..} =
  length (filter isNothing st_cp_sample) * 100 >= cfg_renormalise_threshold * cfg_cp_sample_size

-- | Renormalise the entire queue.
{-# INLINEABLE simplifyQueue #-}
{-# SCC simplifyQueue #-}
simplifyQueue :: Function f => Config f -> State f -> State f
simplifyQueue config state =
  resetSample config state { st_queue = simp (st_queue state) }
  where
    simp =
      Queue.mapMaybe (simplifyPassive config state)

-- | Enqueue a set of critical pairs.
{-# INLINEABLE enqueue #-}
{-# SCC enqueue #-}
enqueue :: Function f => State f -> Id -> [Passive Params] -> State f
enqueue state rule passives =
  state { st_queue = Queue.insert rule passives (st_queue state) }

-- | Dequeue a critical pair.
--
-- Also takes care of:
--
--   * removing any orphans from the head of the queue
--   * ignoring CPs that are too big
{-# INLINEABLE dequeue #-}
{-# SCC dequeue #-}
dequeue :: Function f => Config f -> State f -> (Maybe (Info, CriticalPair f, Active f, Active f), State f)
dequeue Config{..} state@State{..} =
  case deq 0 st_queue of
    -- Explicitly make the queue empty, in case it e.g. contained a
    -- lot of orphans
    Nothing -> (Nothing, state { st_queue = Queue.empty })
    Just (overlap, n, queue) ->
      (Just overlap,
       state { st_queue = queue, st_considered = st_considered + n })
  where
    deq !n queue = do
      (passive, queue) <- Queue.removeMin queue
      case findPassive state passive of
        Just (overlap@Overlap{overlap_eqn = t :=: u, overlap_rule1 = rule1, overlap_rule2 = rule2})
          | fromMaybe True (cfg_accept_term <*> pure t),
            fromMaybe True (cfg_accept_term <*> pure u),
            cp <- makeCriticalPair overlap ->
              return ((combineInfo (active_info rule1) (active_info rule2), cp, rule1, rule2), n+1, queue)
        _ -> deq (n+1) queue

    combineInfo i1 i2 =
      Info {
        -- XXX factor out depth calculation
        info_depth = succ (max (info_depth i1) (info_depth i2)),
        info_max = IntSet.union (info_max i1) (info_max i2) }

----------------------------------------------------------------------
-- * Active rewrite rules.
----------------------------------------------------------------------

data Active f =
  Active {
    active_id    :: {-# UNPACK #-} !Id,
    active_info  :: {-# UNPACK #-} !Info,
    active_rule  :: {-# UNPACK #-} !(Rule f),
    active_top   :: !(Maybe (Term f)),
    active_proof :: {-# UNPACK #-} !(Proof f),
    -- A model in which the rule is false (used when reorienting)
    active_model :: !(Model f),
    active_positions :: !(Positions2 f) }

active_cp :: Active f -> CriticalPair f
active_cp Active{..} =
  CriticalPair {
    cp_eqn = unorient active_rule,
    cp_top = active_top,
    cp_proof = derivation active_proof }

activeRules :: Active f -> [Rule f]
activeRules Active{..} =
  case active_positions of
    ForwardsPos _ -> [active_rule]
    BothPos _ _ -> [active_rule, backwards active_rule]

data Info =
  Info {
    info_depth :: {-# UNPACK #-} !Depth,
    info_max   :: !IntSet }

instance Eq (Active f) where
  (==) = (==) `on` active_id

instance Function f => Pretty (Active f) where
  pPrint Active{..} =
    pPrint active_id <#> text "." <+> pPrint (canonicalise active_rule)

instance Has (Active f) Id where the = active_id
instance Has (Active f) Depth where the = info_depth . active_info
instance f ~ g => Has (Active f) (Rule g) where the = active_rule
instance f ~ g => Has (Active f) (Positions2 g) where the = active_positions

-- Add a new active.
{-# INLINEABLE addActive #-}
{-# SCC addActive #-}
addActive :: Function f => Config f -> State f -> (Id -> Active f) -> State f
addActive config state@State{..} active0 =
  let
    active@Active{..} = active0 st_next_active
    state' =
      message (NewActive active) $
      addActiveOnly state{st_next_active = st_next_active+1} active
  in if subsumed (st_joinable, st_complete) st_rules (unorient active_rule) then
    state
  else
    normaliseGoals config $
    enqueueRule state' active
  where
    enqueueRule state rule =
      sample config (length passives) passives $
      enqueue state (the rule) passives
      where
        passives = makePassives config state rule

-- Update the list of sampled critical pairs.
{-# INLINEABLE sample #-}
sample :: Function f => Config f -> Int -> [Passive Params] -> State f -> State f
sample cfg m passives state@State{st_cp_next_sample = ((n, pos):rest), ..}
  | idx < fromIntegral m =
    sample cfg m passives state {
      st_cp_next_sample = rest,
      st_cp_sample =
        take pos st_cp_sample ++
        [find (passives !! fromIntegral idx)] ++
        drop (pos+1) st_cp_sample }
  | otherwise = state{st_num_cps = st_num_cps + fromIntegral m}
  where
    idx = n - st_num_cps
    find passive = do
      overlap <- findPassive state passive
      simplifyOverlap (index_oriented st_rules) overlap

-- Reset the list of sampled critical pairs.
{-# INLINEABLE resetSample #-}
resetSample :: Function f => Config f -> State f -> State f
resetSample cfg@Config{..} state@State{..} =
  foldl' sample1 state' (Queue.toList st_queue)
  where
    state' =
      state {
        st_num_cps = 0,
        st_cp_next_sample = reservoir cfg_cp_sample_size,
        st_cp_sample = [] }

    sample1 state (n, passives) = sample cfg n passives state

-- Simplify the sampled critical pairs.
-- (A sampled critical pair is replaced with Nothing if it can be
-- simplified.)
{-# INLINEABLE simplifySample #-}
simplifySample :: Function f => State f -> State f
simplifySample state@State{..} =
  state{st_cp_sample = map (>>= simp) st_cp_sample}
  where
    simp overlap = do
      overlap' <- simplifyOverlap (index_oriented st_rules) overlap
      guard (overlap_eqn overlap == overlap_eqn overlap')
      return overlap

-- Add an active without generating critical pairs. Used in interreduction.
{-# INLINEABLE addActiveOnly #-}
addActiveOnly :: Function f => State f -> Active f -> State f
addActiveOnly state@State{..} active@Active{..} =
  state {
    st_rules = foldl' insertRule st_rules (activeRules active),
    st_active_ids = IntMap.insert (fromIntegral active_id) active st_active_ids }
  where
    insertRule rules rule =
      RuleIndex.insert (lhs rule) rule rules

-- Delete an active. Used in interreduction, not suitable for general use.
{-# INLINE deleteActive #-}
deleteActive :: Function f => State f -> Active f -> State f
deleteActive state@State{..} active@Active{..} =
  state {
    st_rules = foldl' deleteRule st_rules (activeRules active),
    st_active_ids = IntMap.delete (fromIntegral active_id) st_active_ids }
  where
    deleteRule rules rule =
      RuleIndex.delete (lhs rule) rule rules

-- Try to join a critical pair.
{-# INLINEABLE consider #-}
consider :: Function f => Config f -> State f -> Info -> CriticalPair f -> State f
consider config state info cp =
  considerUsing (st_rules state) config state info cp

-- Try to join a critical pair, but using a different set of critical
-- pairs for normalisation.
{-# INLINEABLE considerUsing #-}
{-# SCC considerUsing #-}
considerUsing ::
  Function f =>
  RuleIndex f (Rule f) -> Config f -> State f -> Info -> CriticalPair f -> State f
considerUsing rules config@Config{..} state@State{..} info cp0 =
  -- Important to canonicalise the rule so that we don't get
  -- bigger and bigger variable indices over time
  let cp = canonicalise cp0 in
  case joinCriticalPair cfg_join (st_joinable, st_complete) rules Nothing cp of
    Right (mcp, cps) ->
      let
        state' = foldl' (\state cp -> considerUsing rules config state info cp) state cps
      in case mcp of
        Just cp -> addJoinable state' (cp_eqn cp)
        Nothing -> state'

    Left (cp, model) ->
      foldl' (\state cp -> addCP config model state info cp) state (split cp)

{-# INLINEABLE addCP #-}
addCP :: Function f => Config f -> Model f -> State f -> Info -> CriticalPair f -> State f
addCP config model state@State{..} info CriticalPair{..} =
  let
    pf = certify cp_proof
    rule = orient cp_eqn pf
  in
  addActive config state $ \n ->
  Active {
    active_id = n,
    active_info = info,
    active_rule = rule,
    active_model = model,
    active_top = cp_top,
    active_proof = pf,
    active_positions = positionsRule rule }

-- Add a new equation.
{-# INLINEABLE addAxiom #-}
addAxiom :: Function f => Config f -> State f -> Axiom f -> State f
addAxiom config state axiom =
  consider config state
    Info { info_depth = 0, info_max = IntSet.fromList [axiom_number axiom | cfg_complete_subsets config] }
    CriticalPair {
      cp_eqn = axiom_eqn axiom,
      cp_top = Nothing,
      cp_proof = Proof.axiom axiom }

-- Record an equation as being joinable.
{-# INLINEABLE addJoinable #-}
addJoinable :: Function f => State f -> Equation f -> State f
addJoinable state eqn@(t :=: u) =
  message (NewEquation eqn) $
  state {
    st_joinable =
      Index.insert t (t :=: u) $
      Index.insert u (u :=: t) (st_joinable state) }

-- Find a confluent subset of the rules.
{-# INLINEABLE checkCompleteness #-}
checkCompleteness :: Function f => Config f -> State f -> State f
checkCompleteness _ state@State{..} | st_simplified_at == st_next_active = state
checkCompleteness _config state =
  state { st_not_complete = excluded,
          st_complete = Index.fromListWith lhs rules }
  where
    maxSet s = if IntSet.null s then minBound else IntSet.findMax s
    maxN = maximum [maxSet (info_max (active_info r)) | r <- IntMap.elems (st_active_ids state)]
    excluded = go IntSet.empty
    go excl
      | m > maxN = excl
      | otherwise = go (IntSet.insert m excl)
      where
        m = bound excl

    bound excl = minimum . map (passiveMax excl) . concatMap snd . Queue.toList $ st_queue state

    passiveMax excl p = fromMaybe maxBound $ do
      Overlap{overlap_rule1 = r1, overlap_rule2 = r2} <- findPassive state p
      let s = info_max (active_info r1) `IntSet.union` info_max (active_info r2)
      guard (s `IntSet.disjoint` excl)
      (n, _) <- IntSet.maxView s
      return n
    rules = concatMap activeRules (filter ok (IntMap.elems (st_active_ids state)))
    ok r = info_max (active_info r) `IntSet.disjoint` excluded

-- Assume that all rules form a confluent rewrite system.
{-# INLINEABLE assumeComplete #-}
assumeComplete :: Function f => State f -> State f
assumeComplete state =
  state { st_not_complete = IntSet.empty,
          st_complete = Index.fromListWith lhs (concatMap activeRules (IntMap.elems (st_active_ids state))) }

-- For goal terms we store the set of all their normal forms.
-- Name and number are for information only.
data Goal f =
  Goal {
    goal_name         :: String,
    goal_number       :: Int,
    goal_eqn          :: Equation f,
    goal_expanded_lhs :: Map (Term f) (Derivation f),
    goal_expanded_rhs :: Map (Term f) (Derivation f),
    goal_lhs          :: Map (Term f) (Term f, Reduction f),
    goal_rhs          :: Map (Term f) (Term f, Reduction f) }
  deriving Show

-- Add a new goal.
{-# INLINEABLE addGoal #-}
addGoal :: Function f => Config f -> State f -> Goal f -> State f
addGoal config state@State{..} goal =
  normaliseGoals config state { st_goals = goal:st_goals }

-- Normalise all goals.
{-# INLINEABLE normaliseGoals #-}
normaliseGoals :: Function f => Config f -> State f -> State f
normaliseGoals Config{..} state@State{..} =
  state {
    st_goals =
      map (goalMap (nf (rewrite reduces (index_all st_rules)))) st_goals }
  where
    goalMap f goal@Goal{..} =
      goal { goal_lhs = f goal_lhs, goal_rhs = f goal_rhs }
    nf reduce goals
      | cfg_set_join_goals =
        let pair (t, red) = (fst (goals Map.! t), red) in
        Map.map pair $ Rule.normalForms reduce (Map.map snd goals)
      | otherwise =
        Map.fromList $
          [ (result t q, (u, r `trans` q))
          | (t, (u, r)) <- Map.toList goals,
            let q = Rule.normaliseWith (const True) reduce t ]

-- Recompute all normal forms of all goals. Starts from the original goal term.
-- Different from normalising all goals, because there may be an intermediate
-- term on one of the reduction paths which we can now rewrite in a different
-- way.
{-# INLINEABLE recomputeGoals #-}
recomputeGoals :: Function f => Config f -> State f -> State f
recomputeGoals config state =
  -- Make this strict so that newTask can time it correctly
  forceList (map goal_lhs (st_goals state')) `seq`
  forceList (map goal_rhs (st_goals state')) `seq`
  state'
  where
    state' =
      normaliseGoals config (state { st_goals = map resetGoal (st_goals state) })

    forceList [] = ()
    forceList (x:xs) = x `seq` forceList xs

resetGoal :: Goal f -> Goal f
resetGoal goal@Goal{..} =
  goal { goal_lhs = expansions goal_expanded_lhs,
         goal_rhs = expansions goal_expanded_rhs }
  where
    expansions m =
      Map.mapWithKey (\t _ -> (t, [])) m

-- Rewrite goal terms backwards using rewrite rules.
{-# INLINEABLE rewriteGoalsBackwards #-}
rewriteGoalsBackwards :: Function f => State f -> State f
rewriteGoalsBackwards state =
  state { st_goals = map backwardsGoal (st_goals state) }
  where
    backwardsGoal goal@Goal{..} =
      resetGoal goal {
        goal_expanded_lhs = backwardsMap goal_expanded_lhs,
        goal_expanded_rhs = backwardsMap goal_expanded_rhs }
    backwardsMap m =
      Map.fromList $
        Map.toList m ++
        [ (ruleResult t r, p `Proof.trans` q)
        | (t, p) <- Map.toList m,
          r <- backwardsTerm t,
          let q = ruleProof t r ]
    backwardsTerm t = do
      rule <- map the (Index.elems (RuleIndex.index_all (st_rules state)))
      guard (usort (vars (lhs rule)) == usort (vars (rhs rule)))
      [r] <- anywhere (tryRule (\_ _ -> True) (backwards rule)) t
      return r

-- Create a goal.
{-# INLINE goal #-}
goal :: Int -> String -> Equation f -> Goal f
goal n name (t :=: u) =
  Goal {
    goal_name = name,
    goal_number = n,
    goal_eqn = t :=: u,
    goal_expanded_lhs = Map.singleton t (Proof.Refl t),
    goal_expanded_rhs = Map.singleton u (Proof.Refl u),
    goal_lhs = Map.singleton t (t, []),
    goal_rhs = Map.singleton u (u, []) }

----------------------------------------------------------------------
-- Interreduction.
----------------------------------------------------------------------

-- Simplify all rules.
{-# INLINEABLE interreduce #-}
{-# SCC interreduce #-}
interreduce :: Function f => Config f -> State f -> State f
interreduce _ state@State{..} | st_simplified_at == st_next_active = state
interreduce config@Config{..} state =
  let
    state' =
      foldl' (interreduce1 config)
        -- Clear out st_joinable, since we don't know which
        -- equations have made use of each active.
        state { st_joinable = Index.empty, st_complete = Index.empty }
        (IntMap.elems (st_active_ids state))
    in state' { st_joinable = st_joinable state, st_complete = st_complete state, st_simplified_at = st_next_active state' }

{-# INLINEABLE interreduce1 #-}
interreduce1 :: Function f => Config f -> State f -> Active f -> State f
interreduce1 config@Config{..} state active@Active{..} =
  -- Exclude the active from the rewrite rules when testing
  -- joinability, otherwise it will be trivially joinable.
  case
    joinCriticalPair cfg_join
      (Index.empty, Index.empty) -- (st_joinable state)
      (st_rules (deleteActive state active))
      (Just active_model) (active_cp active)
  of
    Right (_, cps) ->
      flip (foldl' (\state cp -> consider config state active_info cp)) cps $
      message (DeleteActive active) $
      deleteActive state active
    Left (cp, model)
      | cp_eqn cp `simplerThan` cp_eqn (active_cp active) ->
        flip (foldl' (\state cp -> consider config state active_info cp)) (split cp) $
        message (DeleteActive active) $
        deleteActive state active
      | model /= active_model ->
        flip addActiveOnly active { active_model = model } $
        deleteActive state active
      | otherwise ->
        state

----------------------------------------------------------------------
-- The main loop.
----------------------------------------------------------------------

data Output m f =
  Output {
    output_message :: Message f -> m () }

{-# INLINE complete #-}
complete :: (Function f, MonadIO m) => Output m f -> Config f -> State f -> m (State f)
complete Output{..} config@Config{..} state =
  flip StateM.execStateT state $ do
    tasks <- sequence
      [newTask 10 (fromIntegral cfg_renormalise_percent / 100) $ do
         state <- StateM.get
         when (shouldSimplifyQueue config state) $ do
           lift $ output_message SimplifyQueue
           StateM.put $! simplifyQueue config state,
       newTask 1 0.02 $ do
         when cfg_complete_subsets $ do
           state <- StateM.get
           let !state' = checkCompleteness config state
           lift $ output_message (NotComplete (st_not_complete state'))
           StateM.put $! state',
       newTask 1 0.05 $ do
         when cfg_simplify $ do
           lift $ output_message Interreduce
           state <- StateM.get
           StateM.put $! simplifySample $! interreduce config state,
       newTask 1 0.02 $ do
          state <- StateM.get
          StateM.put $! recomputeGoals config state,
       newTask 60 0.01 $ do
          State{..} <- StateM.get
          let !n = Queue.queueSize st_queue
          lift $ output_message (Status n)]

    let
      loop = do
        progress <- StateM.state (complete1 config)
        when cfg_always_simplify $ do
          lift $ output_message Interreduce
          state <- StateM.get
          StateM.put $! simplifySample $! interreduce config state
        state <- StateM.get
        lift $ mapM_ output_message (messages state)
        StateM.put (clearMessages state)
        mapM_ checkTask tasks
        when progress loop

    loop

{-# INLINEABLE complete1 #-}
complete1 :: Function f => Config f -> State f -> (Bool, State f)
complete1 config@Config{..} state
  | st_considered state >= cfg_max_critical_pairs =
    (False, state)
  | solved state = (False, state)
  | otherwise =
    case dequeue config state of
      (Nothing, state) -> (False, state)
      (Just (info, overlap, _, _), state) ->
        (True, consider config state info overlap)

{-# INLINEABLE solved #-}
solved :: Function f => State f -> Bool
solved = not . null . solutions

-- Return whatever goals we have proved and their proofs.
{-# INLINEABLE solutions #-}
{-# SCC solutions #-}
solutions :: Function f => State f -> [ProvedGoal f]
solutions State{..} = do
  Goal{goal_lhs = ts, goal_rhs = us, ..} <- st_goals
  let sols = Map.keys (Map.intersection ts us)
  guard (not (null sols))
  let sol:_ = sols
  let t = ts Map.! sol
      u = us Map.! sol
      -- Strict so that we check the proof before returning a solution
      !p =
        Proof.certify $
          expandedProof goal_expanded_lhs t `Proof.trans`
          Proof.symm (expandedProof goal_expanded_rhs u)
  return (provedGoal goal_number goal_name p)
  where
    expandedProof m (t, red) =
      m Map.! t `Proof.trans` reductionProof t red

-- Return all current rewrite rules.
{-# INLINEABLE rules #-}
rules :: Function f => State f -> [Rule f]
rules = map active_rule . IntMap.elems . st_active_ids

----------------------------------------------------------------------
-- For code which uses twee as a library.
----------------------------------------------------------------------

{-# INLINEABLE completePure #-}
completePure :: Function f => Config f -> State f -> State f
completePure cfg state
  | progress = completePure cfg (clearMessages state')
  | otherwise = state'
  where
    (progress, state') = complete1 cfg state

{-# INLINEABLE normaliseTerm #-}
normaliseTerm :: Function f => State f -> Term f -> Reduction f
normaliseTerm State{..} t =
  normaliseWith (const True) (rewrite reduces (index_all st_rules)) t

{-# INLINEABLE normalForms #-}
normalForms :: Function f => State f -> Term f -> Map (Term f) (Reduction f)
normalForms State{..} t =
  Map.map snd $
  Rule.normalForms (rewrite reduces (index_all st_rules)) (Map.singleton t [])

{-# INLINEABLE simplifyTerm #-}
simplifyTerm :: Function f => State f -> Term f -> Term f
simplifyTerm State{..} t =
  simplify (index_oriented st_rules) t
