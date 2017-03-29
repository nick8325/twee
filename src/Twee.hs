{-# LANGUAGE RecordWildCards, MultiParamTypeClasses, GADTs, BangPatterns, OverloadedStrings, ScopedTypeVariables, GeneralizedNewtypeDeriving #-}
module Twee where

import Twee.Base
import Twee.Rule
import Twee.Equation
import qualified Twee.Proof as Proof
import Twee.Proof(Proof, Axiom(..), ProvedGoal(..), certify, derivation, symm)
import Twee.CP hiding (Config)
import qualified Twee.CP as CP
import Twee.Join hiding (Config, defaultConfig)
import qualified Twee.Join as Join
import qualified Twee.Index as Index
import Twee.Index(Index)
import Twee.Constraints
import Twee.Utils
import Twee.Task
import qualified Data.Heap as Heap
import Data.Heap(Heap)
import qualified Data.IntMap.Strict as IntMap
import Data.IntMap(IntMap)
import Data.Maybe
import Data.List
import Data.Function
import qualified Data.Set as Set
import Data.Set(Set)
import Text.Printf
import Data.Int
import Data.Ord
import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import qualified Control.Monad.Trans.State.Strict as StateM

----------------------------------------------------------------------
-- Configuration and prover state.
----------------------------------------------------------------------

data Config =
  Config {
    cfg_max_term_size          :: Int,
    cfg_max_critical_pairs     :: Int,
    cfg_simplify               :: Bool,
    cfg_improve_critical_pairs :: Bool,
    cfg_critical_pairs         :: CP.Config,
    cfg_join                   :: Join.Config,
    cfg_proof_presentation     :: Proof.Config }

data State f =
  State {
    st_oriented_rules :: !(Index f (ActiveRule f)),
    st_rules          :: !(Index f (ActiveRule f)),
    st_active_ids     :: !(IntMap (Active f)),
    st_rule_ids       :: !(IntMap (ActiveRule f)),
    st_joinable       :: !(Index f (Equation f)),
    st_goals          :: ![Goal f],
    st_queue          :: !(Heap (Passive f)),
    st_next_active    :: {-# UNPACK #-} !Id,
    st_considered     :: {-# UNPACK #-} !Int,
    st_messages_rev   :: ![Message f] }

defaultConfig :: Config
defaultConfig =
  Config {
    cfg_max_term_size = maxBound,
    cfg_max_critical_pairs = maxBound,
    cfg_simplify = True,
    cfg_improve_critical_pairs = True,
    cfg_critical_pairs =
      CP.Config {
        cfg_lhsweight = 2,
        cfg_rhsweight = 1,
        cfg_funweight = 4,
        cfg_varweight = 3 },
    cfg_join = Join.defaultConfig,
    cfg_proof_presentation = Proof.defaultConfig }

initialState :: State f
initialState =
  State {
    st_oriented_rules = Index.Nil,
    st_rules = Index.Nil,
    st_active_ids = IntMap.empty,
    st_rule_ids = IntMap.empty,
    st_joinable = Index.Nil,
    st_goals = [],
    st_queue = Heap.empty,
    st_next_active = 1,
    st_considered = 0,
    st_messages_rev = [] }

----------------------------------------------------------------------
-- Messages.
----------------------------------------------------------------------

data Message f =
    NewActive !(Active f)
  | NewEquation !(Equation f)
  | DeleteActive !(Active f)
  | SimplifyQueue
  | Interreduce

instance Function f => Pretty (Message f) where
  pPrint (NewActive rule) = pPrint rule
  pPrint (NewEquation eqn) =
    text "  (hard)" <+> pPrint eqn
  pPrint (DeleteActive rule) =
    text "  (delete rule " <> pPrint (active_id rule) <> text ")"
  pPrint SimplifyQueue =
    text "  (simplifying queued critical pairs...)"
  pPrint Interreduce =
    text "  (simplifying rules with respect to one another...)"

message :: PrettyTerm f => Message f -> State f -> State f
message !msg state@State{..} =
  state { st_messages_rev = msg:st_messages_rev }

clearMessages :: State f -> State f
clearMessages state@State{..} =
  state { st_messages_rev = [] }

messages :: State f -> [Message f]
messages state = reverse (st_messages_rev state)

----------------------------------------------------------------------
-- The CP queue.
----------------------------------------------------------------------

data Passive f =
  Passive {
    passive_score :: {-# UNPACK #-} !Int32,
    passive_rule1 :: {-# UNPACK #-} !RuleId,
    passive_rule2 :: {-# UNPACK #-} !RuleId,
    passive_pos   :: {-# UNPACK #-} !Int32 }
  deriving (Eq, Show)

instance Ord (Passive f) where
  compare = comparing f
    where
      f Passive{..} =
        (passive_score,
         intMax (fromIntegral passive_rule1) (fromIntegral passive_rule2),
         passive_rule1,
         passive_rule2,
         passive_score)

-- Compute all critical pairs from a rule and condense into a Passive.
{-# INLINEABLE makePassive #-}
makePassive :: Function f => Config -> State f -> ActiveRule f -> [Passive f]
makePassive Config{..} State{..} rule =
  {-# SCC makePassive #-}
  [ Passive (fromIntegral (score cfg_critical_pairs o)) (rule_rid rule1) (rule_rid rule2) (fromIntegral (overlap_pos o))
  | (rule1, rule2, o) <- overlaps st_oriented_rules rules rule ]
  where
    rules = IntMap.elems st_rule_ids

-- Turn a Passive back into an overlap.
-- Doesn't try to simplify it.
{-# INLINEABLE findPassive #-}
findPassive :: forall f. Function f => Config -> State f -> Passive f -> Maybe (ActiveRule f, ActiveRule f, Overlap f)
findPassive Config{..} State{..} Passive{..} = {-# SCC findPassive #-} do
  rule1 <- IntMap.lookup (fromIntegral passive_rule1) st_rule_ids
  rule2 <- IntMap.lookup (fromIntegral passive_rule2) st_rule_ids
  overlap <-
    overlapAt (fromIntegral passive_pos)
      (renameAvoiding (the rule2 :: Rule f) (the rule1)) (the rule2)
  return (rule1, rule2, overlap)

-- Renormalise a queued Passive.
-- Orphaned passives get a score of 0.
{-# INLINEABLE simplifyPassive #-}
simplifyPassive :: Function f => Config -> State f -> Passive f -> Passive f
simplifyPassive config@Config{..} state@State{..} passive =
  {-# SCC simplifyPassive #-}
  fromMaybe passive { passive_score = 0 } $ do
    (_, _, overlap) <- findPassive config state passive
    overlap <- simplifyOverlap st_oriented_rules overlap
    return passive { passive_score = fromIntegral (score cfg_critical_pairs overlap) }

-- Renormalise the entire queue.
{-# INLINEABLE simplifyQueue #-}
simplifyQueue :: Function f => Config -> State f -> State f
simplifyQueue config state =
  {-# SCC simplifyQueue #-}
  state { st_queue = simp (st_queue state) }
  where
    simp = Heap.map (simplifyPassive config state)

-- Enqueue a critical pair.
{-# INLINEABLE enqueue #-}
enqueue :: Function f => State f -> Passive f -> State f
enqueue state passive =
  {-# SCC enqueue #-}
  state { st_queue = Heap.insert passive (st_queue state) }

-- Dequeue a critical pair.
-- Also takes care of:
--   * removing any orphans from the head of the queue
--   * splitting ManyCPs up as necessary
--   * ignoring CPs that are too big
{-# INLINEABLE dequeue #-}
dequeue :: Function f => Config -> State f -> (Maybe (CriticalPair f, ActiveRule f, ActiveRule f), State f)
dequeue config@Config{..} state@State{..} =
  {-# SCC dequeue #-}
  case deq 0 st_queue of
    -- Explicitly make the queue empty, in case it e.g. contained a
    -- lot of orphans
    Nothing -> (Nothing, state { st_queue = Heap.empty })
    Just (overlap, n, queue) ->
      (Just overlap,
       state { st_queue = queue, st_considered = st_considered + n })
  where
    deq !n queue = do
      (passive, queue) <- Heap.uncons queue
      case findPassive config state passive of
        Just (rule1, rule2, overlap) ->
          case simplifyOverlap st_oriented_rules overlap of
            Just Overlap{overlap_eqn = t :=: u}
              | size t <= cfg_max_term_size,
                size u <= cfg_max_term_size ->
                return ((makeCriticalPair rule1 rule2 overlap, rule1, rule2), n+1, queue)
            _ -> deq (n+1) queue
        _ -> deq (n+1) queue

----------------------------------------------------------------------
-- Active rewrite rules.
----------------------------------------------------------------------

data Active f =
  Active {
    active_id    :: {-# UNPACK #-} !Id,
    active_rule  :: {-# UNPACK #-} !(Rule f),
    active_top   :: !(Maybe (Term f)),
    active_proof :: {-# UNPACK #-} !(Proof f),
    -- A model in which the rule is false (used when reorienting)
    active_model :: !(Model f),
    active_rules :: ![ActiveRule f] }

active_cp :: Active f -> CriticalPair f
active_cp Active{..} =
  CriticalPair {
    cp_eqn = unorient active_rule,
    cp_top = active_top,
    cp_proof = derivation active_proof }

-- An active oriented in a particular direction.
data ActiveRule f =
  ActiveRule {
    rule_active    :: {-# UNPACK #-} !Id,
    rule_rid       :: {-# UNPACK #-} !RuleId,
    rule_rule      :: {-# UNPACK #-} !(Rule f),
    rule_proof     :: {-# UNPACK #-} !(Proof f),
    rule_positions :: !(Positions f) }

instance Eq (Active f) where
  (==) = (==) `on` active_id

instance Eq (ActiveRule f) where
  (==) = (==) `on` rule_rid

instance Function f => Pretty (Active f) where
  pPrint Active{..} =
    pPrint active_id <> text "." <+> pPrint active_rule

instance Has (ActiveRule f) Id where the = rule_active
instance f ~ g => Has (ActiveRule f) (Rule g) where the = rule_rule
instance f ~ g => Has (ActiveRule f) (Proof g) where the = rule_proof
instance f ~ g => Has (ActiveRule f) (Positions g) where the = rule_positions

newtype RuleId = RuleId Id deriving (Eq, Ord, Show, Num, Real, Integral, Enum)

-- Add a new active.
{-# INLINEABLE addActive #-}
addActive :: Function f => Config -> State f -> (Id -> Active f) -> State f
addActive config state@State{..} active0 =
  {-# SCC addActive #-}
  let
    active@Active{..} = active0 st_next_active
    state' =
      message (NewActive active) $
      addActiveOnly state{st_next_active = st_next_active+1} active
    passives =
      concatMap (makePassive config state') active_rules
  in if subsumed st_joinable st_rules (unorient active_rule) then
    state
  else
    normaliseGoals $
    foldl' enqueue state' passives

-- Add an active without generating critical pairs. Used in interreduction.
{-# INLINEABLE addActiveOnly #-}
addActiveOnly :: Function f => State f -> Active f -> State f
addActiveOnly state@State{..} active@Active{..} =
  state {
    st_oriented_rules =
      if oriented (orientation active_rule)
      then foldl' insertRule st_oriented_rules active_rules
      else st_oriented_rules,
    st_rules = foldl' insertRule st_rules active_rules,
    st_active_ids = IntMap.insert (fromIntegral active_id) active st_active_ids,
    st_rule_ids = foldl' insertRuleId st_rule_ids active_rules }
  where
    insertRule rules rule@ActiveRule{..} =
      Index.insert (lhs rule_rule) rule rules
    insertRuleId rules rule@ActiveRule{..} =
      IntMap.insert (fromIntegral rule_rid) rule rules

-- Delete an active. Used in interreduction, not suitable for general use.
{-# INLINE deleteActive #-}
deleteActive :: State f -> Active f -> State f
deleteActive state@State{..} Active{..} =
  state {
    st_oriented_rules = foldl' deleteRule st_oriented_rules active_rules,
    st_rules = foldl' deleteRule st_rules active_rules,
    st_active_ids = IntMap.delete (fromIntegral active_id) st_active_ids,
    st_rule_ids = foldl' deleteRuleId st_rule_ids active_rules }
  where
    deleteRule rules rule@ActiveRule{..} =
      Index.delete (lhs rule_rule) rule rules
    deleteRuleId rules ActiveRule{..} =
      IntMap.delete (fromIntegral rule_rid) rules

-- Try to join a critical pair.
{-# INLINEABLE consider #-}
consider :: Function f => Config -> State f -> CriticalPair f -> State f
consider config state cp =
  considerUsing (st_rules state) config state cp

-- Try to join a critical pair, but using a different set of critical
-- pairs for normalisation. Used for CP improvement.
{-# INLINEABLE considerUsing #-}
considerUsing ::
  Function f =>
  Index f (ActiveRule f) -> Config -> State f -> CriticalPair f -> State f
considerUsing rules config@Config{..} state@State{..} cp0 =
  {-# SCC consider #-}
  -- Important to canonicalise the rule so that we don't get
  -- bigger and bigger variable indices over time
  let cp = canonicalise cp0 in
  case joinCriticalPair cfg_join st_joinable rules Nothing cp of
    Right (mcp, cps) ->
      let
        state' = foldl' (considerUsing rules config) state cps
      in case mcp of
        Just cp -> addJoinable state' (cp_eqn cp)
        Nothing -> state'

    Left (cp, model) ->
      foldl' (addCP config model) state (split cp)

{-# INLINEABLE addCP #-}
addCP :: Function f => Config -> Model f -> State f -> CriticalPair f -> State f
addCP config model state@State{..} CriticalPair{..} =
  addActive config state $ \n ->
  let
    pf = certify cp_proof
    rule = orient cp_eqn

    makeRule k r p =
      ActiveRule {
        rule_active = n,
        rule_rid = RuleId (n*2+k),
        rule_rule = r rule,
        rule_proof = p pf,
        rule_positions = positions (lhs (r rule)) }
  in
  Active {
    active_id = n,
    active_rule = rule,
    active_model = model,
    active_top = cp_top,
    active_proof = pf,
    active_rules =
      usortBy (comparing (canonicalise . rule_rule)) $
        makeRule 0 id id:
        [ makeRule 1 backwards (certify . symm . derivation)
        | not (oriented (orientation rule)) ] }

-- Add a new equation.
{-# INLINEABLE addAxiom #-}
addAxiom :: Function f => Config -> State f -> Axiom f -> State f
addAxiom config state axiom =
  consider config state $
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

{-# INLINEABLE improves #-}
improves :: Function f => Config -> CriticalPair f -> CriticalPair f -> Bool
  -- XXX also try:
  -- old is renaming of new
  -- and number of inversions is less
improves Config{..} _ _ | not cfg_improve_critical_pairs = False
improves _ old new =
  size (lhs oldRule) >= size (lhs newRule) &&
  size (rhs oldRule) >= size (rhs newRule) &&
  score (orientation oldRule) > score (orientation newRule)
  where
    oldRule = orient (cp_eqn old)
    newRule = orient (cp_eqn new)

    score Unoriented = maxBound
    score (Permutative xs) = length xs
    score _ = 0

-- For goal terms we store the set of all their normal forms.
-- Name and number are for information only.
data Goal f =
  Goal {
    goal_name   :: String,
    goal_number :: Int,
    goal_eqn    :: Equation f,
    goal_lhs    :: Set (Resulting f),
    goal_rhs    :: Set (Resulting f) }

-- Add a new goal.
{-# INLINEABLE addGoal #-}
addGoal :: Function f => Config -> State f -> Goal f -> State f
addGoal _config state@State{..} goal =
  normaliseGoals state { st_goals = goal:st_goals }

-- Normalise all goals.
{-# INLINEABLE normaliseGoals #-}
normaliseGoals :: Function f => State f -> State f
normaliseGoals state@State{..} =
  {-# SCC normaliseGoals #-}
  state {
    st_goals =
      map (goalMap (normalForms (rewrite reduces st_rules) . Set.toList)) st_goals }
  where
    goalMap f goal@Goal{..} =
      goal { goal_lhs = f goal_lhs, goal_rhs = f goal_rhs }

-- Create a goal.
{-# INLINE goal #-}
goal :: Int -> String -> Equation f -> Goal f
goal n name (t :=: u) =
  Goal {
    goal_name = name,
    goal_number = n,
    goal_eqn = t :=: u,
    goal_lhs = Set.singleton (reduce (Refl t)),
    goal_rhs = Set.singleton (reduce (Refl u)) }

----------------------------------------------------------------------
-- Interreduction.
----------------------------------------------------------------------

-- Simplify all rules.
{-# INLINEABLE interreduce #-}
interreduce :: Function f => Config -> State f -> State f
interreduce config@Config{..} state =
  {-# SCC interreduce #-}
  let
    state' =
      foldl' (interreduce1 config)
        -- Clear out st_joinable, since we don't know which
        -- equations have made use of each active.
        state { st_joinable = Index.Nil }
        (IntMap.elems (st_active_ids state))
    in state' { st_joinable = st_joinable state }

{-# INLINEABLE interreduce1 #-}
interreduce1 :: Function f => Config -> State f -> Active f -> State f
interreduce1 config@Config{..} state active@Active{..} =
  -- Exclude the active from the rewrite rules when testing
  -- joinability, otherwise it will be trivially joinable.
  -- Also exclude rules which are improved by this one.
  let
    improved =
      [ active'
      | active' <- IntMap.elems (st_active_ids state),
        improves config (active_cp active') (active_cp active) ]
  in case
    joinCriticalPair cfg_join
      (st_joinable state)
      (st_rules
        (foldl' deleteActive state
         (active:improved)))
      (Just active_model) (active_cp active)
  of
    Right (_, cps) ->
      flip (foldl' (consider config)) cps $
      message (DeleteActive active) $
      deleteActive state active
    Left (cp, model)
      | cp_eqn cp /= cp_eqn (active_cp active) ->
        flip (foldl' (addCP config model)) (split cp) $
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
    output_report  :: State f -> m (),
    output_message :: Message f -> m () }

{-# INLINE complete #-}
complete :: (Function f, MonadIO m) => Output m f -> Config -> State f -> m (State f)
complete Output{..} config@Config{..} state =
  flip StateM.execStateT state $ do
    tasks <- sequence
      [newTask 1 0.1 $ do
         lift $ output_message SimplifyQueue
         state <- StateM.get
         StateM.put $! simplifyQueue config state,
       newTask 0.25 0.05 $ do
         when cfg_simplify $ do
           lift $ output_message Interreduce
           state <- StateM.get
           StateM.put $! interreduce config state,
       newTask 10 1 $ do
         state <- StateM.get
         lift $ output_report state]

    let
      loop = do
        progress <- StateM.state (complete1 config)
        state <- StateM.get
        lift $ mapM_ output_message (messages state)
        StateM.put (clearMessages state)
        mapM_ checkTask tasks
        when progress loop

    loop
    state <- StateM.get
    lift $ output_report state

{-# INLINEABLE complete1 #-}
complete1 :: Function f => Config -> State f -> (Bool, State f)
complete1 config@Config{..} state
  | st_considered state >= cfg_max_critical_pairs =
    (False, state)
  | solved state = (False, state)
  | otherwise =
    case dequeue config state of
      (Nothing, state) -> (False, state)
      (Just (overlap, rule1, rule2), state) ->
        let
          state' =
            foldl' deleteActive state
              [ active
              | ActiveRule{..} <- [rule1, rule2],
                Just active <- [IntMap.lookup (fromIntegral rule_active) (st_active_ids state)],
                or [ improves config (active_cp active) cp | cp <- split overlap ] ]
        in
          (True, considerUsing (st_rules state') config state overlap)

{-# INLINEABLE solved #-}
solved :: Function f => State f -> Bool
solved = not . null . solutions

-- Return whatever goals we have proved and their proofs.
{-# INLINEABLE solutions #-}
solutions :: Function f => State f -> [ProvedGoal f]
solutions State{..} = {-# SCC solutions #-} do
  Goal{goal_lhs = ts, goal_rhs = us, ..} <- st_goals
  guard (not (null (Set.intersection ts us)))
  let t:_ = filter (`Set.member` us) (Set.toList ts)
      u:_ = filter (== t) (Set.toList us)
      -- Strict so that we check the proof before returning a solution
      !p =
        Proof.certify $
          reductionProof (reduction t) `Proof.trans`
          Proof.symm (reductionProof (reduction u))
  return
    ProvedGoal {
      pg_number = goal_number,
      pg_name = goal_name,
      pg_proof = p }

{-# INLINEABLE report #-}
report :: Function f => State f -> String
report State{..} =
  printf "Statistics:\n" ++
  printf "  %d rules, of which %d oriented, %d unoriented, %d permutative, %d weakly oriented.\n"
    (length orients)
    (length [ () | Oriented <- orients ])
    (length [ () | Unoriented <- orients ])
    (length [ () | Permutative{} <- orients ])
    (length [ () | WeaklyOriented{} <- orients ]) ++
  printf "  %d queued critical pairs.\n" queuedPairs ++
  printf "  %d critical pairs considered so far.\n" st_considered
  where
    orients = map (orientation . the) (Index.elems st_rules)
    queuedPairs = Heap.size st_queue
