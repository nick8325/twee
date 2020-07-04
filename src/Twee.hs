-- | The main prover loop.
{-# LANGUAGE RecordWildCards, MultiParamTypeClasses, GADTs, BangPatterns, OverloadedStrings, ScopedTypeVariables, GeneralizedNewtypeDeriving, PatternGuards, TypeFamilies #-}
module Twee where

import Twee.Base
import Twee.Rule hiding (normalForms)
import qualified Twee.Rule as Rule
import Twee.Equation
import qualified Twee.Proof as Proof
import Twee.Proof(Axiom(..), Proof(..), ProvedGoal(..), provedGoal, certify, derivation, symm)
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
import qualified Data.Set as Set
import Data.Set(Set)
import Data.Int
import Data.Ord
import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import qualified Control.Monad.Trans.State.Strict as StateM

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
    cfg_critical_pairs         :: CP.Config,
    cfg_join                   :: Join.Config,
    cfg_proof_presentation     :: Proof.Config f }

-- | The prover state.
data State f =
  State {
    st_rules          :: !(RuleIndex f (ActiveRule f)),
    st_active_ids     :: !(IntMap (Active f)),
    st_rule_ids       :: !(IntMap (ActiveRule f)),
    st_joinable       :: !(Index f (Equation f)),
    st_goals          :: ![Goal f],
    st_queue          :: !(Queue Params),
    st_next_active    :: {-# UNPACK #-} !Id,
    st_next_rule      :: {-# UNPACK #-} !RuleId,
    st_considered     :: {-# UNPACK #-} !Int64,
    st_simplified_at  :: {-# UNPACK #-} !Id,
    st_cp_sample      :: ![Maybe (Overlap f)],
    st_cp_next_sample :: ![(Integer, Int)],
    st_num_cps        :: !Integer,
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
    st_rule_ids = IntMap.empty,
    st_joinable = Index.empty,
    st_goals = [],
    st_queue = Queue.empty,
    st_next_active = 1,
    st_next_rule = 0,
    st_considered = 0,
    st_simplified_at = 1,
    st_cp_sample = [],
    st_cp_next_sample = reservoir cfg_cp_sample_size,
    st_num_cps = 0,
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
    -- | The rules were reduced wrt each other.
  | Interreduce

instance Function f => Pretty (Message f) where
  pPrint (NewActive rule) = pPrint rule
  pPrint (NewEquation eqn) =
    text "  (hard)" <+> pPrint eqn
  pPrint (DeleteActive rule) =
    text "  (delete rule " <#> pPrint (active_id rule) <#> text ")"
  pPrint SimplifyQueue =
    text "  (simplifying queued critical pairs...)"
  pPrint Interreduce =
    text "  (simplifying rules with respect to one another...)"

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
  type Id Params = RuleId
  type PackedId Params = Int32
  type PackedScore Params = Int32
  packScore _ = fromIntegral
  unpackScore _ = fromIntegral
  packId _ = fromIntegral
  unpackId _ = fromIntegral

-- | Compute all critical pairs from a rule.
{-# INLINEABLE makePassives #-}
{-# SCC makePassives #-}
makePassives :: Function f => Config f -> State f -> ActiveRule f -> [Passive Params]
makePassives Config{..} State{..} rule =
  [ Passive (fromIntegral (score cfg_critical_pairs o)) (rule_rid rule1) (rule_rid rule2) (fromIntegral (overlap_pos o))
  | (rule1, rule2, o) <- overlaps (Depth cfg_max_cp_depth) (index_oriented st_rules) rules rule ]
  where
    rules = IntMap.elems st_rule_ids

-- | Turn a Passive back into an overlap.
-- Doesn't try to simplify it.
{-# INLINEABLE findPassive #-}
{-# SCC findPassive #-}
findPassive :: forall f. Function f => State f -> Passive Params -> Maybe (ActiveRule f, ActiveRule f, Overlap f)
findPassive State{..} Passive{..} = do
  rule1 <- IntMap.lookup (fromIntegral passive_rule1) st_rule_ids
  rule2 <- IntMap.lookup (fromIntegral passive_rule2) st_rule_ids
  let !depth = 1 + max (the rule1) (the rule2)
  overlap <-
    overlapAt (fromIntegral passive_pos) depth
      (renameAvoiding (the rule2 :: Rule f) (the rule1)) (the rule2)
  return (rule1, rule2, overlap)

-- | Renormalise a queued Passive.
{-# INLINEABLE simplifyPassive #-}
{-# SCC simplifyPassive #-}
simplifyPassive :: Function f => Config f -> State f -> Passive Params -> Maybe (Passive Params)
simplifyPassive Config{..} state@State{..} passive = do
  (_, _, overlap) <- findPassive state passive
  overlap <- simplifyOverlap (index_oriented st_rules) overlap
  return passive {
    passive_score = fromIntegral $
      fromIntegral (passive_score passive) `intMin`
      score cfg_critical_pairs overlap }

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
enqueue :: Function f => State f -> RuleId -> [Passive Params] -> State f
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
dequeue :: Function f => Config f -> State f -> (Maybe (CriticalPair f, ActiveRule f, ActiveRule f), State f)
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
        Just (rule1, rule2, overlap@Overlap{overlap_eqn = t :=: u})
          | fromMaybe True (cfg_accept_term <*> pure t),
            fromMaybe True (cfg_accept_term <*> pure u),
            cp <- makeCriticalPair rule1 rule2 overlap ->
              return ((cp, rule1, rule2), n+1, queue)
        _ -> deq (n+1) queue

----------------------------------------------------------------------
-- * Active rewrite rules.
----------------------------------------------------------------------

data Active f =
  Active {
    active_id    :: {-# UNPACK #-} !Id,
    active_depth :: {-# UNPACK #-} !Depth,
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
    cp_depth = active_depth,
    cp_top = active_top,
    cp_proof = derivation active_proof }

-- An active oriented in a particular direction.
data ActiveRule f =
  ActiveRule {
    rule_active    :: {-# UNPACK #-} !Id,
    rule_rid       :: {-# UNPACK #-} !RuleId,
    rule_depth     :: {-# UNPACK #-} !Depth,
    rule_rule      :: {-# UNPACK #-} !(Rule f),
    rule_proof     :: {-# UNPACK #-} !(Proof f),
    rule_positions :: !(Positions f) }

instance PrettyTerm f => Symbolic (ActiveRule f) where
  type ConstantOf (ActiveRule f) = f
  termsDL ActiveRule{..} =
    termsDL rule_rule `mplus`
    termsDL (derivation rule_proof)
  subst_ sub r@ActiveRule{..} =
    r {
      rule_rule = rule',
      rule_proof = certify (subst_ sub (derivation rule_proof)),
      rule_positions = positions (lhs rule') }
    where
      rule' = subst_ sub rule_rule

instance Eq (Active f) where
  (==) = (==) `on` active_id

instance Eq (ActiveRule f) where
  (==) = (==) `on` rule_rid

instance Function f => Pretty (Active f) where
  pPrint Active{..} =
    pPrint active_id <#> text "." <+> pPrint (canonicalise active_rule)

instance Has (ActiveRule f) Id where the = rule_active
instance Has (ActiveRule f) RuleId where the = rule_rid
instance Has (ActiveRule f) Depth where the = rule_depth
instance f ~ g => Has (ActiveRule f) (Rule g) where the = rule_rule
instance f ~ g => Has (ActiveRule f) (Proof g) where the = rule_proof
instance f ~ g => Has (ActiveRule f) (Positions g) where the = rule_positions

newtype RuleId = RuleId Id deriving (Eq, Ord, Show, Num, Real, Integral, Enum)

-- Add a new active.
{-# INLINEABLE addActive #-}
{-# SCC addActive #-}
addActive :: Function f => Config f -> State f -> (Id -> RuleId -> RuleId -> Active f) -> State f
addActive config state@State{..} active0 =
  let
    active@Active{..} = active0 st_next_active st_next_rule (succ st_next_rule)
    state' =
      message (NewActive active) $
      addActiveOnly state{st_next_active = st_next_active+1, st_next_rule = st_next_rule+2} active
  in if subsumed st_joinable st_rules (unorient active_rule) then
    state
  else
    normaliseGoals config $
    foldl' enqueueRule state' active_rules
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
      (_, _, overlap) <- findPassive state passive
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
    st_rules = foldl' insertRule st_rules active_rules,
    st_active_ids = IntMap.insert (fromIntegral active_id) active st_active_ids,
    st_rule_ids = foldl' insertRuleId st_rule_ids active_rules }
  where
    insertRule rules rule@ActiveRule{..} =
      RuleIndex.insert (lhs rule_rule) rule rules
    insertRuleId rules rule@ActiveRule{..} =
      IntMap.insert (fromIntegral rule_rid) rule rules

-- Delete an active. Used in interreduction, not suitable for general use.
{-# INLINE deleteActive #-}
deleteActive :: Function f => State f -> Active f -> State f
deleteActive state@State{..} Active{..} =
  state {
    st_rules = foldl' deleteRule st_rules active_rules,
    st_active_ids = IntMap.delete (fromIntegral active_id) st_active_ids,
    st_rule_ids = foldl' deleteRuleId st_rule_ids active_rules }
  where
    deleteRule rules rule =
      RuleIndex.delete (lhs (rule_rule rule)) rule rules
    deleteRuleId rules ActiveRule{..} =
      IntMap.delete (fromIntegral rule_rid) rules

-- Try to join a critical pair.
{-# INLINEABLE consider #-}
consider :: Function f => Config f -> State f -> CriticalPair f -> State f
consider config state cp =
  considerUsing (st_rules state) config state cp

-- Try to join a critical pair, but using a different set of critical
-- pairs for normalisation.
{-# INLINEABLE considerUsing #-}
{-# SCC considerUsing #-}
considerUsing ::
  Function f =>
  RuleIndex f (ActiveRule f) -> Config f -> State f -> CriticalPair f -> State f
considerUsing rules config@Config{..} state@State{..} cp0 =
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
addCP :: Function f => Config f -> Model f -> State f -> CriticalPair f -> State f
addCP config model state@State{..} CriticalPair{..} =
  let
    pf = certify cp_proof
    rule = orient cp_eqn

    makeRule n k r p =
      ActiveRule {
        rule_active = n,
        rule_rid = k,
        rule_depth = cp_depth,
        rule_rule = r rule,
        rule_proof = p pf,
        rule_positions = positions (lhs (r rule)) }
  in
  addActive config state $ \n k1 k2 ->
  Active {
    active_id = n,
    active_depth = cp_depth,
    active_rule = rule,
    active_model = model,
    active_top = cp_top,
    active_proof = pf,
    active_rules =
      usortBy (comparing (canonicalise . rule_rule)) $
        makeRule n k1 id id:
        [ makeRule n k2 backwards (certify . symm . derivation)
        | not (oriented (orientation rule)) ] }

-- Add a new equation.
{-# INLINEABLE addAxiom #-}
addAxiom :: Function f => Config f -> State f -> Axiom f -> State f
addAxiom config state axiom =
  consider config state $
    CriticalPair {
      cp_eqn = axiom_eqn axiom,
      cp_depth = 0,
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

-- For goal terms we store the set of all their normal forms.
-- Name and number are for information only.
data Goal f =
  Goal {
    goal_name     :: String,
    goal_number   :: Int,
    goal_eqn      :: Equation f,
    goal_lhs      :: Set (Resulting f),
    goal_rhs      :: Set (Resulting f) }

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
    nf reduce
      | cfg_set_join_goals = Rule.normalForms reduce
      | otherwise =
        Set.map $ \r ->
          Rule.reduce (reduction r `trans` reduction (Rule.normaliseWith (const True) reduce (result r)))

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
      normaliseGoals config (state { st_goals = map reset (st_goals state) })

    reset goal@Goal{goal_eqn = t :=: u, ..} =
      goal { goal_lhs = Set.singleton (reduce (Refl t)),
             goal_rhs = Set.singleton (reduce (Refl u)) }

    forceList [] = ()
    forceList (x:xs) = x `seq` forceList xs

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
{-# SCC interreduce #-}
interreduce :: Function f => Config f -> State f -> State f
interreduce _ state@State{..} | st_simplified_at == st_next_active = state
interreduce config@Config{..} state =
  let
    state' =
      foldl' (interreduce1 config)
        -- Clear out st_joinable, since we don't know which
        -- equations have made use of each active.
        state { st_joinable = Index.empty }
        (IntMap.elems (st_active_ids state))
    in state' { st_joinable = st_joinable state, st_simplified_at = st_next_active state' }

{-# INLINEABLE interreduce1 #-}
interreduce1 :: Function f => Config f -> State f -> Active f -> State f
interreduce1 config@Config{..} state active =
  -- Exclude the active from the rewrite rules when testing
  -- joinability, otherwise it will be trivially joinable.
  case
    joinCriticalPair cfg_join
      Index.empty -- (st_joinable state)
      (st_rules (deleteActive state active))
      (Just (active_model active)) (active_cp active)
  of
    Right (_, cps) ->
      flip (foldl' (consider config)) cps $
      message (DeleteActive active) $
      deleteActive state active
    Left (cp, model)
      | cp_eqn cp `simplerThan` cp_eqn (active_cp active) ->
        flip (foldl' (consider config)) (split cp) $
        message (DeleteActive active) $
        deleteActive state active
      | model /= active_model active ->
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
       newTask 1 0.05 $ do
         when cfg_simplify $ do
           lift $ output_message Interreduce
           state <- StateM.get
           StateM.put $! simplifySample $! interreduce config state,
       newTask 1 0.02 $ do
          state <- StateM.get
          StateM.put $! recomputeGoals config state ]

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
      (Just (overlap, _, _), state) ->
        (True, consider config state overlap)

{-# INLINEABLE solved #-}
solved :: Function f => State f -> Bool
solved = not . null . solutions

-- Return whatever goals we have proved and their proofs.
{-# INLINEABLE solutions #-}
{-# SCC solutions #-}
solutions :: Function f => State f -> [ProvedGoal f]
solutions State{..} = do
  Goal{goal_lhs = ts, goal_rhs = us, ..} <- st_goals
  guard (not (null (Set.intersection ts us)))
  let t:_ = filter (`Set.member` us) (Set.toList ts)
      u:_ = filter (== t) (Set.toList us)
      -- Strict so that we check the proof before returning a solution
      !p =
        Proof.certify $
          reductionProof (reduction t) `Proof.trans`
          Proof.symm (reductionProof (reduction u))
  return (provedGoal goal_number goal_name p)

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
normaliseTerm :: Function f => State f -> Term f -> Resulting f
normaliseTerm State{..} t =
  normaliseWith (const True) (rewrite reduces (index_all st_rules)) t

{-# INLINEABLE normalForms #-}
normalForms :: Function f => State f -> Term f -> Set (Resulting f)
normalForms State{..} t =
  Rule.normalForms (rewrite reduces (index_all st_rules)) (Set.singleton (reduce (Refl t)))

{-# INLINEABLE simplifyTerm #-}
simplifyTerm :: Function f => State f -> Term f -> Term f
simplifyTerm State{..} t =
  simplify (index_oriented st_rules) t
