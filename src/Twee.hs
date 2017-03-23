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
    cfg_max_term_size      :: Int,
    cfg_max_critical_pairs :: Int,
    cfg_simplify           :: Bool,
    cfg_critical_pairs     :: CP.Config,
    cfg_join               :: Join.Config,
    cfg_proof_presentation :: Proof.Config }

data State f =
  State {
    st_oriented_rules :: !(Index f (ActiveRule f)),
    st_rules          :: !(Index f (ActiveRule f)),
    st_active_ids     :: !(IntMap (Active f)),
    st_rule_ids       :: !(IntMap (ActiveRule f)),
    st_replaced_rules :: !(IntMap RuleId),
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
    st_replaced_rules = IntMap.empty,
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
    NewRule !(Active f)
  | NewEquation !(Equation f)
  | DeleteRule !(Active f)
  | SimplifyQueue

instance Function f => Pretty (Message f) where
  pPrint (NewRule rule) = pPrint rule
  pPrint (NewEquation eqn) =
    text "  (hard)" <+> pPrint eqn
  pPrint (DeleteRule rule) =
    text "  (delete rule " <> pPrint (active_id rule) <> text ")"
  pPrint SimplifyQueue =
    text "  (simplifying queued critical pairs...)"

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
  deriving (Eq, Ord, Show)

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
  let
    lookup rid =
      IntMap.lookup (fromIntegral rid) st_rule_ids `mplus`
      (IntMap.lookup (fromIntegral rid) st_replaced_rules >>= lookup)
  rule1 <- lookup (fromIntegral passive_rule1)
  rule2 <- lookup (fromIntegral passive_rule2)
  overlap <-
    overlapAt (fromIntegral passive_pos)
      (renameAvoiding (the rule2 :: Rule f) (the rule1)) (the rule2)
  return (rule1, rule2, overlap)

-- Renormalise a queued Passive.
-- Also takes care of deleting any orphans.
{-# INLINEABLE simplifyPassive #-}
simplifyPassive :: Function f => Config -> State f -> Passive f -> Maybe (Passive f)
simplifyPassive config@Config{..} state@State{..} passive = {-# SCC simplifyPassive #-} do
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
    simp =
      Heap.fromList .
      mapMaybe (simplifyPassive config state) .
      Heap.toUnsortedList

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
dequeue :: Function f => Config -> State f -> (Maybe (CriticalPair f), State f)
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
                return (makeCriticalPair rule1 rule2 overlap, n+1, queue)
            _ -> deq (n+1) queue
        _ -> deq (n+1) queue

----------------------------------------------------------------------
-- Active rewrite rules.
----------------------------------------------------------------------

data Active f =
  Active {
    active_id :: {-# UNPACK #-} !Id,
    active_rule :: {-# UNPACK #-} !(Rule f),
    active_top :: !(Maybe (Term f)),
    active_proof :: {-# UNPACK #-} !(Proof f),
    -- Models in which the rule is false (used when reorienting)
    active_models    :: ![Model f],
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
      flip (interreduce config) active $
      message (NewRule active) $
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

-- Replace an active with its simplification. Used in interreduction.
{-# INLINE replaceActive #-}
replaceActive :: Function f => State f -> Active f -> Active f -> State f
replaceActive state@State{..} active active' =
  flip addActiveOnly active' $
  flip deleteActive active $
  state {
    st_replaced_rules =
      IntMap.insert (fromIntegral (rid active)) (rid active')
        st_replaced_rules }
  where
    rid Active{active_rules = [ActiveRule{..}]} = rule_rid
    rid _ = error "replaceRule called on unoriented rule"

-- Try to join a critical pair.
{-# INLINEABLE consider #-}
consider :: Function f => Config -> State f -> CriticalPair f -> State f
consider config@Config{..} state@State{..} cp0 =
  {-# SCC consider #-}
  -- Important to canonicalise the rule so that we don't get
  -- bigger and bigger variable indices over time
  let cp = canonicalise cp0 in
  case joinCriticalPair cfg_join st_joinable st_rules cp of
    Right (mcp, cps) ->
      let
        state' = foldl' (consider config) state cps
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
    active_models = [model],
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

data Simplification f = Simplify | Delete | NewModels [Model f]
  deriving Show
instance Pretty (Simplification f) where pPrint = text . show

-- Note on st_rules and st_joinable during interreduction.
-- After adding a new rule we check if any old rules can now be joined
-- or simplified. When we try rewriting an old rule, we must of course
-- remove it from the ruleset first, so as to avoid using the rule to
-- rewrite itself. We must also not use an equation in st_joinable to
-- simplify a rule if the equation was derived from the rule. As we
-- don't keep track of the origin of each joinable equation, we simply
-- disable st_joinable during interreduction.
--
-- After considering all reoriented rules, we put back st_joinable.
-- This is fine because all the equations that were in st_joinable
-- before should indeed still be joinable once the reoriented rules
-- are added.

-- Simplify all old rules wrt a new rule.
{-# INLINEABLE interreduce #-}
interreduce :: Function f => Config -> State f -> Active f -> State f
interreduce config@Config{..} state new
  | not cfg_simplify = state
  | otherwise =
    {-# SCC interreduce #-}
    foldl' interreduce1 state simpls
    where
      simpls =
        [ (old, simp)
        | old <- IntMap.elems (st_active_ids state),
          old /= new,
          let state' = deleteActive state { st_joinable = Index.Nil } old,
          simp <- maybeToList (simplification config state' new old) ]

{-# INLINEABLE interreduce1 #-}
interreduce1 :: Function f => State f -> (Active f, Simplification f) -> State f
interreduce1 state@State{..} (active@Active{active_rule = Rule _ lhs rhs, active_rules = ~[rule], ..}, Simplify) =
  message (DeleteRule active) $
  message (NewRule active') $
  replaceActive state' active active'
  where
    proof =
      Proof.certify $
      Proof.derivation active_proof `Proof.trans` reductionProof (reduction rhs')
    rule' = orient (lhs :=: result rhs')

    active' =
      active {
        active_rule = rule',
        active_id = st_next_active,
        active_proof = proof,
        active_rules =
          [rule {
             rule_active = st_next_active,
             rule_rid = RuleId (st_next_active*2),
             rule_rule = rule',
             rule_proof = proof }]}

    state' = state { st_next_active = succ st_next_active }

    rhs' = normaliseWith (const True) (rewrite reduces st_rules) rhs

interreduce1 state@State{..} (rule@Active{..}, NewModels models) =
  flip addActiveOnly rule' $ deleteActive state rule
  where
    rule' =
      rule {
        active_models = models }
interreduce1 state@State{..} (rule, Delete) =
  message (DeleteRule rule) $
  deleteActive state rule

-- Work out what sort of simplification can be applied to a rule.
{-# INLINEABLE simplification #-}
simplification :: Function f => Config -> State f -> Active f -> Active f -> Maybe (Simplification f)
simplification Config{..} State{..} new oldRule@Active{active_rule = old, active_models = models} = do
  -- Don't do anything unless the new rule matches the old one
  guard (any isJust [ match (lhs (the r)) t | t <- subterms (lhs old) ++ subterms (rhs old), r <- active_rules new ])
  reorient `mplus` simplify
  where
    simplify = do
      guard (oriented (orientation old) && reducesWith reduces (rhs old))
      return Simplify

    -- Discover rules which have become ground joinable
    reorient =
      case partition joinable models of
        ([], _) ->
          -- No models are joinable
          Nothing
        (_, []) ->
          -- All existing models are joinable - find out if the rule
          -- really has become ground joinable
          return $
            case groundJoin cfg_join st_joinable st_rules (branches (And [])) (active_cp oldRule) of
              Left model ->
                NewModels [model]
              Right cps
                | all (isNothing . allSteps cfg_join st_joinable st_rules) cps ->
                  Delete
                | otherwise ->
                  NewModels []
        (_, models') ->
          -- Some but not all models are joinable
          return (NewModels models')

    -- Check if a rule is joinable in a given model
    joinable model =
      (reducesWith (reducesInModel model) (lhs old) ||
       reducesWith (reducesInModel model) (rhs old)) &&
      isNothing (joinWith st_joinable st_rules norm (active_cp oldRule))
      where
        norm = normaliseWith (const True) (rewrite (reducesInModel model) st_rules)

    -- Check if the new rule has any effect on a given term
    reducesWith f t =
      not (null [ u | r <- active_rules new, u <- anywhere (tryRule f r) t ])

----------------------------------------------------------------------
-- The main loop.
----------------------------------------------------------------------

data Output m f =
  Output {
    output_report  :: State f -> m (),
    output_message :: Message f -> m () }

{-# INLINE complete #-}
complete :: (Function f, MonadIO m) => Output m f -> Config -> State f -> m (State f)
complete output@Output{..} config state =
  flip StateM.execStateT state $ do
    tasks <- sequence
      [newTask 0.5 0.1 $ do
         lift $ output_message SimplifyQueue
         state <- StateM.get
         StateM.put $! simplifyQueue config state,
       newTask 30 0 $ do
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
complete1 config state
  | st_considered state >= cfg_max_critical_pairs config =
    (False, state)
  | solved state = (False, state)
  | otherwise =
    case dequeue config state of
      (Nothing, state) -> (False, state)
      (Just overlap, state) ->
        (True, consider config state overlap)

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
