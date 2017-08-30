{-# LANGUAGE RecordWildCards, MultiParamTypeClasses, GADTs, BangPatterns, OverloadedStrings, ScopedTypeVariables, GeneralizedNewtypeDeriving, PatternGuards, TypeFamilies #-}
module Twee where

import Twee.Base
import Twee.Rule
import Twee.Equation
import qualified Twee.Proof as Proof
import Twee.Proof(Proof, Axiom(..), Lemma(..), ProvedGoal(..), provedGoal, certify, derivation, symm)
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
import qualified Twee.Heap as Heap
import Twee.Heap(Heap)
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
import Data.Word
import Data.Bits

----------------------------------------------------------------------
-- Configuration and prover state.
----------------------------------------------------------------------

data Config =
  Config {
    cfg_max_term_size          :: Int,
    cfg_max_critical_pairs     :: Int,
    cfg_max_cp_depth           :: Int,
    cfg_simplify               :: Bool,
    cfg_renormalise_percent    :: Int,
    cfg_critical_pairs         :: CP.Config,
    cfg_join                   :: Join.Config,
    cfg_proof_presentation     :: Proof.Config }

data State f =
  State {
    st_rules          :: !(RuleIndex f (ActiveRule f)),
    st_active_ids     :: !(IntMap (Active f)),
    st_rule_ids       :: !(IntMap (ActiveRule f)),
    st_joinable       :: !(Index f (Equation f)),
    st_goals          :: ![Goal f],
    st_queue          :: !(Heap (PackedPassive f)),
    st_next_active    :: {-# UNPACK #-} !Id,
    st_next_rule      :: {-# UNPACK #-} !RuleId,
    st_considered     :: {-# UNPACK #-} !Int,
    st_messages_rev   :: ![Message f] }

defaultConfig :: Config
defaultConfig =
  Config {
    cfg_max_term_size = maxBound,
    cfg_max_critical_pairs = maxBound,
    cfg_max_cp_depth = maxBound,
    cfg_simplify = True,
    cfg_renormalise_percent = 5,
    cfg_critical_pairs =
      CP.Config {
        cfg_lhsweight = 3,
        cfg_rhsweight = 1,
        cfg_funweight = 7,
        cfg_varweight = 6,
        cfg_depthweight = 16,
        cfg_dupcost = 7,
        cfg_dupfactor = 0 },
    cfg_join = Join.defaultConfig,
    cfg_proof_presentation = Proof.defaultConfig }

initialState :: State f
initialState =
  State {
    st_rules = RuleIndex.nil,
    st_active_ids = IntMap.empty,
    st_rule_ids = IntMap.empty,
    st_joinable = Index.Nil,
    st_goals = [],
    st_queue = Heap.empty,
    st_next_active = 1,
    st_next_rule = 0,
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
         passive_pos)

data PackedPassive f =
  PackedPassive {-# UNPACK #-} !Word64 {-# UNPACK #-} !Word64
  deriving (Eq, Ord, Show)

packPassive :: Passive f -> PackedPassive f
packPassive (Passive score rule1 rule2 pos) =
  -- Do this so that Ord instance matches with Passive
  if rule1 > rule2 then
    PackedPassive
      (pack score (fromIntegral rule1))
      (pack (fromIntegral rule2) (pos `shiftL` 1))
  else
    PackedPassive
      (pack score (fromIntegral rule2))
      (pack (fromIntegral rule1) (pos `shiftL` 1 + 1))
  where
    pack :: Int32 -> Int32 -> Word64
    pack x y =
      fromIntegral x `shiftL` 32 + fromIntegral y

unpackPassive :: PackedPassive f -> Passive f
unpackPassive (PackedPassive x y) =
  if testBit pos1 0 then
    Passive score (fromIntegral rule2) (fromIntegral rule1) pos
  else
    Passive score (fromIntegral rule1) (fromIntegral rule2) pos
  where
    (score, rule1) = unpack x
    (rule2, pos1) = unpack y
    pos = pos1 `shiftR` 1

    unpack :: Word64 -> (Int32, Int32)
    unpack x = (fromIntegral (x `shiftR` 32), fromIntegral x)

-- Compute all critical pairs from a rule and condense into a Passive.
{-# INLINEABLE makePassive #-}
makePassive :: Function f => Config -> State f -> ActiveRule f -> [Passive f]
makePassive Config{..} State{..} rule =
  {-# SCC makePassive #-}
  [ Passive (fromIntegral (score cfg_critical_pairs o)) (rule_rid rule1) (rule_rid rule2) (fromIntegral (overlap_pos o))
  | (rule1, rule2, o) <- overlaps (Depth cfg_max_cp_depth) (index_oriented st_rules) rules rule ]
  where
    rules = IntMap.elems st_rule_ids

-- Turn a Passive back into an overlap.
-- Doesn't try to simplify it.
{-# INLINEABLE findPassive #-}
findPassive :: forall f. Function f => Config -> State f -> Passive f -> Maybe (ActiveRule f, ActiveRule f, Overlap f)
findPassive Config{..} State{..} Passive{..} = {-# SCC findPassive #-} do
  rule1 <- IntMap.lookup (fromIntegral passive_rule1) st_rule_ids
  rule2 <- IntMap.lookup (fromIntegral passive_rule2) st_rule_ids
  let !depth = 1 + max (the rule1) (the rule2)
  overlap <-
    overlapAt (fromIntegral passive_pos) depth
      (renameAvoiding (the rule2 :: Rule f) (the rule1)) (the rule2)
  return (rule1, rule2, overlap)

-- Renormalise a queued Passive.
{-# INLINEABLE simplifyPassive #-}
simplifyPassive :: Function f => Config -> State f -> Passive f -> Maybe (Passive f)
simplifyPassive config@Config{..} state@State{..} passive = {-# SCC simplifyPassive #-} do
  (_, _, overlap) <- findPassive config state passive
  overlap <- simplifyOverlap (index_oriented st_rules) overlap
  return passive {
    passive_score = fromIntegral $
      fromIntegral (passive_score passive) `intMin`
      score cfg_critical_pairs overlap }

-- Renormalise the entire queue.
{-# INLINEABLE simplifyQueue #-}
simplifyQueue :: Function f => Config -> State f -> State f
simplifyQueue config state =
  {-# SCC simplifyQueue #-}
  state { st_queue = simp (st_queue state) }
  where
    simp =
      Heap.mapMaybe (fmap packPassive . simplifyPassive config state . unpackPassive)

-- Enqueue a critical pair.
{-# INLINEABLE enqueue #-}
enqueue :: Function f => State f -> Passive f -> State f
enqueue state passive =
  {-# SCC enqueue #-}
  state { st_queue = Heap.insert (packPassive passive) (st_queue state) }

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
      (packedPassive, queue) <- Heap.removeMin queue
      let passive = unpackPassive packedPassive
      case findPassive config state passive of
        Just (rule1, rule2, overlap)
          | passive_score passive >= 0,
            Just Overlap{overlap_eqn = t :=: u} <-
              simplifyOverlap (index_oriented st_rules) overlap,
            size t <= cfg_max_term_size,
            size u <= cfg_max_term_size,
            Just cp <- makeCriticalPair rule1 rule2 overlap ->
              return ((cp, rule1, rule2), n+1, queue)
        _ -> deq (n+1) queue

----------------------------------------------------------------------
-- Active rewrite rules.
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
    pPrint active_id <> text "." <+> pPrint (canonicalise active_rule)

instance Has (ActiveRule f) Id where the = rule_active
instance Has (ActiveRule f) Depth where the = rule_depth
instance f ~ g => Has (ActiveRule f) (Rule g) where the = rule_rule
instance f ~ g => Has (ActiveRule f) (Proof g) where the = rule_proof
instance f ~ g => Has (ActiveRule f) (Lemma g) where the x = Lemma (the x) (the x)
instance f ~ g => Has (ActiveRule f) (Positions g) where the = rule_positions

newtype RuleId = RuleId Id deriving (Eq, Ord, Show, Num, Real, Integral, Enum)

-- Add a new active.
{-# INLINEABLE addActive #-}
addActive :: Function f => Config -> State f -> (Id -> RuleId -> RuleId -> Active f) -> State f
addActive config state@State{..} active0 =
  {-# SCC addActive #-}
  let
    active@Active{..} = active0 st_next_active st_next_rule (succ st_next_rule)
    state' =
      message (NewActive active) $
      addActiveOnly state{st_next_active = st_next_active+1, st_next_rule = st_next_rule+2} active
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
consider :: Function f => Config -> State f -> CriticalPair f -> State f
consider config state cp =
  considerUsing (st_rules state) config state cp

-- Try to join a critical pair, but using a different set of critical
-- pairs for normalisation.
{-# INLINEABLE considerUsing #-}
considerUsing ::
  Function f =>
  RuleIndex f (ActiveRule f) -> Config -> State f -> CriticalPair f -> State f
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
  addActive config state $ \n k1 k2 ->
  let
    pf = certify cp_proof
    rule = orient cp_eqn

    makeRule k r p =
      ActiveRule {
        rule_active = n,
        rule_rid = k,
        rule_depth = cp_depth,
        rule_rule = r rule,
        rule_proof = p pf,
        rule_positions = positions (lhs (r rule)) }
  in
  Active {
    active_id = n,
    active_depth = cp_depth,
    active_rule = rule,
    active_model = model,
    active_top = cp_top,
    active_proof = pf,
    active_rules =
      usortBy (comparing (canonicalise . rule_rule)) $
        makeRule k1 id id:
        [ makeRule k2 backwards (certify . symm . derivation)
        | not (oriented (orientation rule)) ] }

-- Add a new equation.
{-# INLINEABLE addAxiom #-}
addAxiom :: Function f => Config -> State f -> Axiom f -> State f
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
      map (goalMap (successors (rewrite reduces (index_all st_rules)) . Set.toList)) st_goals }
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
interreduce1 config@Config{..} state active =
  -- Exclude the active from the rewrite rules when testing
  -- joinability, otherwise it will be trivially joinable.
  case
    joinCriticalPair cfg_join
      (st_joinable state)
      (st_rules (deleteActive state active))
      (Just (active_model active)) (active_cp active)
  of
    Right (_, cps) ->
      flip (foldl' (consider config)) cps $
      message (DeleteActive active) $
      deleteActive state active
    Left (cp, model)
      | not (cp_eqn cp `isInstanceOf` cp_eqn (active_cp active)) ->
        flip (foldl' (addCP config model)) (split cp) $
        message (DeleteActive active) $
        deleteActive state active
      | model /= active_model active ->
        flip addActiveOnly active { active_model = model } $
        deleteActive state active
      | otherwise ->
        state
  where
    (t :=: u) `isInstanceOf` (t' :=: u') = isJust $ do
      sub <- match t' t
      matchIn sub u' u


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
      [newTask 1 (fromIntegral cfg_renormalise_percent / 100) $ do
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

{-# INLINEABLE complete1 #-}
complete1 :: Function f => Config -> State f -> (Bool, State f)
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
  return (provedGoal goal_number goal_name p)

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
  printf "  %d critical pairs considered so far." st_considered
  where
    orients = map (orientation . active_rule) (IntMap.elems st_active_ids)
    queuedPairs = Heap.size st_queue

----------------------------------------------------------------------
-- For code which uses twee as a library.
----------------------------------------------------------------------

{-# INLINEABLE completePure #-}
completePure :: Function f => Config -> State f -> State f
completePure cfg state
  | progress = completePure cfg (clearMessages state')
  | otherwise = state'
  where
    (progress, state') = complete1 cfg state

{-# INLINEABLE normaliseTerm #-}
normaliseTerm :: Function f => State f -> Term f -> Resulting f
normaliseTerm State{..} t =
  normaliseWith (const True) (rewrite reduces (index_all st_rules)) t

{-# INLINEABLE simplifyTerm #-}
simplifyTerm :: Function f => State f -> Term f -> Term f
simplifyTerm State{..} t =
  simplify (index_oriented st_rules) t
