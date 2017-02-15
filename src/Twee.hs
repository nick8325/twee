{-# LANGUAGE RecordWildCards, MultiParamTypeClasses, GADTs, BangPatterns, OverloadedStrings #-}
module Twee where

import Twee.Base
import Twee.Rule
import Twee.CP hiding (Config)
import qualified Twee.CP as CP
import Twee.Join
import qualified Twee.Index as Index
import Twee.Index(Index)
import Twee.Constraints
import Twee.Utils
import qualified Data.Heap as Heap
import Data.Heap(Heap)
import qualified Data.IntMap.Strict as IntMap
import Data.IntMap(IntMap)
import Data.Maybe
import Data.Ord
import Data.List
import Data.Function
import qualified Data.Set as Set
import Data.Set(Set)
import Text.Printf
import Debug.Trace

----------------------------------------------------------------------
-- Configuration and prover state.
----------------------------------------------------------------------

data Config =
  Config {
    cfg_max_term_size      :: Int,
    cfg_max_critical_pairs :: Int,
    cfg_critical_pairs     :: CP.Config }

data State f =
  State {
    st_oriented_rules :: !(Index f (TweeRule f)),
    st_rules          :: !(Index f (TweeRule f)),
    st_rule_ids       :: !(IntMap (TweeRule f)),
    st_joinable       :: !(Index f (Equation f)),
    st_goals          :: [Set (Term f)],
    st_queue          :: !(Heap (Passive f)),
    st_label          :: {-# UNPACK #-} !Id,
    st_considered     :: {-# UNPACK #-} !Int }

defaultConfig :: Config
defaultConfig =
  Config {
    cfg_max_term_size = maxBound,
    cfg_max_critical_pairs = maxBound,
    cfg_critical_pairs =
      CP.Config {
        cfg_lhsweight = 2,
        cfg_rhsweight = 1,
        cfg_funweight = 4,
        cfg_varweight = 3,
        cfg_repeats   = True } }

initialState :: State f
initialState =
  State {
    st_oriented_rules = Index.Nil,
    st_rules = Index.Nil,
    st_rule_ids = IntMap.empty,
    st_joinable = Index.Nil,
    st_goals = [],
    st_queue = Heap.empty,
    st_label = 1,
    st_considered = 0 }

----------------------------------------------------------------------
-- The CP queue.
----------------------------------------------------------------------

data Passive f =
  Passive {
    passive_score   :: {-# UNPACK #-} !Int,
    passive_rule1   :: {-# UNPACK #-} !Id,
    passive_rule2   :: {-# UNPACK #-} !Id,
    passive_pos     :: {-# UNPACK #-} !Int }
  deriving (Eq, Ord, Show)

-- Compute all critical pairs from a rule and condense into a Passive.
-- Takes an optional range of rules to use.
{-# INLINEABLE makePassive #-}
makePassive :: Function f => Config -> State f -> Maybe (Id, Id) -> Id -> [Passive f]
makePassive Config{..} State{..} mrange id =
  {-# SCC makePassive #-}
  case IntMap.lookup (unId id) st_rule_ids of
    Nothing -> []
    Just rule ->
      [ Passive (score cfg_critical_pairs o) (rule_id rule1) (rule_id rule2) (overlap_pos o)
      | (rule1, rule2, o) <- overlaps st_oriented_rules rules rule ]
  where
    (lo, hi) = fromMaybe (0, id) mrange
    rules =
      IntMap.elems $
      fst $ IntMap.split (unId (hi+1)) $
      snd $ IntMap.split (unId (lo-1)) st_rule_ids

-- Turn a Passive back into an overlap.
{-# INLINEABLE findPassive #-}
findPassive :: Function f => Config -> State f -> Passive f -> Maybe (Overlap f)
findPassive Config{..} state@State{..} passive@Passive{..} = {-# SCC findPassive #-} do
  rule1 <- the <$> IntMap.lookup (unId passive_rule1) st_rule_ids
  rule2 <- the <$> IntMap.lookup (unId passive_rule2) st_rule_ids
  overlapAt st_oriented_rules passive_pos
    (renameAvoiding rule2 rule1) rule2

-- Renormalise a queued Passive.
-- Also takes care of deleting any orphans.
{-# INLINEABLE simplifyPassive #-}
simplifyPassive :: Function f => Config -> State f -> Passive f -> Maybe (Passive f)
simplifyPassive config@Config{..} state passive = {-# SCC simplifyPassive #-} do
  overlap <- findPassive config state passive
  return passive { passive_score = score cfg_critical_pairs overlap }

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
enqueue :: Function f => Config -> State f -> Passive f -> State f
enqueue config state passive =
  {-# SCC enqueue #-}
  state { st_queue = Heap.insert passive (st_queue state) }

-- Dequeue a critical pair.
-- Also takes care of:
--   * removing any orphans from the head of the queue
--   * splitting ManyCPs up as necessary
--   * ignoring CPs that are too big
{-# INLINEABLE dequeue #-}
dequeue :: Function f => Config -> State f -> (Maybe (Overlap f), State f)
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
        Just overlap@Overlap{overlap_eqn = t :=: u}
          | size t <= cfg_max_term_size,
            size u <= cfg_max_term_size ->
            return (overlap, n+1, queue)
        _ -> deq (n+1) queue

----------------------------------------------------------------------
-- Rules.
----------------------------------------------------------------------

data TweeRule f =
  TweeRule {
    rule_id        :: {-# UNPACK #-} !Id,
    rule_rule      :: {-# UNPACK #-} !(Rule f),
    -- Positions at which the rule can form CPs
    rule_positions :: !(Positions f),
    -- The CP which created the rule
    rule_overlap   :: {-# UNPACK #-} !(Overlap f),
    -- A model in which the rule is false (used when reorienting)
    rule_model     :: !(Model f) }

instance f ~ g => Has (TweeRule f) (Rule g) where the = rule_rule
instance f ~ g => Has (TweeRule f) (Positions g) where the = rule_positions
instance Has (TweeRule f) Id where the = rule_id

-- Add a new rule.
{-# INLINEABLE addRule #-}
addRule :: Function f => Config -> State f -> (Id -> TweeRule f) -> State f
addRule config state@State{..} rule0 =
  {-# SCC addRule #-}
  let
    rule = rule0 st_label
    state' =
      state {
        st_oriented_rules =
          if oriented (orientation (rule_rule rule))
          then Index.insert (lhs (rule_rule rule)) rule st_oriented_rules
          else st_oriented_rules,
        st_rules = Index.insert (lhs (rule_rule rule)) rule st_rules,
        st_rule_ids = IntMap.insert (unId (rule_id rule)) rule st_rule_ids,
        st_label = st_label+1 }
    passives =
      makePassive config state' Nothing (rule_id rule)
  in if subsumed st_joinable st_rules (unorient (rule_rule rule)) then
    state
  else
    traceShow (pPrint (unId (rule_id rule)) <> text ". " <> pPrint (rule_rule rule)) $
    normaliseGoals $
    foldl' (enqueue config) state' passives

-- Normalise all goals.
{-# INLINEABLE normaliseGoals #-}
normaliseGoals :: Function f => State f -> State f
normaliseGoals state@State{..} =
  state {
    st_goals = map (normalForms (rewrite reduces st_rules) . Set.toList) st_goals }

-- Record an equation as being joinable.
addJoinable :: Equation f -> State f -> State f
addJoinable (t :=: u) state =
  state {
    st_joinable =
      Index.insert t (t :=: u) (st_joinable state) }

-- Try to join a critical pair.
{-# INLINEABLE consider #-}
consider :: Function f => Config -> State f -> Overlap f -> State f
consider config state@State{..} overlap0 =
  {-# SCC consider #-}
  let
    -- Important to canonicalise the rule so that we don't get
    -- bigger and bigger variable indices over time
    overlap = canonicalise overlap0
  in
    case joinOverlap st_joinable st_rules overlap of
      Left eqns ->
        foldl' addJoinable state eqns
      Right (overlap, model) ->
        let
          rules =
            [ \n ->
              TweeRule {
                rule_id = n,
                rule_rule = rule,
                rule_positions = positions (lhs rule),
                rule_overlap = overlap,
                rule_model = model }
            | rule <- orient (overlap_eqn overlap) ]
        in
          foldl' (addRule config) state rules

-- Add a new equation.
{-# INLINEABLE newEquation #-}
newEquation :: Function f => Config -> State f -> Equation f -> State f
newEquation config state eqn =
  consider config state $
    Overlap {
      overlap_top = empty,
      overlap_inner = empty,
      overlap_pos = 0,
      overlap_eqn = eqn }

----------------------------------------------------------------------
-- The main loop.
----------------------------------------------------------------------

{-# INLINEABLE complete #-}
complete :: Function f => Config -> State f -> State f
complete config state
  | st_considered state >= cfg_max_critical_pairs config = state
  | solved state = state
  | otherwise =
    case dequeue config state of
      (Nothing, state) -> state
      (Just overlap, state) ->
        let state' = consider config state overlap in
        (if unId (st_label state-1) `div` 100 /= unId (st_label state'-1) `div` 100 then trace (report state') else id) $
        complete config state'

{-# INLINEABLE solved #-}
solved :: Function f => State f -> Bool
solved State{st_goals = goal:goals} =
  not (null (foldl' Set.intersection goal goals))
solved _ = False

{-# INLINEABLE report #-}
report :: Function f => State f -> String
report State{..} =
  printf "\n%% Statistics:\n" ++
  printf "%%   %d rules, of which %d oriented, %d unoriented, %d permutative, %d weakly oriented.\n"
    (length orients)
    (length [ () | Oriented <- orients ])
    (length [ () | Unoriented <- orients ])
    (length [ () | Permutative{} <- orients ])
    (length [ () | WeaklyOriented{} <- orients ]) ++
  printf "%%   %d queued critical pairs.\n" queuedPairs ++
  printf "%%   %d critical pairs considered so far.\n" st_considered
  where
    orients = map (orientation . the) (Index.elems st_rules)
    queuedPairs = Heap.size st_queue
