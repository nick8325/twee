{-# LANGUAGE RecordWildCards, MultiParamTypeClasses, GADTs, BangPatterns #-}
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
import Text.Printf
import Debug.Trace

----------------------------------------------------------------------
-- Configuration and prover state.
----------------------------------------------------------------------

data Config =
  Config {
    cfg_max_term_size     :: Maybe Int,
    cfg_critical_pairs    :: CP.Config,
    cfg_split_cp_set_at   :: Int,
    cfg_split_cp_set_into :: Int }

data State f =
  State {
    st_oriented_rules :: !(Index f (TweeRule f)),
    st_rules          :: !(Index f (TweeRule f)),
    st_rule_ids       :: !(IntMap (TweeRule f)),
    st_joinable       :: !(Index f (Equation f)),
    st_goals          :: [Term f],
    st_queue          :: !(Heap (Passive f)),
    st_label          :: {-# UNPACK #-} !Id,
    st_considered     :: {-# UNPACK #-} !Int }

defaultConfig :: Config
defaultConfig =
  Config {
    cfg_max_term_size = Nothing,
    cfg_critical_pairs =
      CP.Config {
        cfg_lhsweight = 2,
        cfg_rhsweight = 1,
        cfg_funweight = 2 },
    cfg_split_cp_set_at = 5,
    cfg_split_cp_set_into = 5 }

initialState :: State f
initialState =
  State {
    st_oriented_rules = Index.Nil,
    st_rules = Index.Nil,
    st_rule_ids = IntMap.empty,
    st_joinable = Index.Nil,
    st_goals = [],
    st_queue = Heap.empty,
    st_label = 0,
    st_considered = 0 }

----------------------------------------------------------------------
-- The CP queue.
----------------------------------------------------------------------

data Passive f =
  -- A single critical pair
  SingleCP {
    passive_rule1   :: {-# UNPACK #-} !Id,
    passive_rule2   :: {-# UNPACK #-} !Id,
    passive_score   :: {-# UNPACK #-} !Int,
    passive_overlap :: {-# UNPACK #-} !(Overlap f) } |
  -- All critical pairs between one rule and an interval of rules
  ManyCPs {
    passive_rule1      :: {-# UNPACK #-} !Id,
    passive_rule2_lo   :: {-# UNPACK #-} !Id,
    passive_rule2_hi   :: {-# UNPACK #-} !Id,
    passive_count      :: {-# UNPACK #-} !Int,
    passive_rule2      :: {-# UNPACK #-} !Id,
    passive_score      :: {-# UNPACK #-} !Int }
  deriving Show

instance Eq (Passive f) where x == y = compare x y == EQ
instance Ord (Passive f) where
  compare = comparing $ \passive ->
    (passive_score passive, passive_rule1 passive, passive_rule2 passive)

-- Compute all critical pairs from a rule and condense into a Passive.
-- Takes an optional range of rules to use.
{-# INLINEABLE makePassive #-}
makePassive :: Function f => Config -> State f -> Maybe (Id, Id) -> Id -> [Passive f]
makePassive Config{..} State{..} mrange id =
  case IntMap.lookup (unId id) st_rule_ids of
    Nothing -> []
    Just rule
      | unId (hi-lo+1) <= cfg_split_cp_set_at ->
        [ SingleCP (rule_id rule) (rule_id rule') (score cfg_critical_pairs o) o
        | (rule', o) <- overlaps st_oriented_rules rules rule ]
      | otherwise ->
        case bestOverlap cfg_critical_pairs st_oriented_rules rules rule of
          Nothing -> []
          Just Best{..} -> [ManyCPs (rule_id rule) lo hi best_count best_id best_score]
  where
    (lo, hi) = fromMaybe (0, id) mrange
    rules =
      IntMap.elems $
      fst $ IntMap.split (unId (hi+1)) $
      snd $ IntMap.split (unId (lo-1)) st_rule_ids

-- Renormalise a queued Passive.
-- Also takes care of deleting any orphans.
{-# INLINEABLE simplifyPassive #-}
simplifyPassive :: Function f => Config -> State f -> Passive f -> [Passive f]
simplifyPassive Config{..} state@State{..} passive@SingleCP{..}
  | passiveAlive state passive =
    case simplifyOverlap st_oriented_rules passive_overlap of
      Nothing -> []
      Just overlap ->
        [passive {
           passive_score = score cfg_critical_pairs overlap,
           passive_overlap = overlap }]
  | otherwise = []
simplifyPassive config@Config{..} state@State{..} ManyCPs{..} =
  makePassive config state (Just (passive_rule2_lo, passive_rule2_hi)) passive_rule1

-- Check if a Passive is an orphan.
passiveAlive :: State f -> Passive f -> Bool
passiveAlive State{..} SingleCP{..} =
  unId passive_rule1 `IntMap.member` st_rule_ids &&
  unId passive_rule2 `IntMap.member` st_rule_ids
passiveAlive State{..} ManyCPs{..} =
  unId passive_rule1 `IntMap.member` st_rule_ids

-- Renormalise the entire queue.
{-# INLINEABLE simplifyQueue #-}
simplifyQueue :: Function f => Config -> State f -> State f
simplifyQueue config state =
  state { st_queue = simp (st_queue state) }
  where
    simp =
      Heap.fromList .
      concatMap (simplifyPassive config state) .
      Heap.toUnsortedList

-- Enqueue a critical pair.
{-# INLINEABLE enqueue #-}
enqueue :: Function f => Config -> State f -> Passive f -> State f
enqueue config state passive =
  state { st_queue = Heap.insert passive (st_queue state) }

-- Dequeue a critical pair.
-- Also takes care of:
--   * removing any orphans from the head of the queue
--   * splitting ManyCPs up as necessary
--   * ignoring CPs that are too big
{-# INLINEABLE dequeue #-}
dequeue :: Function f => Config -> State f -> (Maybe (Overlap f), State f)
dequeue config@Config{..} state@State{..} =
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
      case passive of
        _ | not (passiveAlive state passive) -> deq n queue
        SingleCP{..} ->
          case simplifyOverlap st_oriented_rules passive_overlap of
            Just overlap@Overlap{overlap_eqn = t :=: u}
              | size t <= fromMaybe maxBound cfg_max_term_size,
                size u <= fromMaybe maxBound cfg_max_term_size ->
                return (overlap, n+1, queue)
            _ -> deq (n+1) queue
        ManyCPs{..} ->
          let
            splits =
              (passive_rule2, passive_rule2):
              splitInterval k (passive_rule2_lo, passive_rule2-1) ++
              splitInterval k (passive_rule2+1, passive_rule2_hi)
            k = fromIntegral cfg_split_cp_set_into
          in
            deq n $ foldr Heap.insert queue $ concat
              [ makePassive config state (Just range) passive_rule1
              | range <- splits ]

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
addRule :: Function f => Config -> State f -> TweeRule f -> State f
addRule config state rule0 =
  let
    -- Important to canonicalise the rule so that we don't get
    -- bigger and bigger variable indices over time
    rule = rule0 { rule_rule = canonicalise (rule_rule rule0) }
    state' =
      state {
        st_oriented_rules =
          if oriented (orientation (rule_rule rule))
          then Index.insert (lhs (rule_rule rule)) rule (st_oriented_rules state)
          else st_oriented_rules state,
        st_rules = Index.insert (lhs (rule_rule rule)) rule (st_rules state),
        st_rule_ids = IntMap.insert (unId (rule_id rule)) rule (st_rule_ids state) }
    passives =
      makePassive config state' Nothing (rule_id rule)
  in
    traceShow (pPrint (unId (rule_id rule)) <> text ". " <> pPrint (rule_rule rule)) $
    normaliseGoals $
    foldl' (enqueue config) state' passives

-- Normalise all goals.
{-# INLINEABLE normaliseGoals #-}
normaliseGoals :: Function f => State f -> State f
normaliseGoals state@State{..} =
  state {
    st_goals = map (result . normaliseWith (rewrite reduces st_rules)) st_goals }

-- Record an equation as being joinable.
addJoinable :: Equation f -> State f -> State f
addJoinable (t :=: u) state =
  state {
    st_joinable =
      Index.insert t (t :=: u) (st_joinable state) }

-- Try to join a critical pair.
{-# INLINEABLE consider #-}
consider :: Function f => Config -> State f -> Overlap f -> State f
consider config state@State{..} overlap =
  case joinOverlap st_joinable st_rules overlap of
    Left eqns ->
      foldr addJoinable state eqns
    Right (overlap, model) ->
      let
        rules =
          [ TweeRule {
              rule_id = n,
              rule_rule = rule,
              rule_positions = positions (lhs rule),
              rule_overlap = overlap,
              rule_model = model }
          | (n, rule) <-
            zip [st_label..] (orient (overlap_eqn overlap)) ]
        state' =
          state {
            st_label = st_label + fromIntegral (length rules) }
      in
        -- XXX usort not quite right - should give a "second chance"
        -- to each rule. Unidirectional join?
        foldl' (addRule config) state' (nubBy ((==) `on` (canonicalise . rule_rule)) rules)

-- Add a new equation.
{-# INLINEABLE newEquation #-}
newEquation :: Function f => Config -> State f -> Equation f -> State f
newEquation config state eqn =
  consider config state $
    Overlap {
      overlap_top = empty,
      overlap_inner = empty,
      overlap_eqn = eqn }

----------------------------------------------------------------------
-- The main loop.
----------------------------------------------------------------------

{-# INLINEABLE complete #-}
complete :: Function f => Config -> State f -> State f
complete config state
  | solved state = state
  | otherwise =
    case dequeue config state of
      (Nothing, state) -> state
      (Just overlap, state) ->
        let state' = consider config state overlap in
        (if unId (st_label state) `div` 100 /= unId (st_label state') `div` 100 then trace (report state') else id) $
        complete config state'

{-# INLINEABLE solved #-}
solved :: Function f => State f -> Bool
solved State{..} = nub st_goals /= st_goals

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
  printf "%%   %d queued critical pairs compressed into %d entries (reduced by %d%%).\n"
    queuedPairs
    compressedPairs
    (100 - (100 * compressedPairs `div` (queuedPairs `max` 1))) ++
  printf "%%   %d critical pairs considered so far.\n"
    st_considered
  where
    orients = map (orientation . the) (Index.elems st_rules)
    queuedPairs = sum (map passiveCount (Heap.toUnsortedList st_queue))
    passiveCount SingleCP{} = 1
    passiveCount ManyCPs{..} = passive_count
    compressedPairs = length (Heap.toUnsortedList st_queue)
