{-# LANGUAGE RecordWildCards, MultiParamTypeClasses, GADTs, BangPatterns, OverloadedStrings, ScopedTypeVariables #-}
module Twee where

import Twee.Base
import Twee.Rule
import Twee.Equation
import qualified Twee.Proof as Proof
import Twee.Proof(Proof, Axiom(..), ProvedGoal(..), Lemma(..))
import Twee.CP hiding (Config)
import qualified Twee.CP as CP
import Twee.Join
import qualified Twee.Index as Index
import Twee.Index(Index)
import Twee.Constraints
import qualified Data.Heap as Heap
import Data.Heap(Heap)
import qualified Data.IntMap.Strict as IntMap
import Data.IntMap(IntMap)
import Data.Maybe
import Data.List
import Data.Function
import qualified Data.Set as Set
import Data.Set(Set)
import qualified Data.IntSet as IntSet
import Data.IntSet(IntSet)
import Text.Printf
import Data.Int
import Control.Monad

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
    st_goals          :: ![Goal f],
    st_queue          :: !(Heap (Passive f)),
    st_label          :: {-# UNPACK #-} !Id,
    st_considered     :: {-# UNPACK #-} !Int,
    st_messages_rev   :: ![Message f] }

-- For goal terms we store the set of all their normal forms.
-- Name and number are for information only.
data Goal f =
  Goal {
    goal_name   :: String,
    goal_number :: Int,
    goal_eqn    :: Equation f,
    goal_lhs    :: Set (Resulting f),
    goal_rhs    :: Set (Resulting f) }

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
        cfg_varweight = 3 } }

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
    st_considered = 0,
    st_messages_rev = [] }

----------------------------------------------------------------------
-- Messages.
----------------------------------------------------------------------

data Message f =
    NewRule !(TweeRule f)
  | NewEquation !Id !(Equation f)

instance PrettyTerm f => Pretty (Message f) where
  pPrint (NewRule rule) =
    pPrint (rule_versionedid rule) <> text "." <+> pPrint (rule_rule rule)
  pPrint (NewEquation n eqn) =
    text (replicate digits 'x') <> text "." <+> pPrint eqn
    where
      digits = length (show (unId n))

message :: Message f -> State f -> State f
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
    passive_score   :: {-# UNPACK #-} !Int32,
    passive_rule1   :: {-# UNPACK #-} !Id,
    passive_rule2   :: {-# UNPACK #-} !Id,
    passive_pos     :: {-# UNPACK #-} !Int32 }
  deriving (Eq, Ord, Show)

-- Compute all critical pairs from a rule and condense into a Passive.
-- Takes an optional range of rules to use.
{-# INLINEABLE makePassive #-}
makePassive :: Function f => Config -> State f -> Maybe (Id, Id) -> Id -> [Passive f]
makePassive Config{..} State{..} mrange id =
  {-# SCC makePassive #-}
  case IntMap.lookup (fromIntegral id) st_rule_ids of
    Nothing -> []
    Just rule ->
      [ Passive (fromIntegral (score cfg_critical_pairs o)) (rule_id rule1) (rule_id rule2) (fromIntegral (overlap_pos o))
      | (rule1, rule2, o) <- overlaps st_oriented_rules rules rule ]
  where
    (lo, hi) = fromMaybe (0, id) mrange
    rules =
      IntMap.elems $
      fst $ IntMap.split (fromIntegral (hi+1)) $
      snd $ IntMap.split (fromIntegral (lo-1)) st_rule_ids

-- Turn a Passive back into an overlap.
-- Doesn't try to simplify it.
{-# INLINEABLE findPassive #-}
findPassive :: forall f. Function f => Config -> State f -> Passive f -> Maybe (TweeRule f, TweeRule f, Overlap f)
findPassive Config{..} State{..} Passive{..} = {-# SCC findPassive #-} do
  rule1 <- IntMap.lookup (fromIntegral passive_rule1) st_rule_ids
  rule2 <- IntMap.lookup (fromIntegral passive_rule2) st_rule_ids
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
-- Rules.
----------------------------------------------------------------------

data TweeRule f =
  TweeRule {
    rule_id        :: {-# UNPACK #-} !Id,
    rule_version   :: {-# UNPACK #-} !Int,
    rule_rule      :: {-# UNPACK #-} !(Rule f),
    -- Positions at which the rule can form CPs
    rule_positions :: !(Positions f),
    -- Models in which the rule is false (used when reorienting)
    rule_models    :: [Model f],
    -- Proof of the rule
    rule_proof     :: !(Proof f),
    -- Lemmas used in the proof (computed from rule_proof)
    rule_lemmas    :: !IntSet }

instance Eq (TweeRule f) where
  (==) = (==) `on` rule_id

instance f ~ g => Has (TweeRule f) (Rule g) where the = rule_rule
instance f ~ g => Has (TweeRule f) (Positions g) where the = rule_positions
instance f ~ g => Has (TweeRule f) (Proof g) where the = rule_proof
instance Has (TweeRule f) Id where the = rule_id
instance Has (TweeRule f) VersionedId where the = rule_versionedid

rule_versionedid :: TweeRule f -> VersionedId
rule_versionedid TweeRule{..} = VersionedId rule_id rule_version

-- Add a new rule.
{-# INLINEABLE addRule #-}
addRule :: Function f => Config -> State f -> (Id -> TweeRule f) -> State f
addRule config state@State{..} rule0 =
  {-# SCC addRule #-}
  let
    rule = rule0 st_label
    state' =
      message (NewRule rule) $
      state {
        st_oriented_rules =
          if oriented (orientation (rule_rule rule))
          then Index.insert (lhs (rule_rule rule)) rule st_oriented_rules
          else st_oriented_rules,
        st_rules = Index.insert (lhs (rule_rule rule)) rule st_rules,
        st_rule_ids = IntMap.insert (fromIntegral (rule_id rule)) rule st_rule_ids,
        st_label = st_label+1 }
    passives =
      makePassive config state' Nothing (rule_id rule)
  in if subsumed Asymmetric st_joinable st_rules (unorient (rule_rule rule)) then
    state
  else
    normaliseGoals $
    foldl' enqueue state' passives

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

-- Record an equation as being joinable.
{-# INLINEABLE addJoinable #-}
addJoinable :: Function f => State f -> Equation f -> State f
addJoinable state eqn@(t :=: u) =
  message (NewEquation (st_label state) eqn) $
  state {
    st_joinable =
      Index.insert t (t :=: u) (st_joinable state) }

-- Try to join a critical pair.
{-# INLINEABLE consider #-}
consider :: Function f => Config -> State f -> CriticalPair f -> State f
consider config state@State{..} cp0 =
  {-# SCC consider #-}
  -- Important to canonicalise the rule so that we don't get
  -- bigger and bigger variable indices over time
  let cp = canonicalise cp0 in
  case joinCriticalPair st_joinable st_rules cp of
    Right (mcp, cps) ->
      let
        state' = foldl' (consider config) state cps
      in case mcp of
        Just cp -> addJoinable state' (cp_eqn cp)
        Nothing -> state'

    Left (cp, model) ->
      let
        rules =
          [ \n ->
            let p = Proof.certify (prf (cp_proof cp)) in
            TweeRule {
              rule_id = n,
              rule_version = 0,
              rule_rule = rule,
              rule_positions = positions (lhs rule),
              rule_models = [model],
              rule_proof = p,
              rule_lemmas =
                IntSet.fromList $
                  map (fromIntegral . versioned_id . lemma_id)
                    (Proof.usedLemmas (Proof.derivation p)) }
          | (rule, prf) <- orient (cp_eqn cp) ]
      in
        foldl' (addRule config) state rules

-- Add a new equation.
{-# INLINEABLE addAxiom #-}
addAxiom :: Function f => Config -> State f -> Axiom f -> State f
addAxiom config state axiom =
  consider config state $
    CriticalPair {
      cp_eqn = axiom_eqn axiom,
      cp_top = Nothing,
      cp_proof = Proof.axiom axiom }

-- Add a new goal.
{-# INLINEABLE addGoal #-}
addGoal :: Function f => Config -> State f -> Goal f -> State f
addGoal _config state@State{..} goal =
  normaliseGoals state { st_goals = goal:st_goals }

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

-- data Simplification f = Simplify [Model f] | Reorient
--
-- reduce :: Function f => Config -> State f -> Rule f -> TweeRule f -> Maybe (Simplification f)
-- reduce config state@State{..} new oldRule@TweeRule{rule_rule = old, rule_models = models} =
--   guarded lhs reorient `mplus` guarded rhs simplify
--   where
--     reorient = undefined
--       -- guard . not . null . concat $
--       --   [ anywhere (tryRule (reducesInModel model) new) (f old)
--       --   | model <- models ]
--
--     simplify =
--       case anywhere (tryRule reduces new) (rhs old) of
--         [] -> Nothing
--         _  -> Just (Simplify models)
--
--     guarded f x = do
--       guard (any isJust [ match (lhs new) t | t <- subterms (f old) ])
--       x
--
--     rules = Index.delete (lhs old) oldRule st_rules
--     oriented_rules = Index.delete (lhs old) oldRule st_oriented_rules

-- reduceWith :: Function f => Twee f -> Label -> Rule f -> Modelled (Critical (Rule f)) -> Maybe (Simplification f)
-- reduceWith s lab new old0@(Modelled model _ (Critical info old@(Rule _ l r)))
--   | not (isWeak new) &&
--     not (lhs new `isInstanceOf` l) &&
--     not (null (anywhere (tryRule reduces new) l)) =
--       Just (Reorient old0)
--   | not (isWeak new) &&
--     not (lhs new `isInstanceOf` l) &&
--     not (oriented (orientation new)) &&
--     not (all isNothing [ match (lhs new) l' | l' <- subterms l ]) &&
--     modelJoinable =
--     tryGroundJoin
--   | not (null (anywhere (tryRule reduces new) (rhs old))) =
--       Just (Simplify model old0)
--   | not (oriented (orientation old)) &&
--     not (oriented (orientation new)) &&
--     not (lhs new `isInstanceOf` r) &&
--     not (all isNothing [ match (lhs new) r' | r' <- subterms r ]) &&
--     modelJoinable =
--     tryGroundJoin
--   | otherwise = Nothing
--   where
--     s' = s { labelledRules = Indexes.delete (Labelled lab old0) (labelledRules s) }
--     modelJoinable = isLeft (normaliseCP s' (Critical info (lm :=: rm)))
--     lm = result (normaliseIn s' model l)
--     rm = result (normaliseIn s' model r)
--     tryGroundJoin =
--       case groundJoin s' (branches (And [])) (Critical info (l :=: r)) of
--         Left model' ->
--           Just (Simplify model' old0)
--         Right _ ->
--           Just (Reorient old0)
--     isWeak (Rule (WeaklyOriented _) _ _) = True
--     isWeak _ = False

----------------------------------------------------------------------
-- The main loop.
----------------------------------------------------------------------

data Output m f =
  Output {
    output_report  :: State f -> m (),
    output_message :: Message f -> m () }

{-# INLINE complete #-}
complete :: (Function f, Monad m) => Output m f -> Config -> State f -> m (State f)
complete output@Output{..} config state =
  let (progress, state') = complete1 config state in do
    mapM_ output_message (messages state')
    when (st_label state `div` 100 /= st_label state' `div` 100) $
      output_report state'
    if progress then
      complete output config (clearMessages state')
    else return state'

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
