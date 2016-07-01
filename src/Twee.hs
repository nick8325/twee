-- Knuth-Bendix completion, with lots of exciting tricks for
-- unorientable equations.

{-# LANGUAGE CPP, TypeFamilies, FlexibleContexts, RecordWildCards, ScopedTypeVariables, UndecidableInstances, StandaloneDeriving, PatternGuards, BangPatterns, OverloadedStrings, DeriveGeneric #-}
module Twee where

#include "errors.h"
import Twee.Base hiding (empty, lookup)
import Twee.Constraints hiding (funs)
import Twee.Rule
import qualified Twee.Index.Split as Indexes
import Twee.Index.Split(Indexes, Rated(..))
import qualified Twee.Index.Simple as Index
import Twee.Index.Simple(Index, Frozen)
import Twee.Queue hiding (queue)
import Twee.Utils
import Control.Monad
import Data.Maybe
import Data.Ord
import qualified Debug.Trace
import Control.Monad.Trans.State.Strict
import Data.List
import Text.Printf
import qualified Data.Set as Set
import Data.Set(Set)
import Data.Either
import qualified Data.Map.Strict as Map
import Data.Map.Strict(Map)
import Data.List.Split
import Twee.Profile
import GHC.Generics

--------------------------------------------------------------------------------
-- Completion engine state.
--------------------------------------------------------------------------------

data Twee f =
  Twee {
    maxSize           :: Maybe Int,
    labelledRules     :: {-# UNPACK #-} !(Indexes (Labelled (Modelled (Critical (Rule f))))),
    extraRules        :: {-# UNPACK #-} !(Indexes (Rule f)),
    cancellationRules :: !(Index (Labelled (CancellationRule f))),
    goals             :: [Set (Term f)],
    totalCPs          :: Int,
    processedCPs      :: Int,
    renormaliseAt     :: Int,
    minimumCPSetSize  :: Int,
    cpSplits          :: Int,
    queue             :: !(Queue (Mix (Either1 FIFO Heap)) (Passive f)),
    renormalise :: Bool,
    useGeneralSuperpositions :: Bool,
    useGroundJoining  :: Bool,
    useConnectedness  :: Bool,
    useSetJoining     :: Bool,
    useSetJoiningForGoals :: Bool,
    useCancellation :: Bool,
    maxCancellationSize :: Maybe Int,
    atomicCancellation :: Bool,
    unifyConstantsInCancellation :: Bool,
    skipCompositeSuperpositions :: Bool,
    tracing :: Bool,
    moreTracing :: Bool,
    lhsWeight         :: Int,
    rhsWeight         :: Int,
    joinStatistics    :: Map JoinReason Int }
  deriving Show

initialState :: Int -> Int -> Twee f
initialState mixFIFO mixPrio =
  Twee {
    maxSize           = Nothing,
    labelledRules     = Indexes.empty,
    extraRules        = Indexes.empty,
    cancellationRules = Index.nil,
    goals             = [],
    totalCPs          = 0,
    processedCPs      = 0,
    renormaliseAt     = 50,
    minimumCPSetSize  = 20,
    cpSplits          = 20,
    queue             = empty (emptyMix mixFIFO mixPrio (Left1 emptyFIFO) (Right1 emptyHeap)),
    renormalise = False,
    useGeneralSuperpositions = True,
    useGroundJoining  = True,
    useConnectedness  = True,
    useSetJoining     = False,
    useSetJoiningForGoals = True,
    useCancellation = True,
    atomicCancellation = True,
    maxCancellationSize = Nothing,
    unifyConstantsInCancellation = False,
    skipCompositeSuperpositions = True,
    tracing = True,
    moreTracing = False,
    lhsWeight         = 2,
    rhsWeight         = 1,
    joinStatistics    = Map.empty }

addGoals :: [Set (Term f)] -> Twee f -> Twee f
addGoals gs s = s { goals = gs ++ goals s }

report :: Function f => Twee f -> String
report Twee{..} =
  printf "Rules: %d total, %d oriented, %d unoriented, %d permutative, %d weakly oriented. "
    (length rs)
    (length [ () | Rule Oriented _ _ <- rs ])
    (length [ () | Rule Unoriented _ _ <- rs ])
    (length [ () | (Rule (Permutative _) _ _) <- rs ])
    (length [ () | (Rule (WeaklyOriented _) _ _) <- rs ]) ++
  printf "%d extra. %d historical.\n"
    (length (Indexes.elems extraRules))
    n ++
  printf "Critical pairs: %d total, %d processed, %d queued compressed into %d.\n\n"
    totalCPs
    processedCPs
    s
    (length (toList queue)) ++
  printf "Critical pairs joined:\n" ++
  concat [printf "%6d %s.\n" n (prettyShow x) | (x, n) <- Map.toList joinStatistics]
  where
    rs = map (critical . modelled . peel) (Indexes.elems labelledRules)
    Label n = nextLabel queue
    s = sum (map passiveCount (toList queue))

enqueueM :: Function f => Passive f -> StateT (Twee f) IO ()
enqueueM cps = do
  traceM (NewCP cps)
  modify' $ \s -> s {
    queue    = enqueue cps (queue s),
    totalCPs = totalCPs s + passiveCount cps }

reenqueueM :: Function f => Passive f -> StateT (Twee f) IO ()
reenqueueM cps = do
  modify' $ \s -> s {
    queue    = reenqueue cps (queue s) }

dequeueM :: Function f => StateT (Twee f) IO (Maybe (Passive f))
dequeueM =
  state $ \s ->
    case dequeue (queue s) of
      Nothing -> (Nothing, s)
      Just (x, q) -> (Just x, s { queue = q })

newLabelM :: StateT (Twee f) IO Label
newLabelM =
  state $ \s ->
    case newLabel (queue s) of
      (l, q) -> (l, s { queue = q })

data Modelled a =
  Modelled {
    model     :: Model (ConstantOf a),
    positions :: [Int],
    modelled  :: a }

instance Eq a => Eq (Modelled a) where x == y = modelled x == modelled y
instance Ord a => Ord (Modelled a) where compare = comparing modelled

instance (PrettyTerm (ConstantOf a), Pretty a) => Pretty (Modelled a) where
  pPrint Modelled{..} = pPrint modelled

deriving instance (Show a, Show (ConstantOf a)) => Show (Modelled a)

instance Symbolic a => Symbolic (Modelled a) where
  type ConstantOf (Modelled a) = ConstantOf a

  termsDL = termsDL . modelled
  replace f Modelled{..} = Modelled model positions (replace f modelled)

instance Singular a => Singular (Modelled a) where
  term = term . modelled

--------------------------------------------------------------------------------
-- Rewriting.
--------------------------------------------------------------------------------

instance Rated a => Rated (Labelled a) where
  rating = rating . peel
  maxRating = maxRating . peel
instance Rated a => Rated (Modelled a) where
  rating = rating . modelled
  maxRating = maxRating . modelled
instance Rated a => Rated (Critical a) where
  rating = rating . critical
  maxRating = maxRating . critical
instance Rated (Rule f) where
  rating (Rule Oriented _ _) = 0
  rating (Rule WeaklyOriented{} _ _) = 0
  rating _ = 1
  maxRating _ = 1

{-# INLINE rulesFor #-}
rulesFor :: Function f => Int -> Twee f -> Frozen (Rule f)
rulesFor n k =
  Index.map (critical . modelled . peel) (Indexes.freeze n (labelledRules k))

easyRules, rules, allRules :: Function f => Twee f -> Frozen (Rule f)
easyRules k = rulesFor 0 k
rules k = rulesFor 1 k `Index.union` Indexes.freeze 0 (extraRules k)
allRules k = rulesFor 1 k `Index.union` Indexes.freeze 1 (extraRules k)

normaliseQuickly :: Function f => Twee f -> Term f -> Reduction f
normaliseQuickly s t = normaliseWith (rewrite "simplify" simplifies (easyRules s)) t

normalise :: Function f => Twee f -> Term f -> Reduction f
normalise s t = normaliseWith (rewrite "reduce" reduces (rules s)) t

normaliseIn :: Function f => Twee f -> Model f -> Term f -> Reduction f
normaliseIn s model t =
  normaliseWith (rewrite "model" (reducesInModel model) (rules s)) t

normaliseSub :: Function f => Twee f -> Term f -> Term f -> Reduction f
normaliseSub s top t
  | useConnectedness s && lessEq t top && isNothing (unify t top) =
    normaliseWith (rewrite "sub" (reducesSub top) (rules s)) t
  | otherwise = Parallel [] t

normaliseSkolem :: Function f => Twee f -> Term f -> Reduction f
normaliseSkolem s t = normaliseWith (rewrite "skolem" reducesSkolem (rules s)) t

reduceCP ::
  Function f =>
  Twee f -> JoinStage -> (Term f -> Term f) ->
  Critical (Equation f) -> Either JoinReason (Critical (Equation f))
reduceCP s stage f (Critical top (t :=: u))
  | t' == u' = Left (Trivial stage)
  | subsumed s t' u' = Left (Subsumed stage)
  | otherwise = Right (Critical top (t' :=: u'))
  where
    t' = stamp "reduce lhs of critical pair" $ f t
    u' = stamp "reduce rhs of critical pair" $ f u

    subsumed s t u = stamp "checking critical pair for subsumption" $ subsumed1 s t u
    subsumed1 s t u = here || there t u
      where
        here =
          or [ rhs x == u | x <- Index.lookup t rs ]
        there (Var x) (Var y) | x == y = True
        there (Fun f ts) (Fun g us) | f == g = and (zipWith (subsumed1 s) (fromTermList ts) (fromTermList us))
        there _ _ = False
        rs = allRules s

data JoinStage = Initial | Simplification | Reducing | Subjoining deriving (Eq, Ord, Show)
data JoinReason = Trivial JoinStage | Subsumed JoinStage | SetJoining | GroundJoined deriving (Eq, Ord, Show)

instance Pretty JoinStage where
  pPrint Initial        = text "no rewriting"
  pPrint Simplification = text "simplification"
  pPrint Reducing       = text "reduction"
  pPrint Subjoining     = text "connectedness testing"

instance Pretty JoinReason where
  pPrint (Trivial stage)  = text "joined after" <+> pPrint stage
  pPrint (Subsumed stage) = text "subsumed after" <+> pPrint stage
  pPrint SetJoining       = text "joined with set of normal forms"
  pPrint GroundJoined     = text "ground joined"

normaliseCPQuickly, normaliseCPReducing, normaliseCP ::
  Function f =>
  Twee f -> Critical (Equation f) -> Either JoinReason (Critical (Equation f))
normaliseCPQuickly s cp =
  reduceCP s Initial id cp >>=
  reduceCP s Simplification (result . normaliseQuickly s)

normaliseCPReducing s cp =
  normaliseCPQuickly s cp >>=
  reduceCP s Reducing (result . normalise s)

normaliseCP s cp@(Critical info _) =
  case (cp1, cp2, cp3, cp4) of
    (Right cp, Right _, Right _, Right _) -> Right cp
    (Right _, Right _, Right _, Left x) -> Left x
    (Right _, Right _, Left x, _) -> Left x
    (Right _, Left x, _, _) -> Left x
    (Left x, _, _, _) -> Left x
  where
    cp1 =
      normaliseCPReducing s cp >>=
      reduceCP s Subjoining (result . normaliseSub s (top info))

    cp2 =
      normaliseCPReducing s cp >>=
      reduceCP s Subjoining (result . normaliseSub s (flipCP (top info))) . flipCP

    cp3 = setJoin cp
    cp4 = setJoin (flipCP cp)

    flipCP :: Symbolic a => a -> a
    flipCP t = replace (substList sub) t
      where
        n = maximum (0:map fromEnum (vars t))
        sub (V x) = var (V (n - x))

    -- XXX shouldn't this also check subsumption?
    setJoin (Critical info (t :=: u))
      | not (useSetJoining s) ||
        Set.null (norm t `Set.intersection` norm u) =
        Right (Critical info (t :=: u))
      | otherwise =
        Debug.Trace.traceShow (sep [text "Joined", nest 2 (pPrint (Critical info (t :=: u))), text "to", nest 2 (pPrint v)])
        Left SetJoining
      where
        norm t
          | lessEq t (top info) && isNothing (unify t (top info)) =
            normalForms (rewrite "setjoin" (reducesSub (top info)) (rules s)) [t]
          | otherwise = Set.singleton t
        v = Set.findMin (norm t `Set.intersection` norm u)

--------------------------------------------------------------------------------
-- Completion loop.
--------------------------------------------------------------------------------

complete :: Function f => StateT (Twee f) IO ()
complete = do
  res <- complete1
  when res complete

complete1 :: Function f => StateT (Twee f) IO Bool
complete1 = stampM "completion loop" complete2

complete2 :: Function f => StateT (Twee f) IO Bool
complete2 = do
  Twee{..} <- get
  let Label n = nextLabel queue
  when (n >= renormaliseAt) $ stampM "normalise critical pairs" $ do
    normaliseCPs
    modify (\s -> s { renormaliseAt = renormaliseAt * 3 `div` 2 })

  res <- stampM "dequeue" dequeueM
  case res of
    Just (SingleCP (CP info cp l1 l2)) -> stampM "consider critical pair" $ do
      res <- consider (cpWeight info) l1 l2 cp
      when res renormaliseGoals
      return True
    Just (ManyCPs (CPs _ l lower upper _ rule)) -> stampM "split critical pair" $ do
      s <- get
      queueCPsSplit reenqueueM lower (l-1) rule
      mapM_ (reenqueueM . SingleCP) (toCPs s l l rule)
      queueCPsSplit reenqueueM (l+1) upper rule
      complete2
    Nothing ->
      return False

renormaliseGoals :: Function f => StateT (Twee f) IO ()
renormaliseGoals = do
  Twee{..} <- get
  if useSetJoiningForGoals then
    modify $ \s -> s { goals = map (normalForms (rewrite "goal" reduces (rules s)) . Set.toList) goals }
  else
    modify $ \s -> s { goals = map (Set.fromList . map (result . normaliseWith (rewrite "goal" reduces (rules s))) . Set.toList) goals }

normaliseCPs :: forall f. Function f => StateT (Twee f) IO ()
normaliseCPs = do
  s@Twee{..} <- get
  when renormalise $ do
    traceM (NormaliseCPs s)
    put s { queue = emptyFrom queue }
    forM_ (toList queue) $ \cp ->
      case cp of
        SingleCP (CP _ cp l1 l2) -> queueCP enqueueM trivial l1 l2 cp
        ManyCPs (CPs _ _ lower upper _ rule) -> queueCPs enqueueM lower upper (const []) rule
    modify (\s -> s { totalCPs = totalCPs })

consider ::
  Function f =>
  Int -> Label -> Label -> Critical (Equation f) -> StateT (Twee f) IO Bool
consider w l1 l2 pair = do
  traceM (Consider pair)
  modify' (\s -> s { processedCPs = processedCPs s + 1 })
  s <- get
  let record reason = modify' (\s -> s { joinStatistics = Map.insertWith (+) reason 1 (joinStatistics s) })
      hard (Trivial Subjoining) = True
      hard (Subsumed Subjoining) = True
      hard SetJoining = True
      hard _ = False
      tooBig (Critical _ (t :=: u)) =
        case maxSize s of
          Nothing -> False
          Just sz -> size t > sz || size u > sz
      hardJoinable = isLeft . normaliseCPReducing s . Critical noCritInfo
  if tooBig pair then return False else
    case normaliseCP s pair of
      Left reason -> do
        record reason
        when (hard reason) $ forM_ (map canonicalise (orient (critical pair))) $ \(Rule _ t u0) -> do
          s <- get
          let u = result (normaliseSub s t u0)
              r = rule t u
          addExtraRule r
        traceM (Joined pair reason)
        return False
      Right pair | tooBig pair ->
        return False
      Right pair@(Critical _ eq)
        | cancelledWeight s hardJoinable eq > w -> do
          traceM (Delay pair)
          queueCP enqueueM hardJoinable l1 l2 pair
          return False
      Right pair@(Critical _ eq)
        | (_, eq') <- bestCancellation s hardJoinable eq,
          eq /= eq' -> do
            traceM (Cancel pair)
            res <- consider maxBound l1 l2 (Critical noCritInfo eq')
            queueCP enqueueM hardJoinable l1 l2 pair
            return res
      Right (Critical info eq) ->
        fmap or $ forM (map canonicalise (orient eq)) $ \r0@(Rule _ t u0) -> do
          s <- get
          let u = result (normaliseSub s t u0)
              r = rule t u
              info' = info { top = t }
          case normaliseCP s (Critical info' (t :=: u)) of
            Left reason -> do
              when (hard reason) $ record reason
              addExtraRule r
              addExtraRule r0
              return False
            Right eq ->
              case groundJoin s (branches (And [])) eq of
                Right eqs -> do
                  record GroundJoined
                  mapM_ (consider maxBound l1 l2) [ eq { critInfo = info' } | eq <- eqs ]
                  addExtraRule r
                  addExtraRule r0
                  return False
                Left model -> do
                  traceM (NewRule r)
                  l <- addRule (Modelled model (ruleOverlaps s (lhs r)) (Critical info r))
                  queueCPsSplit enqueueM noLabel l (Labelled l r)
                  interreduce r
                  return True

groundJoin :: Function f =>
  Twee f -> [Branch f] -> Critical (Equation f) -> Either (Model f) [Critical (Equation f)]
groundJoin s ctx r@(Critical info (t :=: u)) =
  stamp "ground joinability testing" $
  case partitionEithers (map (solve (usort (atoms t ++ atoms u))) ctx) of
    ([], instances) ->
      let rs = [ subst sub r | sub <- instances ] in
      Right (usort (map canonicalise rs))
    (model:_, _)
      | not (useGroundJoining s) -> Left model
      | isRight (normaliseCP s (Critical info (t' :=: u'))) -> Left model
      | otherwise ->
          let model1 = optimise model weakenModel (\m -> valid m nt && valid m nu)
              model2 = optimise model1 weakenModel (\m -> isLeft (normaliseCP s (Critical info (result (normaliseIn s m t) :=: result (normaliseIn s m u)))))

              diag [] = Or []
              diag (r:rs) = negateFormula r ||| (weaken r &&& diag rs)
              weaken (LessEq t u) = Less t u
              weaken x = x
              ctx' = formAnd (diag (modelToLiterals model2)) ctx in

          trace s (Discharge r model2) $
          groundJoin s ctx' r
      where
        nt = normaliseIn s model t
        nu = normaliseIn s model u
        t' = result nt
        u' = result nu

valid :: Function f => Model f -> Reduction f -> Bool
valid model red = all valid1 (steps red)
  where
    valid1 (rule, sub) = reducesInModel model rule sub

optimise :: a -> (a -> [a]) -> (a -> Bool) -> a
optimise x f p =
  case filter p (f x) of
    y:_ -> optimise y f p
    _   -> x

addRule :: Function f => Modelled (Critical (Rule f)) -> StateT (Twee f) IO Label
addRule rule = do
  l <- newLabelM
  modify (\s -> s { labelledRules = Indexes.insert (Labelled l rule) (labelledRules s) })
  modify (addCancellationRule l (critical (modelled rule)))
  return l

addExtraRule :: Function f => Rule f -> StateT (Twee f) IO ()
addExtraRule rule = do
  traceM (ExtraRule rule)
  modify (\s -> s { extraRules = Indexes.insert rule (extraRules s) })

deleteRule :: Function f => Label -> Modelled (Critical (Rule f)) -> StateT (Twee f) IO ()
deleteRule l rule = do
  modify $ \s ->
    s { labelledRules = Indexes.delete (Labelled l rule) (labelledRules s),
        queue = deleteLabel l (queue s) }
  modify (deleteCancellationRule l (critical (modelled rule)))

data Simplification f = Simplify (Model f) (Modelled (Critical (Rule f))) | Reorient (Modelled (Critical (Rule f))) deriving Show

instance (Numbered f, PrettyTerm f) => Pretty (Simplification f) where
  pPrint (Simplify _ rule) = text "Simplify" <+> pPrint rule
  pPrint (Reorient rule) = text "Reorient" <+> pPrint rule

interreduce :: Function f => Rule f -> StateT (Twee f) IO ()
interreduce new = do
  rules <- gets (\s -> Indexes.elems (labelledRules s))
  forM_ rules $ \(Labelled l old) -> do
    s <- get
    case reduceWith s l new old of
      Nothing -> return ()
      Just red -> do
        traceM (Reduce red new)
        case red of
          Simplify model rule -> simplifyRule l model rule
          Reorient rule@(Modelled _ _ (Critical info (Rule _ t u))) -> do
            deleteRule l rule
            queueCP enqueueM trivial noLabel noLabel (Critical info (t :=: u))
            return ()

reduceWith :: Function f => Twee f -> Label -> Rule f -> Modelled (Critical (Rule f)) -> Maybe (Simplification f)
reduceWith s lab new old0@(Modelled model _ (Critical info old@(Rule _ l r)))
  | not (isWeak new) &&
    not (lhs new `isInstanceOf` l) &&
    not (null (anywhere (tryRule reduces new) l)) =
      Just (Reorient old0)
  | not (isWeak new) &&
    not (lhs new `isInstanceOf` l) &&
    not (oriented (orientation new)) &&
    not (all isNothing [ match (lhs new) l' | l' <- subterms l ]) &&
    modelJoinable =
    tryGroundJoin
  | not (null (anywhere (tryRule reduces new) (rhs old))) =
      Just (Simplify model old0)
  | not (oriented (orientation old)) &&
    not (oriented (orientation new)) &&
    not (lhs new `isInstanceOf` r) &&
    not (all isNothing [ match (lhs new) r' | r' <- subterms r ]) &&
    modelJoinable =
    tryGroundJoin
  | otherwise = Nothing
  where
    s' = s { labelledRules = Indexes.delete (Labelled lab old0) (labelledRules s) }
    modelJoinable = isLeft (normaliseCP s' (Critical info (lm :=: rm)))
    lm = result (normaliseIn s' model l)
    rm = result (normaliseIn s' model r)
    tryGroundJoin =
      case groundJoin s' (branches (And [])) (Critical info (l :=: r)) of
        Left model' ->
          Just (Simplify model' old0)
        Right _ ->
          Just (Reorient old0)
    isWeak (Rule (WeaklyOriented _) _ _) = True
    isWeak _ = False

simplifyRule :: Function f => Label -> Model f -> Modelled (Critical (Rule f)) -> StateT (Twee f) IO ()
simplifyRule l model r@(Modelled _ positions (Critical info (Rule _ lhs rhs))) = do
  modify $ \s ->
    s {
      labelledRules =
         Indexes.insert (Labelled l (Modelled model positions (Critical info (rule lhs (result (normalise s rhs))))))
           (Indexes.delete (Labelled l r) (labelledRules s)) }
  modify (deleteCancellationRule l (critical (modelled r)))
  modify (addCancellationRule l (critical (modelled r)))

newEquation :: Function f => Equation f -> StateT (Twee f) IO ()
newEquation (t :=: u) = do
  consider maxBound noLabel noLabel (Critical noCritInfo (t :=: u))
  renormaliseGoals
  return ()

noCritInfo :: Function f => CritInfo f
noCritInfo = CritInfo minimalTerm 0

--------------------------------------------------------------------------------
-- Cancellation rules.
--------------------------------------------------------------------------------

data CancellationRule f =
  CancellationRule {
    cr_unified :: [[Term f]],
    cr_rule :: {-# UNPACK #-} !(Rule f) }
  deriving (Show, Generic)

instance (Numbered f, PrettyTerm f) => Pretty (CancellationRule f) where
  pPrint (CancellationRule tss rule) =
    pPrint rule <+> text "cancelling" <+> pPrint tss

instance Symbolic (CancellationRule f) where
  type ConstantOf (CancellationRule f) = f

instance Singular (CancellationRule f) where
  term (CancellationRule _ rule) = term rule

toCancellationRule :: Function f => Twee f -> Rule f -> Maybe (CancellationRule f)
toCancellationRule _ (Rule Permutative{} _ _) = Nothing
toCancellationRule _ (Rule WeaklyOriented{} _ _) = Nothing
toCancellationRule s (Rule or l r)
  | not (null vs) &&
    (not (atomicCancellation s) || atomic r) =
    Just (CancellationRule tss (Rule or' l' r))
  | otherwise = Nothing
  where
    consts = unifyConstantsInCancellation s
    atomic (Var _) = True
    atomic (Fun _ Empty) = True
    atomic _ = False

    -- Variables that occur on lhs more than once, but not rhs
    vs = usort (vars l \\ usort (vars l)) \\ usort (vars r)
    cs = usort [ c | consts, Fun c Empty <- subterms l ]

    V n = bound l `max` bound r

    l' = build (freshenVars (n + length cs) (singleton l))
    freshenVars !_ Empty = mempty
    freshenVars n (Cons (Var x) ts) =
      var y `mappend` freshenVars (n+1) ts
      where
        y = if x `elem` vs then V n else x
    freshenVars i (Cons (Fun f Empty) ts) | f `elem` cs =
      var (V m) `mappend` freshenVars (i+1) ts
      where
        m = n + fromMaybe __ (elemIndex f cs)
    freshenVars n (Cons (Fun f ts) us) =
      fun f (freshenVars (n+1) ts) `mappend`
      freshenVars (n+lenList ts+1) us

    tss =
      map (map (build . var . snd)) (partitionBy fst pairs) ++
      zipWith (\i c -> [build (con c), build (var (V i))]) [n..] cs
    pairs = concat (zipWith f (subterms l) (subterms l'))
      where
        f (Var x) (Var y)
          | x `elem` vs = [(x, y)]
        f _ _ = []

    or' = subst (var . f) or
      where
        f x = fromMaybe __ (lookup x pairs)

addCancellationRule :: Function f => Label -> Rule f -> Twee f -> Twee f
addCancellationRule _ (Rule _ t u) s
  | Just n <- maxCancellationSize s, size (t :=: u) > n = s
addCancellationRule l r s =
  case toCancellationRule s r of
    Nothing -> s
    Just c
      | moreTracing s &&
        Debug.Trace.traceShow (sep [text "Adding cancellation rule", nest 2 (pPrint c)]) False -> __
    Just c -> s {
      cancellationRules =
          Index.insert (Labelled l c) (cancellationRules s) }

deleteCancellationRule :: Function f => Label -> Rule f -> Twee f -> Twee f
deleteCancellationRule l r s =
  case toCancellationRule s r of
    Nothing -> s
    Just c -> s {
      cancellationRules =
          Index.delete (Labelled l c) (cancellationRules s) }

--------------------------------------------------------------------------------
-- Critical pairs.
--------------------------------------------------------------------------------

data Critical a =
  Critical {
    critInfo :: CritInfo (ConstantOf a),
    critical :: a }
  deriving Generic

data CritInfo f =
  CritInfo {
    top      :: Term f,
    overlap  :: Int }

instance Eq a => Eq (Critical a) where x == y = critical x == critical y
instance Ord a => Ord (Critical a) where compare = comparing critical

instance (PrettyTerm (ConstantOf a), Pretty a) => Pretty (Critical a) where
  pPrint Critical{..} = pPrint critical

deriving instance (Show a, Show (ConstantOf a)) => Show (Critical a)
deriving instance Show f => Show (CritInfo f)

instance Symbolic a => Symbolic (Critical a) where
  type ConstantOf (Critical a) = ConstantOf a

instance Singular a => Singular (Critical a) where
  term = term . critical

instance Symbolic (CritInfo f) where
  type ConstantOf (CritInfo f) = f

  termsDL = termsDL . top
  replace f CritInfo{..} = CritInfo (replace f top) overlap

data CPInfo =
  CPInfo {
    cpWeight  :: {-# UNPACK #-} !Int,
    cpWeight2 :: {-# UNPACK #-} !Int,
    cpAge1    :: {-# UNPACK #-} !Label,
    cpAge2    :: {-# UNPACK #-} !Label }
    deriving (Eq, Ord, Show)

data CP f =
  CP {
    info :: {-# UNPACK #-} !CPInfo,
    cp   :: {-# UNPACK #-} !(Critical (Equation f)),
    l1   :: {-# UNPACK #-} !Label,
    l2   :: {-# UNPACK #-} !Label }
  deriving Show

instance Eq (CP f) where x == y = info x == info y
instance Ord (CP f) where compare = comparing info
instance Labels (CP f) where labels x = [l1 x, l2 x]
instance (Numbered f, PrettyTerm f) => Pretty (CP f) where
  pPrint = pPrint . cp

data CPs f =
  CPs {
    best  :: {-# UNPACK #-} !CPInfo,
    -- The label of the rule having the best critical pair.
    -- This is l2 in the single critical pair.
    label :: {-# UNPACK #-} !Label,
    -- The range of rules that the CP set represents.
    lower :: {-# UNPACK #-} !Label,
    upper :: {-# UNPACK #-} !Label,
    count :: {-# UNPACK #-} !Int,
    from  :: {-# UNPACK #-} !(Labelled (Rule f)) }
  deriving Show

instance Eq (CPs f) where x == y = best x == best y
instance Ord (CPs f) where compare = comparing best
instance Labels (CPs f) where labels (CPs _ _ _ _ _ (Labelled l _)) = [l]
instance (Numbered f, PrettyTerm f) => Pretty (CPs f) where
  pPrint CPs{..} = text "Family of size" <+> pPrint count <+> text "from" <+> pPrint from

data Passive f =
    SingleCP {-# UNPACK #-} !(CP f)
  | ManyCPs  {-# UNPACK #-} !(CPs f)
  deriving (Eq, Show)

instance Ord (Passive f) where
  compare = comparing f
    where
      f (SingleCP x) = info x
      f (ManyCPs  x) = best x
instance Labels (Passive f) where
  labels (SingleCP x) = labels x
  labels (ManyCPs x) = labels x
instance (Numbered f, PrettyTerm f) => Pretty (Passive f) where
  pPrint (SingleCP cp) = pPrint cp
  pPrint (ManyCPs cps) = pPrint cps

passiveCount :: Passive f -> Int
passiveCount SingleCP{} = 1
passiveCount (ManyCPs x) = count x

criticalPairs :: Function f => Twee f -> Label -> Label -> Rule f -> [Labelled (Critical (Equation f))]
criticalPairs s lower upper rule =
  stamp "finding critical pairs" (length res `seq` res)
  where
    rules = filter (p . labelOf) (Indexes.elems (labelledRules s))
    p l = lower <= l && l <= upper
    res =
      criticalPairs1 s (ruleOverlaps s (lhs rule)) rule (map (fmap (critical . modelled)) rules) ++
      [ cp
      | Labelled l' (Modelled _ ns (Critical _ old)) <- rules,
        cp <- criticalPairs1 s ns old [Labelled l' rule] ]

ruleOverlaps :: Twee f -> Term f -> [Int]
ruleOverlaps s t = aux 0 Set.empty (singleton t)
  where
    aux !_ !_ Empty = []
    aux n m (Cons (Var _) t) = aux (n+1) m t
    aux n m (ConsSym t@Fun{} u)
      | useGeneralSuperpositions s && t `Set.member` m = aux (n+1) m u
      | otherwise = n:aux (n+1) (Set.insert t m) u

overlaps :: [Int] -> Term f -> Term f -> [(Subst f, Int)]
overlaps ns t1 t2@(Fun g _) = go 0 ns (singleton t1) []
  where
    go !_ _ !_ _ | False = __
    go _ [] _ rest = rest
    go _ _ Empty rest = rest
    go n (m:ms) (ConsSym ~t@(Fun f _) u) rest
      | m == n && f == g = here ++ go (n+1) ms u rest
      | m == n = go (n+1) ms u rest
      | otherwise = go (n+1) (m:ms) u rest
      where
        here =
          case unify t t2 of
            Nothing -> []
            Just sub -> [(sub, n)]
overlaps _ _ _ = []

emitReplacement :: Int -> Term f -> TermList f -> Builder f
emitReplacement n t = aux n
  where
    aux !_ !_ | False = __
    aux _ Empty = mempty
    aux 0 (Cons _ u) = builder t `mappend` builder u
    aux n (Cons (Var x) u) = var x `mappend` aux (n-1) u
    aux n (Cons t@(Fun f ts) u)
      | n < len t =
        fun f (aux (n-1) ts) `mappend` builder u
      | otherwise =
        builder t `mappend` aux (n-len t) u

criticalPairs1 :: Function f => Twee f -> [Int] -> Rule f -> [Labelled (Rule f)] -> [Labelled (Critical (Equation f))]
criticalPairs1 s ns r rs = do
  let V b = maximum (V 0:[ bound t | Labelled _ (Rule _ t _) <- rs ])
      Rule or t u = subst (\(V x) -> var (V (x+b))) r
  Labelled l (Rule or' t' u') <- rs
  (sub, pos) <- overlaps ns t t'
  let left = subst sub u
      right = subst sub (build (emitReplacement pos u' (singleton t)))
      top = subst sub t
      overlap = at pos (singleton t)

      inner = subst sub overlap
      osz = size overlap + (size u - size t) + (size u' - size t')

  guard (left /= top && right /= top && left /= right)
  when (or  /= Oriented) $ guard (not (lessEq top right))
  when (or' /= Oriented) $ guard (not (lessEq top left))
  when (skipCompositeSuperpositions s) $
    guard (null (nested (anywhere (rewrite "prime" simplifies (easyRules s))) inner))
  return (Labelled l (Critical (CritInfo top osz) (left :=: right)))

queueCP ::
  Function f =>
  (Passive f -> StateT (Twee f) IO ()) ->
  (Equation f -> Bool) -> Label -> Label -> Critical (Equation f) -> StateT (Twee f) IO ()
queueCP enq joinable l1 l2 eq = do
  s <- get
  case toCP s l1 l2 joinable eq of
    Nothing -> return ()
    Just cp -> enq (SingleCP cp)

queueCPs ::
  Function f =>
  (Passive f -> StateT (Twee f) IO ()) ->
  Label -> Label -> ([Label] -> [Label]) -> Labelled (Rule f) -> StateT (Twee f) IO ()
queueCPs enq lower upper f rule = stampM "adding critical pairs" $ do
  s <- get
  let cps = sortBy (comparing l2) (toCPs s lower upper rule)
      cpss = slurp (f (map l2 cps)) cps
  forM_ cpss $ \xs -> do
    if length xs <= minimumCPSetSize s then
      mapM_ (enq . SingleCP) xs
    else
      let best = minimum xs
          l1' = minimum (map l2 xs)
          l2' = maximum (map l2 xs) in
      enq (ManyCPs (CPs (info best) (l2 best) l1' l2' (length xs) rule))
  where
    slurp [] cps = [cps]
    slurp (l:ls) cps =
      cps1:slurp ls cps2
      where
        (cps1, cps2) = span ((< l) . l2) cps

queueCPsSplit ::
  Function f =>
  (Passive f -> StateT (Twee f) IO ()) ->
  Label -> Label -> Labelled (Rule f) -> StateT (Twee f) IO ()
queueCPsSplit enq l u rule = do
  s <- get
  let f xs = drop 1 (map head (chunksOf (1 `max` (length xs `div` cpSplits s)) xs))
  queueCPs enq l u f rule

toCPs ::
  Function f =>
  Twee f -> Label -> Label -> Labelled (Rule f) -> [CP f]
toCPs s lower upper (Labelled l rule) =
  catMaybes [toCP s l l' trivial eqn | Labelled l' eqn <- criticalPairs s lower upper rule]

toCP ::
  Function f =>
  Twee f -> Label -> Label -> (Equation f -> Bool) -> Critical (Equation f) -> Maybe (CP f)
toCP s l1 l2 joinable cp = fmap toCP' (norm cp)
  where
    norm (Critical info (t :=: u)) = do
      guard (t /= u)
      let t' = result (normaliseQuickly s t)
          u' = result (normaliseQuickly s u)
          eq' = Critical info (t' :=: u')
      guard (t' /= u')
      return eq'

    toCP' eq@(Critical info (t :=: u)) =
      CP (CPInfo w (-(overlap info)) l2 l1) eq l1 l2
      where
        w = cancelledWeight s joinable (t :=: u)

cancelledWeight :: Function f => Twee f -> (Equation f -> Bool) -> Equation f -> Int
cancelledWeight s joinable eq = fst (bestCancellation s joinable eq)

bestCancellation :: Function f => Twee f -> (Equation f -> Bool) -> Equation f -> (Int, Equation f)
bestCancellation s _ eq | not (useCancellation s) = (weight s eq, eq)
bestCancellation s joinable (t :=: u)
  | moreTracing s && length cs > 1 && w /= weight s (t :=: u) && Debug.Trace.trace ("Cancelled " ++ prettyShow (t :=: u) ++ " into " ++ prettyShow (tail cs)) False = __
  | otherwise = (w, best)
  where
    cs   = cancellations s joinable (t :=: u)
    ws   = zipWith (+) [0..] (map (weight s) cs)
    w    = minimum ws
    best = snd (minimumBy (comparing fst) (zip ws cs))

weight, weight' :: Function f => Twee f -> Equation f -> Int
weight s eq = weight' s (order eq)

weight' s (t :=: u) =
  lhsWeight s*size' t + rhsWeight s*size' u
  where
    size' t = 4*(size t + len t) - length (vars t) - length (nub (vars t))

cancellations :: Function f => Twee f -> (Equation f -> Bool) -> Equation f -> [Equation f]
cancellations s joinable (t :=: u) =
  t :=: u:
  case cands of
    [] -> []
    _  -> cancellations s joinable (minimumBy (comparing size) cands)
  where
    cands =
      filter (\eq -> size eq < size (t :=: u)) $
      [ t' :=: u' | (sub, t') <- cancel t, let u' = result (normaliseQuickly s (subst sub u)), not (joinable (t' :=: u')) ] ++
      [ t' :=: u' | (sub, u') <- cancel u, let t' = result (normaliseQuickly s (subst sub t)), not (joinable (t' :=: u')) ]
    cancel t = do
      (i, u) <- zip [0..] (subterms t)
      Labelled _ (CancellationRule tss (Rule _ _ u')) <-
        Index.lookup u (Index.freeze (cancellationRules s))
      sub <- maybeToList (unifyMany [(t, u) | t:ts <- tss, u <- ts])
      let t' = result (normaliseQuickly s (subst sub (build (emitReplacement i u' (singleton t)))))
      return (sub, t')

    unifyMany ps =
      unifyList (buildList (map fst ps)) (buildList (map snd ps))

--------------------------------------------------------------------------------
-- Tracing.
--------------------------------------------------------------------------------

data Event f =
    NewRule (Rule f)
  | ExtraRule (Rule f)
  | NewCP (Passive f)
  | Reduce (Simplification f) (Rule f)
  | Consider (Critical (Equation f))
  | Joined (Critical (Equation f)) JoinReason
  | Delay (Critical (Equation f))
  | Cancel (Critical (Equation f))
  | Discharge (Critical (Equation f)) (Model f)
  | NormaliseCPs (Twee f)

trace :: Function f => Twee f -> Event f -> a -> a
trace Twee{..} (NewRule rule) = traceIf tracing (hang (text "New rule") 2 (pPrint rule))
trace Twee{..} (ExtraRule rule) = traceIf tracing (hang (text "Extra rule") 2 (pPrint rule))
trace Twee{..} (NewCP cp) = traceIf moreTracing (hang (text "Critical pair") 2 (pPrint cp))
trace Twee{..} (Reduce red rule) = traceIf tracing (sep [pPrint red, nest 2 (text "using"), nest 2 (pPrint rule)])
trace Twee{..} (Consider eq) = traceIf moreTracing (sep [text "Considering", nest 2 (pPrint eq), text "under", nest 2 (pPrint (top (critInfo eq)))])
trace Twee{..} (Joined eq reason) = traceIf moreTracing (sep [text "Joined", nest 2 (pPrint eq), text "under", nest 2 (pPrint (top (critInfo eq))), text "by", nest 2 (pPrint reason)])
trace Twee{..} (Delay eq) = traceIf moreTracing (sep [text "Delaying", nest 2 (pPrint eq)])
trace Twee{..} (Cancel eq) = traceIf tracing (sep [text "Cancelled", nest 2 (pPrint eq)])
trace Twee{..} (Discharge eq fs) = traceIf tracing (sep [text "Discharge", nest 2 (pPrint eq), text "under", nest 2 (pPrint fs)])
trace Twee{..} (NormaliseCPs s) = traceIf tracing (text "" $$ text "Normalising unprocessed critical pairs." $$ text (report s) $$ text "")

traceM :: Function f => Event f -> StateT (Twee f) IO ()
traceM x = do
  s <- get
  trace s x (return ())

traceIf :: Bool -> Doc -> a -> a
traceIf True x = Debug.Trace.trace (show x)
traceIf False _ = id
