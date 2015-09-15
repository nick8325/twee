-- Knuth-Bendix completion, with lots of exciting tricks for
-- unorientable equations.

{-# LANGUAGE CPP, TypeFamilies, FlexibleContexts, RecordWildCards, ScopedTypeVariables, UndecidableInstances, StandaloneDeriving, PatternGuards, BangPatterns #-}
module KBC where

#include "errors.h"
import KBC.Base hiding (empty)
import KBC.Constraints hiding (funs)
import KBC.Rule
import qualified KBC.Indexes as Indexes
import KBC.Indexes(Indexes, Rated(..))
import qualified KBC.Index as Index
import KBC.Index(Index, Frozen)
import KBC.Queue hiding (queue)
import KBC.Utils
import Control.Monad
import Data.Maybe
import Data.Ord
import qualified Debug.Trace
import Control.Monad.Trans.State.Strict
import Data.List
import Data.Function
import Text.Printf
import qualified Data.Set as Set
import Data.Set(Set)
import Data.Either
import qualified Data.Map.Strict as Map
import Data.Map.Strict(Map)
import qualified Data.DList as DList

--------------------------------------------------------------------------------
-- Completion engine state.
--------------------------------------------------------------------------------

data KBC f =
  KBC {
    maxSize           :: Maybe Int,
    labelledRules     :: {-# UNPACK #-} !(Indexes (Labelled (Modelled (Critical (Rule f))))),
    extraRules        :: {-# UNPACK #-} !(Indexes (Rule f)),
    subRules          :: Index (Term f, Rule f),
    goals             :: [Set (Term f)],
    totalCPs          :: Int,
    processedCPs      :: Int,
    renormaliseAt     :: Int,
    queue             :: !(Queue (Passive f)),
    useInversionRules :: Bool,
    useSkolemPenalty  :: Bool,
    useGroundPenalty  :: Bool,
    useGeneralSuperpositions :: Bool,
    useOvergeneralSuperpositions :: Bool,
    joinStatistics    :: Map JoinReason Int }
  deriving Show

initialState :: KBC f
initialState =
  KBC {
    maxSize           = Nothing,
    labelledRules     = Indexes.empty,
    extraRules        = Indexes.empty,
    subRules          = Index.Nil,
    goals             = [],
    totalCPs          = 0,
    processedCPs      = 0,
    renormaliseAt     = 50,
    queue             = empty,
    useInversionRules = False,
    useSkolemPenalty  = False,
    useGroundPenalty  = False,
    useGeneralSuperpositions = True,
    useOvergeneralSuperpositions = False,
    joinStatistics    = Map.empty }

addGoals :: [Set (Term f)] -> KBC f -> KBC f
addGoals gs s = s { goals = gs ++ goals s }

report :: Function f => KBC f -> String
report KBC{..} =
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

enqueueM :: Function f => Passive f -> State (KBC f) ()
enqueueM cps = do
  traceM (NewCP cps)
  modify' $ \s -> s {
    queue    = enqueue cps (queue s),
    totalCPs = totalCPs s + passiveCount cps }

dequeueM :: Function f => State (KBC f) (Maybe (Passive f))
dequeueM =
  state $ \s ->
    case dequeue (queue s) of
      Nothing -> (Nothing, s)
      Just (x, q) -> (Just x, s { queue = q })

newLabelM :: State (KBC f) Label
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

  term = term . modelled
  symbols fun var = symbols fun var . modelled
  subst sub Modelled{..} = Modelled model positions (subst sub modelled)

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
rulesFor :: Function f => Int -> KBC f -> Frozen (Rule f)
rulesFor n k =
  {-# SCC rules #-}
  Index.map (critical . modelled . peel) (Indexes.freeze n (labelledRules k)) `Index.union`
  Indexes.freeze n (extraRules k)

easyRules, rules :: Function f => KBC f -> Frozen (Rule f)
easyRules k = rulesFor 0 k
rules k = rulesFor 1 k

normaliseQuickly :: Function f => KBC f -> Term f -> Reduction f
normaliseQuickly s = normaliseWith (rewrite "simplify" simplifies (easyRules s))

normalise :: Function f => KBC f -> Term f -> Reduction f
normalise s = normaliseWith (rewrite "reduce" reduces (rules s))

normaliseIn :: Function f => KBC f -> Model f -> Term f -> Reduction f
normaliseIn s model =
  normaliseWith (rewrite "model" (reducesInModel model) (rules s))

normaliseSub :: Function f => KBC f -> Term f -> Term f -> Reduction f
normaliseSub s top t
  | lessEq t top && isNothing (unify t top) =
    normaliseWith (rewrite "sub" (reducesSub top) (rules s)) t
  | otherwise = Parallel [] t

normaliseSkolem :: Function f => KBC f -> Term f -> Reduction f
normaliseSkolem s = normaliseWith (rewrite "skolem" reducesSkolem (rules s))

reduceCP ::
  Function f =>
  KBC f -> JoinStage -> (Term f -> Term f) ->
  Critical (Equation f) -> Either JoinReason (Critical (Equation f))
reduceCP s stage f (Critical top (t :=: u))
  | t' == u' = Left (Trivial stage)
  | subsumed s True t' u' = Left (Subsumed stage)
  | otherwise = Right (Critical top (t' :=: u'))
  where
    t' = f t
    u' = f u

    subsumed s root t u = here || there t u
      where
        here =
          or [ rhs x == u | x <- Index.lookup t rs ] ||
          or [ subst sub (rhs x) == t | Index.Match xs sub <- Index.matches u rs, x <- xs, not root || not (isVariantOf (lhs x) u) ]
        there (Var x) (Var y) | x == y = True
        there (Fun f ts) (Fun g us) | f == g = and (zipWith (subsumed s False) (fromTermList ts) (fromTermList us))
        there _ _ = False
        rs = rules s

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

normaliseCPQuickly, normaliseCP ::
  Function f =>
  KBC f -> Critical (Equation f) -> Either JoinReason (Critical (Equation f))
normaliseCPQuickly s cp =
  reduceCP s Initial id cp >>=
  reduceCP s Simplification (result . normaliseQuickly s)

normaliseCP s cp@(Critical info _) =
  case (cp1, cp2, cp3, cp4) of
    (Right cp, Right _, Right _, Right _) -> Right cp
    (Right _, Right _, Right _, Left x) -> Left x
    (Right _, Right _, Left x, _) -> Left x
    (Right _, Left x, _, _) -> Left x
    (Left x, _, _, _) -> Left x
  where
    cp1 =
      normaliseCPQuickly s cp >>=
      reduceCP s Reducing (result . normalise s) >>=
      reduceCP s Subjoining (result . normaliseSub s (top info))

    cp2 =
      reduceCP s Subjoining (result . normaliseSub s (flipCP (top info))) (flipCP cp)

    cp3 = setJoin cp
    cp4 = setJoin (flipCP cp)

    flipCP :: Symbolic a => a -> a
    flipCP t = subst sub t
      where
        n = maximum (0:map fromEnum (vars t))
        sub = flattenSubst [(MkVar x, var (MkVar (n - x))) | MkVar x <- vars t]

    -- XXX shouldn't this also check subsumption?
    setJoin (Critical info (t :=: u))
      | Set.null (norm t `Set.intersection` norm u) =
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

complete :: Function f => State (KBC f) ()
complete = do
  res <- complete1
  when res complete

complete1 :: Function f => State (KBC f) Bool
complete1 = {-# SCC complete1 #-} do
  KBC{..} <- get
  let Label n = nextLabel queue
  when (n >= renormaliseAt) $ do
    normaliseCPs
    modify (\s -> s { renormaliseAt = renormaliseAt * 3 `div` 2 })

  res <- dequeueM
  case res of
    Just (SingleCP (CP _ cp _ _)) -> do
      consider cp
      modify $ \s -> s { goals = map (normalForms (rewrite "goal" reduces (rules s)) . Set.toList) goals }
      return True
    Just (ManyCPs (CPs _ l lower upper size rule)) -> do
      s <- get
      modify (\s@KBC{..} -> s { totalCPs = totalCPs - size })

      queueCPsSplit lower (l-1) rule
      mapM_ (enqueueM . SingleCP) (toCPs s l l rule)
      queueCPsSplit (l+1) upper rule
      complete1
    Nothing ->
      return False

normaliseCPs :: forall f v. Function f => State (KBC f) ()
normaliseCPs = {-# SCC normaliseCPs #-} do
  s@KBC{..} <- get
  traceM (NormaliseCPs s)
  put s { queue = emptyFrom queue }
  forM_ (toList queue) $ \cp ->
    case cp of
      SingleCP (CP _ cp l1 l2) -> queueCP l1 l2 cp
      ManyCPs (CPs _ _ lower upper _ rule) -> queueCPs lower upper (const ()) rule
  modify (\s -> s { totalCPs = totalCPs })

consider ::
  Function f =>
  Critical (Equation f) -> State (KBC f) ()
consider pair = {-# SCC consider #-} do
  traceM (Consider pair)
  modify' (\s -> s { processedCPs = processedCPs s + 1 })
  s <- get
  let record reason = modify' (\s -> s { joinStatistics = Map.insertWith (+) reason 1 (joinStatistics s) })
  case {-# SCC normalise1 #-} normaliseCP s pair of
    Left reason -> record reason
    Right (Critical info eq) ->
      forM_ (map canonicalise (orient eq)) $ \(Rule orientation t u0) -> do
        s <- get
        let u = result (normaliseSub s t u0)
            r = rule t u
        case {-# SCC normalise2 #-} normaliseCP s (Critical info (t :=: u)) of
          Left reason -> do
            let hard (Trivial Subjoining) = True
                hard (Subsumed Subjoining) = True
                hard (Trivial Reducing) | lessEq u t = True
                hard (Subsumed Reducing) | lessEq u t = True
                hard SetJoining = True
                hard _ = False
            when (hard reason) $ do
              traceM (ExtraRule r)
              addExtraRule r
          Right eq ->
            case groundJoin s (branches (And [])) eq of
              Right eqs -> {-# SCC "GroundJoined" #-} do
                record GroundJoined
                mapM_ consider eqs
                traceM (ExtraRule r)
                addExtraRule r
                newSubRule r
              Left model -> {-# SCC "NewRule" #-} do
                traceM (NewRule r)
                l <- addRule (Modelled model (ruleOverlaps s (lhs r)) (Critical info r))
                queueCPsSplit noLabel l (Labelled l r)
                interreduce r

groundJoin :: Function f =>
  KBC f -> [Branch f] -> Critical (Equation f) -> Either (Model f) [Critical (Equation f)]
groundJoin s ctx r@(Critical info (t :=: u)) = {-# SCC groundJoin #-}
  case partitionEithers (map (solve (usort (vars t ++ vars u))) ctx) of
    ([], instances) ->
      let rs = [ subst sub r | sub <- instances ] in
      Right (usort (map canonicalise rs))
    (model:_, _)
      | isRight (normaliseCP s (Critical info (t' :=: u'))) -> Left model
      | otherwise ->
          let model1 = optimise model weakenModel (\m -> valid m nt && valid m nu)
              model2 = optimise model1 weakenModel (\m -> isLeft (normaliseCP s (Critical info (result (normaliseIn s m t) :=: result (normaliseIn s m u)))))

              diag [] = Or []
              diag (r:rs) = negateFormula r ||| (weaken r &&& diag rs)
              weaken (LessEq t u) = Less t u
              weaken x = x
              ctx' = formAnd (diag (modelToLiterals model2)) ctx in

          trace (Discharge r model2) $
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

newSubRule :: Function f => Rule f -> State (KBC f) ()
newSubRule r@(Rule _ t u) = do
  s <- get
  when (useInversionRules s) $
    put s { subRules = foldr ins (subRules s) (properSubterms t) }
  where
    ins v idx
      | isFun v && not (lessEq v u) && usort (vars u) `isSubsequenceOf` usort (vars v) = Index.insert (v, r) idx
      | otherwise = idx

addRule :: Function f => Modelled (Critical (Rule f)) -> State (KBC f) Label
addRule rule = do
  l <- newLabelM
  modify (\s -> s { labelledRules = Indexes.insert (Labelled l rule) (labelledRules s) })
  newSubRule (critical (modelled rule))
  return l

addExtraRule :: Function f => Rule f -> State (KBC f) ()
addExtraRule rule =
  modify (\s -> s { extraRules = Indexes.insert rule (extraRules s) })

deleteRule :: Function f => Label -> Modelled (Critical (Rule f)) -> State (KBC f) ()
deleteRule l rule =
  modify $ \s ->
    s { labelledRules = Indexes.delete (Labelled l rule) (labelledRules s),
        queue = deleteLabel l (queue s) }

data Simplification f = Simplify (Model f) (Modelled (Critical (Rule f))) | Reorient (Modelled (Critical (Rule f))) deriving Show

instance PrettyTerm f => Pretty (Simplification f) where
  pPrint (Simplify _ rule) = text "Simplify" <+> pPrint rule
  pPrint (Reorient rule) = text "Reorient" <+> pPrint rule

interreduce :: Function f => Rule f -> State (KBC f) ()
interreduce new = {-# SCC interreduce #-} do
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
            queueCP noLabel noLabel (Critical info (t :=: u))

reduceWith :: Function f => KBC f -> Label -> Rule f -> Modelled (Critical (Rule f)) -> Maybe (Simplification f)
reduceWith s lab new old0@(Modelled model _ (Critical info old@(Rule _ l r)))
  | {-# SCC "reorient-normal" #-}
    not (lhs new `isInstanceOf` l) &&
    not (null (anywhere (tryRule reduces new) l)) =
      Just (Reorient old0)
  | {-# SCC "reorient-ground" #-}
    not (lhs new `isInstanceOf` l) &&
    orientation new == Unoriented &&
    not (all isNothing [ match (lhs new) l' | l' <- subterms l ]) &&
    modelJoinable =
    tryGroundJoin
  | {-# SCC "simplify" #-}
    not (null (anywhere (tryRule reduces new) (rhs old))) =
      Just (Simplify model old0)
  | {-# SCC "reorient-ground/ground" #-}
    orientation old == Unoriented &&
    orientation new == Unoriented &&
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

simplifyRule :: Function f => Label -> Model f -> Modelled (Critical (Rule f)) -> State (KBC f) ()
simplifyRule l model r@(Modelled _ positions (Critical info (Rule ctx lhs rhs))) = do
  s <- get
  modify $ \s ->
    s {
      labelledRules =
         Indexes.insert (Labelled l (Modelled model positions (Critical info (rule lhs (result (normalise s rhs))))))
           (Indexes.delete (Labelled l r) (labelledRules s)) }
  newSubRule (rule lhs rhs)

newEquation :: Function f => Equation f -> State (KBC f) ()
newEquation (t :=: u) = do
  consider (Critical (CritInfo minimalTerm 0) (t :=: u))
  return ()

--------------------------------------------------------------------------------
-- Critical pairs.
--------------------------------------------------------------------------------

data Critical a =
  Critical {
    critInfo :: CritInfo (ConstantOf a),
    critical :: a }

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

  term = term . critical
  symbols fun var Critical{..} = symbols fun var (critical, critInfo)
  subst sub Critical{..} = Critical (subst sub critInfo) (subst sub critical)

instance Symbolic (CritInfo f) where
  type ConstantOf (CritInfo f) = f

  term = __
  symbols fun var = symbols fun var . top
  subst sub CritInfo{..} = CritInfo (subst sub top) overlap

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
instance PrettyTerm f => Pretty (CP f) where
  pPrint = pPrint . cp

data CPs f =
  CPs {
    best  :: {-# UNPACK #-} !CPInfo,
    label :: {-# UNPACK #-} !Label,
    lower :: {-# UNPACK #-} !Label,
    upper :: {-# UNPACK #-} !Label,
    count :: {-# UNPACK #-} !Int,
    from  :: {-# UNPACK #-} !(Labelled (Rule f)) }
  deriving Show

instance Eq (CPs f) where x == y = best x == best y
instance Ord (CPs f) where compare = comparing best
instance Labels (CPs f) where labels (CPs _ _ _ _ _ (Labelled l _)) = [l]
instance PrettyTerm f => Pretty (CPs f) where
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
instance PrettyTerm f => Pretty (Passive f) where
  pPrint (SingleCP cp) = pPrint cp
  pPrint (ManyCPs cps) = pPrint cps

passiveCount :: Passive f -> Int
passiveCount SingleCP{} = 1
passiveCount (ManyCPs x) = count x

data InitialCP f =
  InitialCP {
    cpId :: (Term f, Label),
    cpOK :: Bool,
    cpCP :: Labelled (Critical (Equation f)) }

criticalPairs :: Function f => KBC f -> Label -> Label -> Rule f -> [Labelled (Critical (Equation f))]
criticalPairs s lower upper rule = {-# SCC criticalPairs #-}
  criticalPairs1 s (ruleOverlaps s (lhs rule)) rule (map (fmap (critical . modelled)) rules) ++
  [ cp
  | Labelled l' (Modelled _ ns (Critical _ old)) <- rules,
    cp <- criticalPairs1 s ns old [Labelled l' rule] ]
  where
    rules = filter (p . labelOf) (Indexes.elems (labelledRules s))
    p l = lower <= l && l <= upper

ruleOverlaps :: KBC f -> Term f -> [Int]
ruleOverlaps s t = aux 0 Set.empty (singleton t)
  where
    aux !_ !_ Empty = []
    aux n m (Cons (Var _) t) = aux (n+1) m t
    aux n m (ConsSym t@Fun{} u)
      | (useGeneralSuperpositions s || useOvergeneralSuperpositions s) &&
        canon t `Set.member` m = aux (n+1) m u
      | otherwise = n:aux (n+1) (Set.insert (canon t) m) u

    canon = if useOvergeneralSuperpositions s then canonicalise else id

overlaps :: [Int] -> Term f -> Term f -> [(Subst f, Int)]
overlaps ns t1 t2 = {-# SCC overlaps #-} go 0 ns (singleton t1) []
  where
    go !_ _ !_ _ | False = __
    go _ [] _ rest = rest
    go _ _ Empty rest = rest
    go n (m:ms) (ConsSym t u) rest
      | m == n = here ++ go (n+1) ms u rest
      | otherwise = go (n+1) (m:ms) u rest
      where
        here =
          case unify t t2 of
            Nothing -> []
            Just sub -> [(sub, n)]

emitReplacement :: Int -> Term f -> TermList f -> BuildM s f ()
emitReplacement n t = aux n
  where
    aux !_ !_ | False = __
    aux _ Empty = return ()
    aux 0 (Cons _ u) = do
      emitTerm t
      emitTermList u
    aux n (Cons (Var x) u) = do
      emitVar x
      aux (n-1) u
    aux n (Cons t@(Fun f ts) u)
      | n < len t = do
          emitFun f (aux (n-1) ts)
          emitTermList u
      | otherwise = do
          emitTerm t
          aux (n-len t) u

criticalPairs1 :: Function f => KBC f -> [Int] -> Rule f -> [Labelled (Rule f)] -> [Labelled (Critical (Equation f))]
criticalPairs1 s ns (Rule or t u) rs = {-# SCC criticalPairs1 #-} do
  let b = {-# SCC bound #-} bound t
  Labelled l r <- rs
  let sub = flattenSubst [(x, var (toEnum (fromEnum x+b))) | x <- vars r]
      Rule or' t' u' = subst sub r
  (sub, pos) <- overlaps ns t t'
  let left = subst sub u
      right = subst sub (buildTerm 32 (emitReplacement pos u' (singleton t)))
      top = subst sub t
      overlap = at pos (singleton t)

      inner = subst sub overlap
      osz = size overlap + (size u - size t) + (size u' - size t')
      sz = size top

  guard (left /= top && right /= top && left /= right)
  when (or  /= Oriented) $ guard (not (lessEq top right))
  when (or' /= Oriented) $ guard (not (lessEq top left))
  case maxSize s of
    Nothing -> return ()
    Just n -> guard (size top <= n)
  guard (null (nested (anywhere (rewrite "prime" simplifies (easyRules s))) inner))
  return (Labelled l (Critical (CritInfo top osz) (left :=: right)))

queueCP ::
  Function f =>
  Label -> Label -> Critical (Equation f) -> State (KBC f) ()
queueCP l1 l2 eq = do
  s <- get
  case toCP s l1 l2 eq of
    Nothing -> return ()
    Just cp -> enqueueM (SingleCP cp)

queueCPs ::
  (Function f, Ord a) =>
  Label -> Label -> (Label -> a) -> Labelled (Rule f) -> State (KBC f) ()
queueCPs lower upper f rule = {-# SCC queueCPs #-} do
  s <- get
  let cps = toCPs s lower upper rule
      cpss = partitionBy (f . l2) cps
  forM_ cpss $ \xs -> do
    if length xs <= 20 then
      mapM_ (enqueueM . SingleCP) xs
    else
      let best = minimum xs
          l1' = minimum (map l1 xs)
          l2' = minimum (map l2 xs) in
      enqueueM (ManyCPs (CPs (info best) (l2 best) l1' l2' (length xs) rule))

queueCPsSplit ::
  Function f =>
  Label -> Label -> Labelled (Rule f) -> State (KBC f) ()
queueCPsSplit l u rule = queueCPs l u f rule
  where
    f x = 5*(x-l) `div` (u-l+1)

toCPs ::
  Function f =>
  KBC f -> Label -> Label -> Labelled (Rule f) -> [CP f]
toCPs s lower upper (Labelled l rule) = {-# SCC toCPs #-}
  catMaybes [toCP s l l' eqn | Labelled l' eqn <- criticalPairs s lower upper rule]

toCP ::
  Function f =>
  KBC f -> Label -> Label -> Critical (Equation f) -> Maybe (CP f)
toCP s l1 l2 cp = {-# SCC toCP #-} fmap toCP' (norm cp)
  where
    norm (Critical info (t :=: u)) = {-# SCC norm #-} do
      guard (t /= u)
      let t' = result (normaliseQuickly s t)
          u' = result (normaliseQuickly s u)
      guard (t' /= u')
      invert (Critical info (t' :=: u'))

    invert (Critical info (t :=: u))
      | useInversionRules s,
        Just (t', u') <- focus (top info) t u `mplus` focus (top info) u t =
          Debug.Trace.traceShow (sep [text "Reducing", nest 2 (pPrint (t :=: u)), text "to", nest 2 (pPrint (t' :=: u'))]) $
          norm (Critical info (t' :=: u'))
      | otherwise = Just (Critical info (t :=: u))

    focus top t u =
      listToMaybe $ do
        (_, r1) <- Index.lookup t (Index.freeze (subRules s))
        r2 <- Index.lookup (replace t u (rhs r1)) (rules s)

        guard (reducesSub top r1 emptySubst && reducesSub top r2 emptySubst)
        let t' = rhs r1
            u' = rhs r2
        guard (subsumes True (t', u') (t, u))
        return (t', u')

    replace t u v | v == t = u
    replace t u (Fun f ts) = fun f (map (replace t u) (fromTermList ts))
    replace _ _ t = t

    subsumes strict (t', u') (t, u) =
      (isJust (matchList (concatTerms [singleton t', singleton t]) (concatTerms [singleton u', singleton u]))) &&
       (not strict || isNothing (matchList (concatTerms [singleton t, singleton t']) (concatTerms [singleton u, singleton u']))) ||
      case focus t u of
        Just (t'', u'') -> subsumes False (t', u') (t'', u'')
        _ -> False
      where
        focus (Fun f ts) (Fun g us) | f == g = aux ts us
          where
            aux Empty Empty = Nothing
            aux (Cons t ts) (Cons u us)
              | t == u = aux ts us
              | ts == us = Just (t, u)
              | otherwise = Nothing
        focus _ _ = Nothing

    toCP' (Critical info (t :=: u)) = {-# SCC toCP' #-}
      CP (CPInfo (weight t' u') (-(overlap info)) l2 l1) (Critical info' (t' :=: u')) l1 l2
      where
        Critical info' (t' :=: u') = canonicalise (Critical info (order (t :=: u)))

    weight t u
      | u `lessEq` t = f t u + penalty t u
      | otherwise    = (f t u `max` f u t) + penalty t u
      where
        f t u = 2*size' t + size u + length (vars u \\ vars t) + length (usort (vars t) \\ vars u) + if useGroundPenalty s && null (vars u) then 5 else 0
        size' t =
          size t +
          -- Lots of different constants are probably bad
          length (usort [ x | x <- funs t, arity x == 0 ]) +
          -- Lots of (maybe the same) constants are probably slightly bad
          ilog (length [ x | x <- funs t, arity x == 0 ]) +
          -- Expressions of the form f(f(f(f(f(...))))) where f is size 0
          -- are definitely bad!
          ilog (length [ x | (x,y) <- zip (funs t) (tail (funs t)), x == y, arity x == 1 && size x == 0 ])
        ilog n | n < 4 = 0
        ilog n = 1 + ilog (n `div` 4)

    penalty t u
      | useSkolemPenalty s &&
        result (normaliseSkolem s t) == result (normaliseSkolem s u) =
        -- Arbitrary heuristic: assume one in three of the variables need to
        -- be instantiated with with terms of size > 1 to not be joinable
        (length (vars t) + length (vars u)) `div` 3
      | otherwise = 0

--------------------------------------------------------------------------------
-- Tracing.
--------------------------------------------------------------------------------

data Event f =
    NewRule (Rule f)
  | ExtraRule (Rule f)
  | NewCP (Passive f)
  | Reduce (Simplification f) (Rule f)
  | Consider (Critical (Equation f))
  | Discharge (Critical (Equation f)) (Model f)
  | NormaliseCPs (KBC f)

trace :: Function f => Event f -> a -> a
trace (NewRule rule) = traceIf True (hang (text "New rule") 2 (pPrint rule))
trace (ExtraRule rule) = traceIf True (hang (text "Extra rule") 2 (pPrint rule))
trace (NewCP cp) = traceIf False (hang (text "Critical pair") 2 (pPrint cp))
trace (Reduce red rule) = traceIf True (sep [pPrint red, nest 2 (text "using"), nest 2 (pPrint rule)])
trace (Consider eq) = traceIf False (sep [text "Considering", nest 2 (pPrint eq)])
trace (Discharge eq fs) = traceIf True (sep [text "Discharge", nest 2 (pPrint eq), text "under", nest 2 (pPrint fs)])
trace (NormaliseCPs s) = traceIf True (text "" $$ text "Normalising unprocessed critical pairs." $$ text (report s) $$ text "")

traceM :: (Monad m, Function f) => Event f -> m ()
traceM x = trace x (return ())

traceIf :: Bool -> Doc -> a -> a
traceIf True x = Debug.Trace.trace (show x)
traceIf False _ = id
