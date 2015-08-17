-- Knuth-Bendix completion, with lots of exciting tricks for
-- unorientable equations.

{-# LANGUAGE CPP, TypeFamilies, FlexibleContexts, RecordWildCards, ScopedTypeVariables, UndecidableInstances, StandaloneDeriving #-}
module KBC where

#include "errors.h"
import KBC.Base
import KBC.Constraints
import KBC.Equation
import qualified KBC.Index as Index
import KBC.Index(Index)
import KBC.Queue hiding (queue)
import KBC.Rewrite
import KBC.Term
import KBC.Utils
import Control.Monad
import Data.Maybe
import Data.Ord
import qualified Data.Rewriting.CriticalPair as CP
import Data.Rewriting.Rule(Rule(..))
import qualified Debug.Trace
import Control.Monad.Trans.State.Strict
import Data.List
import Data.Function

--------------------------------------------------------------------------------
-- Completion engine state.
--------------------------------------------------------------------------------

data KBC f v =
  KBC {
    maxSize       :: Int,
    labelledRules :: Index (Labelled (Critical (Oriented (Rule f v)))),
    extraRules    :: Index (Oriented (Rule f v)),
    goals         :: [Tm f v],
    totalCPs      :: Int,
    renormaliseAt :: Int,
    queue         :: Queue (CP f v) }
  deriving Show

initialState :: Int -> [Tm f v] -> KBC f v
initialState maxSize goals =
  KBC {
    maxSize       = maxSize,
    labelledRules = Index.empty,
    extraRules    = Index.empty,
    goals         = goals,
    totalCPs      = 0,
    renormaliseAt = 1000,
    queue         = empty }

report :: (Ord f, Ord v, Sized f, Minimal f) => KBC f v -> String
report KBC{..} =
  show (length rs) ++ " rules, of which " ++
  show (length (filter ((== Oriented) . orientation) rs)) ++ " oriented, " ++
  show (length (filter ((== Unoriented) . orientation) rs)) ++ " unoriented, " ++
  show (length [ r | r@(MkOriented (WeaklyOriented _) _) <- rs ]) ++ " weakly oriented. " ++
  show (length (Index.elems extraRules)) ++ " extra rules. " ++
  show (queueSize queue) ++ " queued critical pairs out of " ++ show totalCPs ++ " total."
  where
    rs = map (critical . peel) (Index.elems labelledRules)

enqueueM ::
  (PrettyTerm f, Minimal f, Sized f, Ord f, Ord v, Numbered v, Pretty v) =>
  Label -> [Labelled (CP f v)] -> State (KBC f v) ()
enqueueM l eqns = do
  let eqns' = [Labelled l' cp { cpIndex = i } | (i, Labelled l' cp) <- zip [0..] eqns]
  modify $ \s -> s {
    queue    = enqueue l eqns' (queue s),
    totalCPs = totalCPs s + length eqns }

dequeueM ::
  (Minimal f, Sized f, Ord f, Ord v) =>
  State (KBC f v) (Maybe (Label, Label, CP f v))
dequeueM =
  state $ \s ->
    case dequeue (queue s) of
      Nothing -> (Nothing, s)
      Just (l1, l2, x, q) -> (Just (l1, l2, x), s { queue = q })

newLabelM :: State (KBC f v) Label
newLabelM =
  state $ \s ->
    case newLabel (queue s) of
      (l, q) -> (l, s { queue = q })

--------------------------------------------------------------------------------
-- Rewriting.
--------------------------------------------------------------------------------

rules :: (Ord f, Ord v) => KBC f v -> Index (Oriented (Rule f v))
rules k =
  Index.mapMonotonic (critical . peel) (labelledRules k)
  `Index.union` extraRules k

normalise ::
  (PrettyTerm f, Pretty v, Minimal f, Sized f, Ord f, Ord v, Numbered f, Numbered v) =>
  KBC f v -> Tm f v -> Reduction f v
normalise s = normaliseWith (anywhere (rewrite (rules s)))

normaliseIn ::
  (PrettyTerm f, Pretty v, Minimal f, Sized f, Ord f, Ord v, Numbered f, Numbered v) =>
  KBC f v -> [Formula f v] -> Tm f v -> Reduction f v
normaliseIn s model =
  normaliseWith (anywhere (rewriteInModel (rules s) model))

normaliseSub ::
  (PrettyTerm f, Pretty v, Minimal f, Sized f, Ord f, Ord v, Numbered f, Numbered v) =>
  KBC f v -> Tm f v -> [Formula f v] -> Tm f v -> Reduction f v
normaliseSub s top model t
  | lessEq t top && isNothing (unify t top) =
    normaliseWith (anywhere (rewriteSub (rules s) top model)) t
  | otherwise = normaliseWith (\_ -> []) t

normaliseCP ::
  (PrettyTerm f, Pretty v, Minimal f, Sized f, Ord f, Ord v, Numbered f, Numbered v) =>
  KBC f v -> Critical (Equation f v) -> Maybe (Critical (Equation f v))
normaliseCP s (Critical top (t :=: u))
  | t  == u          = Nothing
  | t' == u'         = Nothing
  | subsumed t' u'   = Nothing
  | t'' == u''       = Nothing
  | subsumed t'' u'' = Nothing
  | otherwise = Just (Critical top (t' :=: u'))
  where
    t'  = result (normalise s t)
    u'  = result (normalise s u)
    t'' = result (normaliseSub s top m t')
    u'' = result (normaliseSub s top m u')
    m = fst (solve (vars t' ++ vars u') trueBranch)
    subsumed t u =
      or [ rhs (rule x) == u | x <- anywhere (flip Index.lookup rs) t ] ||
      or [ rhs (rule x) == t | x <- nested (anywhere (flip Index.lookup rs)) u ] ||
      or [ rhs (rule x) == t | (x, x') <- Index.lookup' u rs, not (isVariantOf (lhs (rule x')) u) ]
    rs = rules s

--------------------------------------------------------------------------------
-- Completion loop.
--------------------------------------------------------------------------------

complete ::
  (PrettyTerm f, Minimal f, Sized f, Ord f, Ord v, Numbered f, Numbered v, Pretty v) =>
  State (KBC f v) ()
complete = do
  res <- complete1
  when res complete

complete1 ::
  (PrettyTerm f, Minimal f, Sized f, Ord f, Ord v, Numbered f, Numbered v, Pretty v) =>
  State (KBC f v) Bool
complete1 = do
  KBC{..} <- get
  when (totalCPs >= renormaliseAt) $ do
    normaliseCPs
    modify (\s -> s { renormaliseAt = renormaliseAt * 3 })

  res <- dequeueM
  case res of
    Just (_, _, cp) -> do
      consider (cpEquation cp)
      modify $ \s -> s { goals = map (result . normalise s) goals }
      return True
    Nothing ->
      return False

normaliseCPs ::
  forall f v.
  (PrettyTerm f, Minimal f, Sized f, Ord f, Ord v, Numbered f, Numbered v, Pretty v) =>
  State (KBC f v) ()
normaliseCPs = do
  s@KBC{..} <- get
  traceM (NormaliseCPs totalCPs :: Event f v)
  put s { queue = emptyFrom queue }
  forM_ (toList queue) $ \(Labelled l cps) ->
    queueCPs l (map (fmap (return . cpEquation)) cps)
  modify (\s -> s { totalCPs = totalCPs })

consider ::
  (PrettyTerm f, Minimal f, Sized f, Ord f, Ord v, Numbered f, Numbered v, Pretty v) =>
  Critical (Equation f v) -> State (KBC f v) ()
consider pair = do
  traceM (Consider pair)
  s <- get
  case normaliseCP s pair of
    Nothing -> return ()
    Just (Critical top eq) ->
      forM_ (orient eq) $ \r@(MkOriented _ (Rule t u)) -> do
        s <- get
        case normaliseCP s (Critical top (t :=: u)) of
          Nothing -> return ()
          Just eq | groundJoinable s (branches (And [])) eq -> do
            traceM (ExtraRule (canonicalise r))
            modify (\s -> s { extraRules = Index.insert r (extraRules s) })
          _ -> do
            traceM (NewRule (canonicalise r))
            l <- addRule (Critical top r)
            addCriticalPairs l r
            interreduce r

groundJoinable :: (Numbered f, Numbered v, Sized f, Minimal f, Ord f, Ord v, PrettyTerm f, Pretty v) =>
  KBC f v -> [Branch f v] -> Critical (Equation f v) -> Bool
groundJoinable s ctx r@(Critical top (t :=: u)) =
  case partition (isNothing . snd) (map (solve (usort (vars t ++ vars u))) ctx) of
    ([], instances) ->
      let rs = [ substf (evalSubst sub) r | (_, Just sub) <- instances ] in
      all (groundJoinable s (branches (And []))) (usort (map canonicalise rs))
    ((model, Nothing):_, _)
      | isJust (normaliseCP s (Critical top (t' :=: u'))) -> False
      | otherwise ->
          let rs = shrinkList model (\fs -> isNothing (normaliseCP s (Critical top (result (normaliseIn s fs t) :=: result (normaliseIn s fs u)))))
              nt = normaliseIn s rs t
              nu = normaliseIn s rs u
              rs' = strengthen rs (\fs -> valid fs nt && valid fs nu)

              diag [] = Or []
              diag (r:rs) = negateFormula r ||| (weaken r &&& diag rs)
              weaken (LessEq t u) = Less t u
              weaken x = x
              ctx' = formAnd (diag rs') ctx in

          trace (Discharge r rs') $
          groundJoinable s ctx' r
      where
        Reduction t' _ = normaliseIn s model t
        Reduction u' _ = normaliseIn s model u
    _ -> __

valid :: (Sized f, Minimal f, Ord f, Ord v, PrettyTerm f, Pretty v) => [Formula f v] -> Reduction f v -> Bool
valid model Reduction{..} = all valid1 steps
  where
    valid1 orule = allowedInModel model orule

shrinkList :: [a] -> ([a] -> Bool) -> [a]
shrinkList [] _ = []
shrinkList (x:xs) p
  | p xs = shrinkList xs p
  | otherwise = x:shrinkList xs (\ys -> p (x:ys))

strengthen :: [Formula f v] -> ([Formula f v] -> Bool) -> [Formula f v]
strengthen [] _ = []
strengthen (Less t u:xs) p
  | p (LessEq t u:xs) = strengthen (LessEq t u:xs) p
  | otherwise = Less t u:strengthen xs (\ys -> p (Less t u:ys))
strengthen (x:xs) p = x:strengthen xs (\ys -> p (x:ys))

addRule :: (PrettyTerm f, Minimal f, Sized f, Ord f, Ord v, Numbered f, Numbered v, Pretty v) => Critical (Oriented (Rule f v)) -> State (KBC f v) Label
addRule rule = do
  l <- newLabelM
  modify (\s -> s { labelledRules = Index.insert (Labelled l rule) (labelledRules s) })
  return l

deleteRule :: (Minimal f, Sized f, Ord f, Ord v, Numbered f, Numbered v) => Label -> Critical (Oriented (Rule f v)) -> State (KBC f v) ()
deleteRule l rule =
  modify $ \s ->
    s { labelledRules = Index.delete (Labelled l rule) (labelledRules s),
        queue = deleteLabel l (queue s) }

data Simplification f v = Simplify (Critical (Oriented (Rule f v))) | Reorient (Critical (Oriented (Rule f v))) deriving Show

instance (PrettyTerm f, Pretty v) => Pretty (Simplification f v) where
  pPrint (Simplify rule) = text "Simplify" <+> pPrint rule
  pPrint (Reorient rule) = text "Reorient" <+> pPrint rule

interreduce :: (PrettyTerm f, Ord f, Minimal f, Sized f, Ord v, Numbered f, Numbered v, Pretty v) => Oriented (Rule f v) -> State (KBC f v) ()
interreduce new = do
  rules <- gets (Index.elems . labelledRules)
  forM_ rules $ \(Labelled l old) -> do
    s <- get
    case reduceWith s l new old of
      Nothing -> return ()
      Just red -> do
        traceM (Reduce red new)
        case red of
          Simplify rule -> simplifyRule l rule
          Reorient rule@(Critical top (MkOriented _ (Rule t u))) -> do
            deleteRule l rule
            queueCPs noLabel [Labelled noLabel [Critical top (t :=: u)]]

reduceWith :: (PrettyTerm f, Pretty v, Minimal f, Sized f, Ord f, Ord v, Numbered f, Numbered v) => KBC f v -> Label -> Oriented (Rule f v) -> Critical (Oriented (Rule f v)) -> Maybe (Simplification f v)
reduceWith s lab new (Critical top old@(MkOriented _ (Rule l r)))
  | not (lhs (rule new) `isInstanceOf` l) &&
    not (null (anywhere (tryRule new) l)) =
      Just (Reorient (Critical top old))
  | not (lhs (rule new) `isInstanceOf` l) &&
    orientation new == Unoriented &&
    not (all isNothing [ match (lhs (rule new)) l' | l' <- subterms l ]) &&
    groundJoinable s' (branches (And [])) (Critical top (l :=: r)) =
      Just (Reorient (Critical top old))
  | not (null (anywhere (tryRule new) (rhs (rule old)))) =
      Just (Simplify (Critical top old))
  | orientation old == Unoriented &&
    orientation new == Unoriented &&
    not (all isNothing [ match (lhs (rule new)) r' | r' <- subterms r ]) &&
    groundJoinable s' (branches (And [])) (Critical top (l :=: r)) =
      Just (Reorient (Critical top old))
  | otherwise = Nothing
  where
    s' = s { labelledRules = Index.delete (Labelled lab (Critical top old)) (labelledRules s) }

simplifyRule :: (PrettyTerm f, Pretty v, Minimal f, Sized f, Ord f, Ord v, Numbered f, Numbered v) => Label -> Critical (Oriented (Rule f v)) -> State (KBC f v) ()
simplifyRule l rule@(Critical top (MkOriented ctx (Rule lhs rhs))) = do
  modify $ \s ->
    s {
      labelledRules =
         Index.insert (Labelled l (Critical top (MkOriented ctx (Rule lhs (result (normalise s rhs))))))
           (Index.delete (Labelled l rule) (labelledRules s)) }

addCriticalPairs :: (PrettyTerm f, Ord f, Minimal f, Sized f, Ord v, Numbered f, Numbered v, Pretty v) => Label -> Oriented (Rule f v) -> State (KBC f v) ()
addCriticalPairs l new = do
  s <- get
  rules <- gets labelledRules
  size  <- gets maxSize
  queueCPs l $
    criticalPairs s size new (Index.mapMonotonic (fmap critical) rules) ++
    [ cp
    | Labelled l' (Critical _ old) <- Index.elems rules,
      cp <- criticalPairs s size old (Index.singleton (Labelled l' new)) ]

newEquation ::
  (PrettyTerm f, Pretty v, Minimal f, Sized f, Ord f, Ord v, Numbered f, Numbered v) =>
  Equation f v -> State (KBC f v) ()
newEquation (t :=: u) = do
  consider (Critical minimalTerm (t :=: u))
  return ()

--------------------------------------------------------------------------------
-- Critical pairs.
--------------------------------------------------------------------------------

data Critical a =
  Critical {
    top      :: TmOf a,
    critical :: a }

instance Eq a => Eq (Critical a) where x == y = critical x == critical y
instance Ord a => Ord (Critical a) where compare = comparing critical

instance (PrettyTerm (ConstantOf a), Pretty (VariableOf a), Pretty a) => Pretty (Critical a) where
  pPrint Critical{..} =
    hang (pPrint critical) 2 (text "from" <+> pPrint top)

deriving instance (Show a, Show (ConstantOf a), Show (VariableOf a)) => Show (Critical a)

instance Symbolic a => Symbolic (Critical a) where
  type ConstantOf (Critical a) = ConstantOf a
  type VariableOf (Critical a) = VariableOf a

  termsDL Critical{..} = termsDL critical `mplus` termsDL top
  substf sub Critical{..} = Critical (substf sub top) (substf sub critical)

data CP f v =
  CP {
    cpWeight    :: Int,
    cpIndex     :: Int,
    cpEquation  :: Critical (Equation f v) } deriving (Eq, Show)

instance (Minimal f, Sized f, Ord f, Ord v) => Ord (CP f v) where
  compare = comparing (\x -> (cpWeight x, cpIndex x))

instance (Minimal f, PrettyTerm f, Pretty v) => Pretty (CP f v) where
  pPrint = pPrint . cpEquation

criticalPairs :: (PrettyTerm f, Pretty v, Minimal f, Sized f, Ord f, Ord v, Numbered v, Numbered f) => KBC f v -> Int -> Oriented (Rule f v) -> Index (Labelled (Oriented (Rule f v))) -> [Labelled [Critical (Equation f v)]]
criticalPairs s n r idx =
  map pick (groupBy ((==) `on` f) (sortBy (comparing f) (criticalPairs1 s n r idx)))
  where
    f (t, Labelled l _) = (t, l)
    pick xs@((_, Labelled l _):_) = Labelled l (map (peel . snd) xs)

criticalPairs1 :: (PrettyTerm f, Pretty v, Minimal f, Sized f, Ord f, Ord v, Numbered v, Numbered f) => KBC f v -> Int -> Oriented (Rule f v) -> Index (Labelled (Oriented (Rule f v))) -> [(Tm f v, Labelled (Critical (Equation f v)))]
criticalPairs1 s n (MkOriented or1 r1@(Rule t _)) idx = do
  Labelled l (MkOriented or2 r2) <- Index.elems idx
  cp <- CP.cps [r2] [r1]
  let f (Left x)  = withNumber (number x*2) x
      f (Right x) = withNumber (number x*2+1) x
      left = rename f (CP.left cp)
      right = rename f (CP.right cp)
      top = rename f (CP.top cp)

      inner = fromMaybe __ (subtermAt top (CP.leftPos cp))
      sz = size top

  guard (left /= top && right /= top)
  when (or1 == Unoriented) $ guard (not (lessEq top right))
  when (or2 == Unoriented) $ guard (not (lessEq top left))
  guard (size top <= n)
  guard (null (nested (anywhere (rewrite (rules s))) inner))
  return (canonicalise (fromMaybe __ (subtermAt t (CP.leftPos cp))),
          Labelled l (Critical top (left :=: right)))

queueCPs ::
  (PrettyTerm f, Minimal f, Sized f, Ord f, Ord v, Numbered f, Numbered v, Pretty v) =>
  Label -> [Labelled [(Critical (Equation f v))]] -> State (KBC f v) ()
queueCPs l eqnss = do
  s <- get
  let cps =
        usortBy (comparing (critical . cpEquation . peel)) $
        [ Labelled l' (minimum cps)
        | Labelled l' eqns <- eqnss,
          cps@(_:_) <- [catMaybes (map (toCP s) eqns)] ]
  mapM_ (traceM . NewCP . peel) cps
  enqueueM l cps

toCP ::
  (PrettyTerm f, Minimal f, Sized f, Ord f, Ord v, Numbered f, Numbered v, Pretty v) =>
  KBC f v -> Critical (Equation f v) -> Maybe (CP f v)
toCP s (Critical top (t :=: u))
  | t  == u   = Nothing
  | t' == u'  = Nothing
  | otherwise =
    Just (CP (weight t'' u'') 0 (Critical top' (t'' :=: u'')))
  where
    t' = result (normalise s t)
    u' = result (normalise s u)
    Critical top' (t'' :=: u'') = canonicalise (Critical top (order (t' :=: u')))

    weight t u
      | u `lessEq` t = f t u + penalty t u
      | otherwise    = (f t u `min` f u t) + penalty t u
      where
        f t u = size t + size u + length (vars u \\ vars t) + length (usort (vars t) \\ vars u)

    penalty t u
      | result (normalise s (skolemise t)) == result (normalise s (skolemise u)) =
        length (vars t) `max` length (vars u)
      | otherwise = 0

--------------------------------------------------------------------------------
-- Tracing.
--------------------------------------------------------------------------------

data Event f v =
    NewRule (Oriented (Rule f v))
  | ExtraRule (Oriented (Rule f v))
  | Reduce (Simplification f v) (Oriented (Rule f v))
  | NewCP (CP f v)
  | Consider (Critical (Equation f v))
  | Discharge (Critical (Equation f v)) [Formula f v]
  | NormaliseCPs Int

trace :: (Minimal f, PrettyTerm f, Pretty v) => Event f v -> a -> a
trace (NewRule rule) = traceIf True (hang (text "New rule") 2 (pPrint rule))
trace (ExtraRule rule) = traceIf True (hang (text "Extra rule") 2 (pPrint rule))
trace (Reduce red rule) = traceIf True (sep [pPrint red, nest 2 (text "using"), nest 2 (pPrint rule)])
trace (NewCP cps) = traceIf False (hang (text "Critical pair") 2 (pPrint cps))
trace (Consider eq) = traceIf False (sep [text "Considering", nest 2 (pPrint eq)])
trace (Discharge eq fs) = traceIf True (sep [text "Discharge", nest 2 (pPrint eq), text "under", nest 2 (pPrint fs)])
trace (NormaliseCPs n) = traceIf True (text "Normalise unprocessed critical pairs after generating" <+> pPrint n)

traceM :: (Monad m, Minimal f, PrettyTerm f, Pretty v) => Event f v -> m ()
traceM x = trace x (return ())

traceIf :: Bool -> Doc -> a -> a
traceIf True x = Debug.Trace.trace (show x)
traceIf False _ = id
