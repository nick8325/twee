-- Knuth-Bendix completion, up to an adjustable size limit.
-- Does constrained rewriting for unorientable equations.

{-# LANGUAGE CPP, TypeFamilies, FlexibleContexts #-}
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
import qualified Data.Set as Set
import Data.Set(Set)
import qualified Debug.Trace
import Control.Monad.Trans.State.Strict
import Data.Map.Strict(Map)

data Event f v =
    NewRule (Constrained (Rule f v))
  | Reduce (Simplification f v) (Constrained (Rule f v))
  | NewCP (CP f v)
  | Consider (Constrained (Equation f v))
  | Split (Constrained (Equation f v)) [Constrained (Equation f v)]
  | Discharge (Constrained (Equation f v)) [Formula Simple f v]

traceM :: (Monad m, PrettyTerm f, Pretty v) => Event f v -> m ()
traceM (NewRule rule) = traceIf True (hang (text "New rule") 2 (pPrint rule))
traceM (Reduce red rule) = traceIf True (sep [pPrint red, nest 2 (text "using"), nest 2 (pPrint rule)])
traceM (NewCP cps) = traceIf True (hang (text "Critical pair") 2 (pPrint cps))
traceM (Consider eq) = traceIf True (sep [text "Considering", nest 2 (pPrint eq)])
traceM (Split eq []) = traceIf True (sep [text "Split", nest 2 (pPrint eq), text "into nothing"])
traceM (Split eq eqs) = traceIf True (sep [text "Split", nest 2 (pPrint eq), text "into", nest 2 (vcat (map pPrint eqs))])
traceM (Discharge eq fs) = traceIf True (sep [text "Discharge", nest 2 (pPrint eq), text "under", nest 2 (pPrint fs)])
traceIf :: Monad m => Bool -> Doc -> m ()
traceIf True x = Debug.Trace.traceM (show x)
traceIf _ _ = return ()

data KBC f v =
  KBC {
    maxSize       :: Int,
    labelledRules :: Index (Labelled (Constrained (Rule f v))),
    queue         :: Queue (CP f v) }
  deriving Show

data CP f v =
  CP {
    cpSize      :: Int,
    cpSizeRight :: Int,
    cpEquation  :: Constrained (Equation f v) } deriving (Eq, Show)

instance (Minimal f, Sized f, Ord f, Ord v) => Ord (CP f v) where
  compare =
    comparing $ \(CP size size' (Constrained _ (l :==: r))) ->
      (size, size', l, r)

instance (PrettyTerm f, Pretty v) => Pretty (CP f v) where
  pPrint = pPrint . cpEquation

report :: KBC f v -> String
report s = show r ++ " rewrite rules."
  where
    r = length (Index.elems (labelledRules s))

initialState :: Int -> KBC f v
initialState maxSize =
  KBC {
    maxSize       = maxSize,
    labelledRules = Index.empty,
    queue         = empty }

enqueueM ::
  (PrettyTerm f, Minimal f, Sized f, Ord f, Ord v, Numbered v, Pretty v) =>
  Label -> [Labelled (CP f v)] -> StateT (KBC f v) IO ()
enqueueM l eqns = do
  modify (\s -> s { queue = enqueue l eqns (queue s) })

dequeueM ::
  (Minimal f, Sized f, Ord f, Ord v) =>
  StateT (KBC f v) IO (Maybe (Label, Label, CP f v))
dequeueM =
  state $ \s ->
    case dequeue (queue s) of
      Nothing -> (Nothing, s)
      Just (l1, l2, x, q) -> (Just (l1, l2, x), s { queue = q })

newLabelM :: StateT (KBC f v) IO Label
newLabelM =
  state $ \s ->
    case newLabel (queue s) of
      (l, q) -> (l, s { queue = q })

rules :: KBC f v -> Index (Constrained (Rule f v))
rules = Index.mapMonotonic peel . labelledRules

normaliser ::
  (PrettyTerm f, Pretty v, Minimal f, Sized f, Ord f, Ord v, Numbered f, Numbered v) =>
  StateT (KBC f v) IO (Tm f v -> Reduction f v)
normaliser = do
  rules <- gets rules
  return $
    normaliseWith (anywhere (rewrite rules))

modelNormaliser ::
  (PrettyTerm f, Pretty v, Minimal f, Sized f, Ord f, Ord v, Numbered f, Numbered v) =>
  Map v (Extended f v) -> StateT (KBC f v) IO (Tm f v -> Reduction f v)
modelNormaliser model = do
  rules <- gets rules
  return $
    normaliseWith (anywhere (rewriteInModel rules model))

specificNormaliser ::
  (PrettyTerm f, Pretty v, Minimal f, Sized f, Ord f, Ord v, Numbered f, Numbered v) =>
  StateT (KBC f v) IO (Set (Formula Simple f v) -> Tm f v -> Reduction f v)
specificNormaliser = do
  rules <- gets rules
  return $ \forms ->
    normaliseWith (anywhere (rewriteAllowing rules forms))

newEquation ::
  (PrettyTerm f, Pretty v, Minimal f, Sized f, Ord f, Ord v, Numbered f, Numbered v) =>
  Equation f v -> StateT (KBC f v) IO ()
newEquation (t :==: u) =
  queueCPs noLabel [Labelled noLabel (Constrained (toConstraint true) (t :==: u))]

queueCPs ::
  (PrettyTerm f, Minimal f, Sized f, Ord f, Ord v, Numbered f, Numbered v, Pretty v) =>
  Label -> [Labelled (Constrained (Equation f v))] -> StateT (KBC f v) IO ()
queueCPs l eqns = do
  norm <- normaliser
  maxN <- gets maxSize
  let cps = [ Labelled l' (CP n (size u') (Constrained ctx (t' :==: u')))
            | Labelled l' (Constrained ctx (t :==: u)) <- eqns,
              formula ctx /= false,
              t /= u,
              let t' :==: u' = order (result (norm t) :==: result (norm u)),
              t' /= u',
              let n = size t',
              n <= fromIntegral maxN ]
  mapM_ (traceM . NewCP . peel) cps
  enqueueM l cps

toCP ::
  (Minimal f, Sized f, Ord f, Ord v, Numbered v, PrettyTerm f, Pretty v) =>
  (Tm f v -> Tm f v) ->
  Constrained (Equation f v) -> Maybe (CP f v)
toCP norm (Constrained ctx (l :==: r)) = do
  guard (l /= r)
  let l' :==: r' = order (norm l :==: norm r)
  guard (l' /= r')
  return (CP (size l') (size r') (Constrained ctx (l' :==: r')))

complete1 ::
  (PrettyTerm f, Minimal f, Sized f, Ord f, Ord v, Numbered f, Numbered v, Pretty v) =>
  StateT (KBC f v) IO Bool
complete1 = do
  res <- dequeueM
  case res of
    Just (l1, l2, cp) -> do
      consider l1 l2 (cpEquation cp)
      return True
    Nothing ->
      return False

complete ::
  (PrettyTerm f, Minimal f, Sized f, Ord f, Ord v, Numbered f, Numbered v, Pretty v) =>
  StateT (KBC f v) IO ()
complete = do
  res <- complete1
  when res complete

consider ::
  (PrettyTerm f, Minimal f, Sized f, Ord f, Ord v, Numbered f, Numbered v, Pretty v) =>
  Label -> Label -> Constrained (Equation f v) -> StateT (KBC f v) IO ()
consider l1 l2 pair@(Constrained ctx (t :==: u)) = unless (formula ctx == false) $ do
  traceM (Consider pair)
  norm <- normaliser
  t <- return (result (norm t))
  u <- return (result (norm u))
  rs <- gets rules
  unless (t == u) $ do
    case map toModel (solve (branches ctx)) of
      [] -> do
        let pairs = usort (map canonicalise (instantiate (Constrained ctx (t :==: u))))
        traceM (Split pair pairs)
        queueCPs l1 (map (Labelled l2) pairs)
      model:_ -> do
        norm <- modelNormaliser model
        let Reduction t' rs1 = norm t
            Reduction u' rs2 = norm u
        cond <-
          case t' == u' of
            True -> do
              snorm <- specificNormaliser
              let rs = shrinkList (usort (map (formula . constraint) rs1 ++ map (formula . constraint) rs2))
                                  (\fs -> result (snorm (Set.fromList fs) t) == result (snorm (Set.fromList fs) u))
              traceM (Discharge pair rs)
              return (foldr (&&&) true rs)
            False -> do
              let applicable rule =
                    not (null (anywhere (tryRuleInModel model rule) t')) ||
                    not (null (anywhere (tryRuleInModel model rule) u'))
                  rule:_ = filter applicable (orient (t' :==: u'))
              traceM (NewRule (canonicalise rule))
              l <- addRule rule
              interreduce rule
              addCriticalPairs l rule
              return (formula (constraint rule))
        consider l1 l2 (Constrained (toConstraint (formula ctx &&& negateFormula cond)) (t :==: u))

shrinkList :: [a] -> ([a] -> Bool) -> [a]
shrinkList [] _ = []
shrinkList (x:xs) p
  | p xs = shrinkList xs p
  | otherwise = x:shrinkList xs (\ys -> p (x:ys))

addRule :: (PrettyTerm f, Minimal f, Sized f, Ord f, Ord v, Numbered f, Numbered v, Pretty v) => Constrained (Rule f v) -> StateT (KBC f v) IO Label
addRule rule = do
  l <- newLabelM
  modify (\s -> s { labelledRules = Index.insert (Labelled l rule) (labelledRules s) })
  return l

deleteRule :: (Minimal f, Sized f, Ord f, Ord v, Numbered f, Numbered v) => Label -> Constrained (Rule f v) -> StateT (KBC f v) IO ()
deleteRule l rule =
  modify $ \s ->
    s { labelledRules = Index.delete (Labelled l rule) (labelledRules s),
        queue = deleteLabel l (queue s) }

data Simplification f v = Simplify (Constrained (Rule f v)) | Reorient (Constrained (Rule f v)) deriving Show

instance (PrettyTerm f, Pretty v) => Pretty (Simplification f v) where
  pPrint (Simplify rule) = text "Simplify" <+> pPrint rule
  pPrint (Reorient rule) = text "Reorient" <+> pPrint rule

interreduce :: (PrettyTerm f, Ord f, Minimal f, Sized f, Ord v, Numbered f, Numbered v, Pretty v) => Constrained (Rule f v) -> StateT (KBC f v) IO ()
interreduce new = do
  rules <- gets (Index.elems . labelledRules)
  let reductions = catMaybes (map (moveLabel . fmap (reduceWith new)) rules)
  sequence_ [ traceM (Reduce red new) | red <- map peel reductions ]
  sequence_ [ simplifyRule l rule | Labelled l (Simplify rule) <- reductions ]
  sequence_ [ newEquation (unorient (constrained rule)) | Reorient rule <- map peel reductions ]
  sequence_ [ deleteRule l rule | Labelled l (Reorient rule) <- reductions ]

reduceWith :: (PrettyTerm f, Pretty v, Minimal f, Sized f, Ord f, Ord v, Numbered f, Numbered v) => Constrained (Rule f v) -> Constrained (Rule f v) -> Maybe (Simplification f v)
reduceWith new old
  | not (lhs (constrained new) `isInstanceOf` lhs (constrained old)) &&
    not (null (anywhere (tryRule new) (lhs (constrained old)))) =
      Just (Reorient old)
  | not (null (anywhere (tryRule new) (rhs (constrained old)))) =
      Just (Simplify old)
  | otherwise = Nothing

simplifyRule :: (PrettyTerm f, Pretty v, Minimal f, Sized f, Ord f, Ord v, Numbered f, Numbered v) => Label -> Constrained (Rule f v) -> StateT (KBC f v) IO ()
simplifyRule l rule@(Constrained ctx (Rule lhs rhs)) = do
  norm <- normaliser
  modify $ \s ->
    s {
      labelledRules =
         Index.insert (Labelled l (Constrained ctx (Rule lhs (result (norm rhs)))))
           (Index.delete (Labelled l rule) (labelledRules s)) }

addCriticalPairs :: (PrettyTerm f, Ord f, Minimal f, Sized f, Ord v, Numbered f, Numbered v, Pretty v) => Label -> Constrained (Rule f v) -> StateT (KBC f v) IO ()
addCriticalPairs l new = do
  rules <- gets labelledRules
  size  <- gets maxSize
  queueCPs l $
    [ Labelled l' cp
    | Labelled l' old <- Index.elems rules,
      cp <- criticalPairs size new old ++ criticalPairs size old new ]

canonicaliseBoth :: (Symbolic a, Ord (VariableOf a), Numbered (VariableOf a)) => (a, a) -> (a, a)
canonicaliseBoth (x, y) = (x', substf (Var . increase) y')
  where
    x' = canonicalise x
    y' = canonicalise y
    n  = maximum (0:map (succ . number) (vars x'))
    increase v = withNumber (n+number v) v

criticalPairs :: (PrettyTerm f, Pretty v, Minimal f, Sized f, Ord f, Ord v, Numbered v) => Int -> Constrained (Rule f v) -> Constrained (Rule f v) -> [Constrained (Equation f v)]
criticalPairs _ r1 r2 = do
  let (Constrained ctx1 r1', Constrained ctx2 r2') = canonicaliseBoth (r1, r2)
  cp <- CP.cps [r1'] [r2']
  let sub = CP.subst cp
      f (Left x)  = x
      f (Right x) = x
      left = rename f (CP.left cp)
      right = rename f (CP.right cp)
      ctx =
        toConstraint $
          substf (rename f . evalSubst sub . Left) (formula ctx1) &&&
          substf (rename f . evalSubst sub . Right) (formula ctx2)

  return (Constrained ctx (left :==: right))
