-- Knuth-Bendix completion, up to an adjustable size limit.
-- Does constrained rewriting for unorientable equations.

{-# LANGUAGE CPP, TypeFamilies, FlexibleContexts, RecordWildCards #-}
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
import Data.List

data Event f v =
    NewRule (Oriented (Rule f v))
  | Reduce (Simplification f v) (Oriented (Rule f v))
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
    labelledRules :: Index (Labelled (Oriented (Rule f v))),
    extraRules    :: Index (Oriented (Rule f v)),
    queue         :: Queue (CP f v) }
  deriving Show

data CP f v =
  CP {
    cpSize      :: Int,
    cpSizeRight :: Int,
    oriented    :: Bool,
    cpEquation  :: Constrained (Equation f v) } deriving (Eq, Show)

instance (Minimal f, Sized f, Ord f, Ord v) => Ord (CP f v) where
  compare =
    comparing $ \(CP size size' oriented (Constrained ctx (l :==: r))) ->
      if oriented then size * 2 + size'
      else (size + size') * 2

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
    extraRules    = Index.empty,
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

rules :: KBC f v -> Index (Oriented (Rule f v))
rules = Index.mapMonotonic peel . labelledRules

allRules :: (Ord f, Ord v) => KBC f v -> Index (Oriented (Rule f v))
allRules state =
  Index.mapMonotonic peel (labelledRules state) `Index.union`
  extraRules state

normaliser ::
  (PrettyTerm f, Pretty v, Minimal f, Sized f, Ord f, Ord v, Numbered f, Numbered v) =>
  StateT (KBC f v) IO (Tm f v -> Reduction f v)
normaliser = do
  rules <- gets allRules
  return $
    normaliseWith (anywhere (rewrite rules))

modelNormaliser ::
  (PrettyTerm f, Pretty v, Minimal f, Sized f, Ord f, Ord v, Numbered f, Numbered v) =>
  Map v (Extended f v) -> StateT (KBC f v) IO (Tm f v -> Reduction f v)
modelNormaliser model = do
  rules <- gets allRules
  return $
    normaliseWith (anywhere (rewriteInModel rules model))

specificNormaliser ::
  (PrettyTerm f, Pretty v, Minimal f, Sized f, Ord f, Ord v, Numbered f, Numbered v) =>
  StateT (KBC f v) IO (Set (Formula Simple f v) -> Tm f v -> Reduction f v)
specificNormaliser = do
  rules <- gets allRules
  return $ \forms ->
    normaliseWith (anywhere (rewriteAllowing rules forms))

newEquation ::
  (PrettyTerm f, Pretty v, Minimal f, Sized f, Ord f, Ord v, Numbered f, Numbered v) =>
  Equation f v -> StateT (KBC f v) IO ()
newEquation (t :==: u) = do
  consider noLabel noLabel (Constrained (toConstraint true) (t :==: u))
  return ()

queueCPs ::
  (PrettyTerm f, Minimal f, Sized f, Ord f, Ord v, Numbered f, Numbered v, Pretty v) =>
  Label -> [Labelled (Constrained (Equation f v))] -> StateT (KBC f v) IO ()
queueCPs l eqns = do
  norm <- normaliser
  maxN <- gets maxSize
  let cps = [ Labelled l' (CP n (size u') (lessThan Strict u' t') (Constrained ctx (t' :==: u')))
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
  return (CP (size l') (size r') (lessThan Strict r' l') (Constrained ctx (l' :==: r')))

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

data ConsiderResult = Joined | Case | New

consider, consider1 ::
  (PrettyTerm f, Minimal f, Sized f, Ord f, Ord v, Numbered f, Numbered v, Pretty v) =>
  Label -> Label -> Constrained (Equation f v) -> StateT (KBC f v) IO ConsiderResult
consider l1 l2 pair@(Constrained _ (t :==: u)) = do
  norm <- normaliser
  res <- consider1 l1 l2 pair
  case res of
    Case -> do
      let t' = result (norm t)
          u' = result (norm u)
      --forM_ (orient (t' :==: u')) $ \rule ->
      --  modify (\s -> s { extraRules = Index.insert rule (extraRules s) })
      return res
    _ -> return res

consider1 l1 l2 pair@(Constrained ctx (t :==: u)) = if formula ctx == false then return Joined else do
  traceM (Consider pair)
  norm <- normaliser
  t <- return (result (norm t))
  u <- return (result (norm u))
  rs <- gets allRules
  let subsumed =
        or [ rhs (rule x) == u | x <- look t ] ||
        or [ rhs (rule x) == t | x <- look u ]
      look t = nested (anywhere (flip Index.lookup rs)) t ++
               [ r | r <- Index.lookup t rs, not (isVariantOf t (lhs (rule r))) ]
  case (t == u || subsumed) of
    True -> return Joined
    False -> do
      let evil ctx0 ctx =
            case map toModel (solve (branches ctx)) of
              [] -> ctx0
              model:_ ->
                let constraints =
                      map ruleConstraint $
                      anywhere (rewriteInModel rs model) t ++
                      anywhere (rewriteInModel rs model) u in
                case [ ctx' | c <- constraints, let ctx' = toConstraint (formula ctx &&& negateFormula c), not (null (map toModel (solve (branches ctx')))) ] of
                  [] -> ctx
                  (ctx':_) -> evil ctx ctx'
          nice ctx' =
            head ([ctx | ctx <- ctxs, not (null (solve (branches ctx)))] ++ [ctx'])
            where
              ctxs =
                usort $
                  [ toConstraint (ruleConstraint o &&& formula ctx) | o@MkOriented{..} <- anywhere (flip Index.lookup rs) t, rhs rule == u ] ++
                  [ toConstraint (ruleConstraint o &&& formula ctx) | o@MkOriented{..} <- anywhere (flip Index.lookup rs) u, rhs rule == t ]
      case map toModel (solve (branches (nice (evil ctx ctx)))) of
        [] -> do
          let pairs = usort (map canonicalise (instantiate (Constrained ctx (t :==: u))))
          traceM (Split pair pairs)
          queueCPs l1 (map (Labelled l2) pairs)
          --mapM_ (consider1 l1 l2) pairs
          return Case
        model:_ -> do
          norm <- modelNormaliser model
          let Reduction t' rs1 = norm t
              Reduction u' rs2 = norm u
          cond <-
            case t' == u' of
              True -> do
                snorm <- specificNormaliser
                let rs = shrinkList (usort (map ruleConstraint rs1 ++ map ruleConstraint rs2))
                                    (\fs -> result (snorm (Set.fromList fs) t) == result (snorm (Set.fromList fs) u))
                traceM (Discharge pair rs)
                return (conj [ disj (r:map negateFormula rs') | r:rs' <- inits rs ])
              False -> do
                let applicable rule =
                      not (null (anywhere (tryRuleInModel model rule) t')) ||
                      not (null (anywhere (tryRuleInModel model rule) u'))
                    rule:_ = filter applicable (orient (t' :==: u'))
                traceM (NewRule (canonicalise rule))
                l <- addRule rule
                interreduce l rule
                addCriticalPairs l rule
                return false --(ruleConstraint rule)
          res <- consider1 l1 l2 (Constrained (toConstraint (formula ctx &&& negateFormula cond)) (t :==: u))
          return $ case res of
            New -> New
            _ -> Case

shrinkList :: [a] -> ([a] -> Bool) -> [a]
shrinkList [] _ = []
shrinkList (x:xs) p
  | p xs = shrinkList xs p
  | otherwise = x:shrinkList xs (\ys -> p (x:ys))

addRule :: (PrettyTerm f, Minimal f, Sized f, Ord f, Ord v, Numbered f, Numbered v, Pretty v) => Oriented (Rule f v) -> StateT (KBC f v) IO Label
addRule rule = do
  l <- newLabelM
  modify (\s -> s { labelledRules = Index.insert (Labelled l rule) (labelledRules s) })
  return l

deleteRule :: (Minimal f, Sized f, Ord f, Ord v, Numbered f, Numbered v) => Label -> Oriented (Rule f v) -> StateT (KBC f v) IO ()
deleteRule l rule =
  modify $ \s ->
    s { labelledRules = Index.delete (Labelled l rule) (labelledRules s),
        queue = deleteLabel l (queue s) }

data Simplification f v = Simplify (Oriented (Rule f v)) | Reorient (Oriented (Rule f v)) deriving Show

instance (PrettyTerm f, Pretty v) => Pretty (Simplification f v) where
  pPrint (Simplify rule) = text "Simplify" <+> pPrint rule
  pPrint (Reorient rule) = text "Reorient" <+> pPrint rule

interreduce :: (PrettyTerm f, Ord f, Minimal f, Sized f, Ord v, Numbered f, Numbered v, Pretty v) => Label -> Oriented (Rule f v) -> StateT (KBC f v) IO ()
interreduce l new = do
  rules <- gets (Index.elems . labelledRules)
  let reductions = catMaybes (map (moveLabel . fmap (reduceWith new)) rules)
  sequence_ [ traceM (Reduce red new) | red <- map peel reductions ]
  sequence_ [ simplifyRule l rule | Labelled l (Simplify rule) <- reductions ]
  queueCPs l [Labelled noLabel (Constrained (toConstraint true) (unorient (rule r))) | Reorient r <- map peel reductions ]
  sequence_ [ deleteRule l rule | Labelled l (Reorient rule) <- reductions ]

reduceWith :: (PrettyTerm f, Pretty v, Minimal f, Sized f, Ord f, Ord v, Numbered f, Numbered v) => Oriented (Rule f v) -> Oriented (Rule f v) -> Maybe (Simplification f v)
reduceWith new old
  | not (lhs (rule new) `isInstanceOf` lhs (rule old)) &&
    not (null (anywhere (tryRule new) (lhs (rule old)))) =
      Just (Reorient old)
  | not (null (anywhere (tryRule new) (rhs (rule old)))) =
      Just (case orientation old of { Unoriented -> Reorient old; _ -> Simplify old })
  | otherwise = Nothing

simplifyRule :: (PrettyTerm f, Pretty v, Minimal f, Sized f, Ord f, Ord v, Numbered f, Numbered v) => Label -> Oriented (Rule f v) -> StateT (KBC f v) IO ()
simplifyRule l rule@(MkOriented ctx (Rule lhs rhs)) = do
  norm <- normaliser
  modify $ \s ->
    s {
      labelledRules =
         Index.insert (Labelled l (MkOriented ctx (Rule lhs (result (norm rhs)))))
           (Index.delete (Labelled l rule) (labelledRules s)) }

addCriticalPairs :: (PrettyTerm f, Ord f, Minimal f, Sized f, Ord v, Numbered f, Numbered v, Pretty v) => Label -> Oriented (Rule f v) -> StateT (KBC f v) IO ()
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

criticalPairs :: (PrettyTerm f, Pretty v, Minimal f, Sized f, Ord f, Ord v, Numbered v) => Int -> Oriented (Rule f v) -> Oriented (Rule f v) -> [Constrained (Equation f v)]
criticalPairs _ r1 r2 = do
  let (cr1@(MkOriented _ r1'), cr2@(MkOriented _ r2')) = canonicaliseBoth (r1, r2)
  cp <- CP.cps [r1'] [r2']
  let sub = CP.subst cp
      f (Left x)  = x
      f (Right x) = x
      left = rename f (CP.left cp)
      right = rename f (CP.right cp)
      ctx =
        toConstraint $
          substf (rename f . evalSubst sub . Left) (ruleConstraint cr1) &&&
          substf (rename f . evalSubst sub . Right) (ruleConstraint cr2)

  return (Constrained ctx (left :==: right))
