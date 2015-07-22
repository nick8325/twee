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
  | ExtraRule (Oriented (Rule f v))
  | Reduce (Simplification f v) (Oriented (Rule f v))
  | NewCP (CP f v)
  | Consider (Constrained (Equation f v))
  | Discharge (Oriented (Rule f v)) [Formula f v]

traceM :: (Monad m, Minimal f, PrettyTerm f, Pretty v) => Event f v -> m ()
traceM (NewRule rule) = traceIf True (hang (text "New rule") 2 (pPrint rule))
traceM (ExtraRule rule) = traceIf True (hang (text "Extra rule") 2 (pPrint rule))
traceM (Reduce red rule) = traceIf True (sep [pPrint red, nest 2 (text "using"), nest 2 (pPrint rule)])
traceM (NewCP cps) = traceIf False (hang (text "Critical pair") 2 (pPrint cps))
traceM (Consider eq) = traceIf True (sep [text "Considering", nest 2 (pPrint eq)])
traceM (Discharge eq fs) = traceIf True (sep [text "Discharge", nest 2 (pPrint eq), text "under", nest 2 (pPrint fs)])
traceIf :: Monad m => Bool -> Doc -> m ()
traceIf True x = Debug.Trace.traceM (show x)
traceIf _ _ = return ()

data KBC f v =
  KBC {
    maxSize       :: Int,
    labelledRules :: Index (Labelled (Oriented (Rule f v))),
    weakInverse   :: Index (Labelled (Rule f v)),
    extraRules    :: Index (Oriented (Rule f v)),
    queue         :: Queue (CP f v) }
  deriving Show

data CP f v =
  CP {
    cpSize      :: Int,
    cpSizeRight :: Int,
    cpIndex     :: Int,
    oriented    :: Bool,
    cpEquation  :: Constrained (Equation f v) } deriving (Eq, Show)

instance (Minimal f, Sized f, Ord f, Ord v) => Ord (CP f v) where
  compare =
    comparing $ \(CP size size' idx oriented (Constrained ctx (l :==: r))) ->
      if oriented then (size * 2 + size', idx)
      else ((size + size') * 2, idx)

instance (Minimal f, PrettyTerm f, Pretty v) => Pretty (CP f v) where
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
    weakInverse   = Index.empty,
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

rules :: (Ord f, Ord v) => KBC f v -> Index (Oriented (Rule f v))
rules k =
  Index.mapMonotonic peel (labelledRules k)
  `Index.union` extraRules k

normaliser ::
  (PrettyTerm f, Pretty v, Minimal f, Sized f, Ord f, Ord v, Numbered f, Numbered v) =>
  StateT (KBC f v) IO (Tm f v -> Reduction f v)
normaliser = do
  rules <- gets rules
  return $
    normaliseWith (anywhere (rewrite rules))

modelNormaliser ::
  (PrettyTerm f, Pretty v, Minimal f, Sized f, Ord f, Ord v, Numbered f, Numbered v) =>
  StateT (KBC f v) IO ([Formula f v] -> Tm f v -> Reduction f v)
modelNormaliser = do
  rules <- gets rules
  return $ \model ->
    normaliseWith (anywhere (rewriteInModel rules model))

newEquation ::
  (PrettyTerm f, Pretty v, Minimal f, Sized f, Ord f, Ord v, Numbered f, Numbered v) =>
  Equation f v -> StateT (KBC f v) IO ()
newEquation (t :==: u) = do
  consider noLabel noLabel (Constrained (And []) (t :==: u))
  return ()

queueCPs ::
  (PrettyTerm f, Minimal f, Sized f, Ord f, Ord v, Numbered f, Numbered v, Pretty v) =>
  Label -> [Labelled (Constrained (Equation f v))] -> StateT (KBC f v) IO ()
queueCPs l eqns = do
  norm <- normaliser
  maxN <- gets maxSize
  let eqns' =
        usort $
        [ Labelled l' (Constrained ctx' (order eq'))
        | Labelled l' (Constrained ctx (t  :==: u)) <- eqns,
          t /= u,
          let t' = result (norm t)
              u' = result (norm u)
              Constrained ctx' eq' = canonicalise (Constrained ctx (t' :==: u')),
          t' /= u' ]
  let cps = [ Labelled l' (CP n (size u) i (lessThan Strict u t) (Constrained ctx (t :==: u)))
            | (i, Labelled l' (Constrained ctx (t :==: u))) <- zip [0..] eqns,
              t /= u,
              let n = size t `max` size u,
              n <= fromIntegral maxN ]
  mapM_ (traceM . NewCP . peel) cps
  enqueueM l cps

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
consider l1 l2 pair@(Constrained ctx (t :==: u)) = do
  traceM (Consider pair)
  norm <- normaliser
  t <- return (result (norm t))
  u <- return (result (norm u))
  forM_ (orient (t :==: u)) $ \r@(MkOriented _ (Rule t u)) -> do
    res <- groundJoin (branches ctx) r
    case res of
      Failed -> do
        s <- get
        let r' = canonicalise (strengthenRule s r)
        traceM (NewRule r')
        l <- addRule r'
        interreduce l r'
        addCriticalPairs l r'
      Hard -> do
        s <- get
        let r' = canonicalise (strengthenRule s r)
        traceM (ExtraRule r')
        modify (\s -> s { extraRules = Index.insert r' (extraRules s) })
      Easy -> return ()

data Join = Easy | Hard | Failed

groundJoin :: (Numbered f, Numbered v, Sized f, Minimal f, Ord f, Ord v, PrettyTerm f, Pretty v) =>
  [Branch f v] -> Oriented (Rule f v) -> StateT (KBC f v) IO Join
groundJoin ctx r@(MkOriented _ (Rule t u)) = do
  rs <- gets rules
  let subsumed t u =
        or [ rhs (rule x) == u | x <- anywhere (flip Index.lookup rs) t ] ||
        or [ rhs (rule x) == t | x <- nested (anywhere (flip Index.lookup rs)) u ] ||
        or [ rhs (rule x) == t | (x, x') <- Index.lookup' u rs, not (isVariantOf (lhs (rule x')) u) ]
  if t /= u && not (subsumed t u) then do
    let (here, there) = partition (isNothing . snd) (map (solve (usort (vars t ++ vars u))) ctx)
    case here of
      [] -> do
        let pairs = usort (map canonicalise [ Constrained (And ctx') (substf (evalSubst sub) (t :==: u)) | (ctx', Just sub) <- there ])
        mapM_ (consider noLabel noLabel) pairs
        return Easy
      (model, Nothing):_ -> do
        norm <- modelNormaliser
        let Reduction t' rs1 = norm model t
            Reduction u' rs2 = norm model u
        case t' == u' of
          True -> do
            let rs = shrinkList model (\fs -> result (norm fs t) == result (norm fs u))
                nt = norm rs t
                nu = norm rs u
                rs' = strengthen rs (\fs -> valid fs nt && valid fs nu)
            traceM (Discharge r rs')
            let diag [] = Or []
                diag (r:rs) = negateFormula r ||| (weaken r &&& diag rs)
                weaken (LessEq t u) = Less t u
                weaken x = x
                ctx' = formAnd (diag rs') ctx
            res <- groundJoin ctx' r
            return $
              case res of
                Easy | length rs' > 1 -> Hard
                _ -> res
          False ->
            return Failed
  else return Easy

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

strengthenRule :: (PrettyTerm f, Minimal f, Sized f, Ord f, Ord v, Numbered f, Numbered v, Pretty v) => KBC f v -> Oriented (Rule f v) -> Oriented (Rule f v)
strengthenRule s@KBC{..} r@(MkOriented o (Rule t u)) =
  case anywhere expand1 t of
    [] -> r
    (MkOriented _ (Rule t t'):_) ->
      strengthenRule s (MkOriented o (Rule t' u))
  where
    expand1 t = map (apply t . peel . snd) (Index.lookup' t weakInverse)
    apply t (Rule u v) =
      case match u t of
        Nothing -> __
        Just sub ->
          MkOriented Oriented . Rule t $
            substf (evalSubst sub) (freshen (vars u ++ vars r) v)
    freshen vs t =
      substf (\x -> if x `elem` vars t then Var x else Var (withNumber (number x + v) x)) t
      where
        v = maximum (0:map (succ . number) vs)

addRule :: (PrettyTerm f, Minimal f, Sized f, Ord f, Ord v, Numbered f, Numbered v, Pretty v) => Oriented (Rule f v) -> StateT (KBC f v) IO Label
addRule rule = do
  l <- newLabelM
  modify (\s -> s { labelledRules = Index.insert (Labelled l rule) (labelledRules s) })
  case rule of
    MkOriented (WeaklyOriented _) (Rule t u) ->
      modify (\s -> s { weakInverse = Index.insert (Labelled l (Rule u t)) (weakInverse s) })
    _ -> return ()
  return l

deleteRule :: (Minimal f, Sized f, Ord f, Ord v, Numbered f, Numbered v) => Label -> Oriented (Rule f v) -> StateT (KBC f v) IO ()
deleteRule l rule = do
  modify $ \s ->
    s { labelledRules = Index.delete (Labelled l rule) (labelledRules s),
        queue = deleteLabel l (queue s) }
  case rule of
    MkOriented (WeaklyOriented _) (Rule t u) ->
      modify (\s -> s { weakInverse = Index.delete (Labelled l (Rule u t)) (weakInverse s) })
    _ -> return ()

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
  queueCPs l [Labelled noLabel (Constrained (And []) (unorient (rule r))) | Reorient r <- map peel reductions ]
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

  return (Constrained (And []) (left :==: right))
