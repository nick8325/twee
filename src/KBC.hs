-- Knuth-Bendix completion, up to an adjustable size limit.
-- Does constrained rewriting for unorientable equations.

{-# LANGUAGE CPP, TypeFamilies, FlexibleContexts, RecordWildCards, ScopedTypeVariables #-}
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

data Event f v =
    NewRule (Oriented (Rule f v))
  | ExtraRule (Oriented (Rule f v))
  | Reduce (Simplification f v) (Oriented (Rule f v))
  | NewCP (CP f v)
  | Consider (Constrained (Equation f v))
  | Discharge (Oriented (Rule f v)) [Formula f v]
  | NormaliseCPs Int

traceM :: (Monad m, Minimal f, PrettyTerm f, Pretty v) => Event f v -> m ()
traceM (NewRule rule) = traceIf True (hang (text "New rule") 2 (pPrint rule))
traceM (ExtraRule rule) = traceIf True (hang (text "Extra rule") 2 (pPrint rule))
traceM (Reduce red rule) = traceIf True (sep [pPrint red, nest 2 (text "using"), nest 2 (pPrint rule)])
traceM (NewCP cps) = traceIf False (hang (text "Critical pair") 2 (pPrint cps))
traceM (Consider eq) = traceIf True (sep [text "Considering", nest 2 (pPrint eq)])
traceM (Discharge eq fs) = traceIf True (sep [text "Discharge", nest 2 (pPrint eq), text "under", nest 2 (pPrint fs)])
traceM (NormaliseCPs n) = traceIf True (text "Normalise unprocessed critical pairs after generating" <+> pPrint n)

traceIf :: Monad m => Bool -> Doc -> m ()
traceIf True x = Debug.Trace.traceM (show x)
traceIf _ _ = return ()

data KBC f v =
  KBC {
    maxSize       :: Int,
    labelledRules :: Index (Labelled (Oriented (Rule f v))),
    extraRules    :: Index (Oriented (Rule f v)),
    totalCPs      :: Int,
    renormaliseAt :: Int,
    queue         :: Queue (CP f v) }
  deriving Show

report :: (Ord f, Ord v, Sized f, Minimal f) => KBC f v -> String
report KBC{..} =
  show (length rs) ++ " rules, of which " ++
  show (length (filter ((== Oriented) . orientation) rs)) ++ " oriented, " ++
  show (length (filter ((== Unoriented) . orientation) rs)) ++ " unoriented, " ++
  show (length [ r | r@(MkOriented (WeaklyOriented _) _) <- rs ]) ++ " weakly oriented. " ++
  show (length (Index.elems extraRules)) ++ " extra rules. " ++
  show (queueSize queue) ++ " queued critical pairs."
  where
    rs = map peel (Index.elems labelledRules)

data CP f v =
  CP {
    cpSize      :: Int,
    cpSizeRight :: Int,
    cpIndex     :: Int,
    oriented    :: Bool,
    cpEquation  :: Constrained (Equation f v) } deriving (Eq, Show)

instance (Minimal f, Sized f, Ord f, Ord v) => Ord (CP f v) where
  compare =
    comparing $ \(CP size size' idx oriented (Constrained _ (_ :==: _))) ->
      if oriented then (size * 2 + size', idx)
      else ((size + size') * 2, idx)

instance (Minimal f, PrettyTerm f, Pretty v) => Pretty (CP f v) where
  pPrint = pPrint . cpEquation

initialState :: Int -> KBC f v
initialState maxSize =
  KBC {
    maxSize       = maxSize,
    labelledRules = Index.empty,
    extraRules    = Index.empty,
    totalCPs      = 0,
    renormaliseAt = 100,
    queue         = empty }

enqueueM ::
  (PrettyTerm f, Minimal f, Sized f, Ord f, Ord v, Numbered v, Pretty v) =>
  Label -> [Labelled (CP f v)] -> State (KBC f v) ()
enqueueM l eqns = do
  modify $ \s -> s {
    queue    = enqueue l eqns (queue s),
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

rules :: (Ord f, Ord v) => KBC f v -> Index (Oriented (Rule f v))
rules k =
  Index.mapMonotonic peel (labelledRules k)
  `Index.union` extraRules k

normalise ::
  (PrettyTerm f, Pretty v, Minimal f, Sized f, Ord f, Ord v, Numbered f, Numbered v) =>
  KBC f v -> Tm f v -> Reduction f v
normalise s = normaliseWith (anywhere (rewrite (rules s)))

modelNormalise ::
  (PrettyTerm f, Pretty v, Minimal f, Sized f, Ord f, Ord v, Numbered f, Numbered v) =>
  KBC f v -> [Formula f v] -> Tm f v -> Reduction f v
modelNormalise s model =
  normaliseWith (anywhere (rewriteInModel (rules s) model))

newEquation ::
  (PrettyTerm f, Pretty v, Minimal f, Sized f, Ord f, Ord v, Numbered f, Numbered v) =>
  Equation f v -> State (KBC f v) ()
newEquation (t :==: u) = do
  consider noLabel noLabel (Constrained (And []) (t :==: u))
  return ()

queueCPs ::
  (PrettyTerm f, Minimal f, Sized f, Ord f, Ord v, Numbered f, Numbered v, Pretty v) =>
  Label -> [Labelled (Constrained (Equation f v))] -> State (KBC f v) ()
queueCPs l eqns = do
  s <- get
  maxN <- gets maxSize
  let eqns' =
        usort $
        [ Labelled l' (Constrained ctx' (order eq'))
        | Labelled l' (Constrained ctx (t  :==: u)) <- eqns,
          t /= u,
          let t' = result (normalise s t)
              u' = result (normalise s u)
              Constrained ctx' eq' = canonicalise (Constrained ctx (t' :==: u')),
          t' /= u' ]
  let cps = [ Labelled l' (CP n (size u) i (lessThan Strict u t) (Constrained ctx (t :==: u)))
            | (i, Labelled l' (Constrained ctx (t :==: u))) <- zip [0..] eqns',
              t /= u,
              let n = size t `max` size u,
              n <= fromIntegral maxN ]
  mapM_ (traceM . NewCP . peel) cps
  enqueueM l cps

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
    Just (l1, l2, cp) -> do
      consider l1 l2 (cpEquation cp)
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
    queueCPs l (map (fmap cpEquation) cps)
  modify (\s -> s { totalCPs = totalCPs })

consider ::
  (PrettyTerm f, Minimal f, Sized f, Ord f, Ord v, Numbered f, Numbered v, Pretty v) =>
  Label -> Label -> Constrained (Equation f v) -> State (KBC f v) ()
consider _ _ pair@(Constrained ctx (t :==: u)) = do
  traceM (Consider pair)
  s <- get
  t <- return (result (normalise s t))
  u <- return (result (normalise s u))
  forM_ (orient (t :==: u)) $ \r -> do
    res <- groundJoin (branches ctx) r
    case res of
      Failed -> do
        traceM (NewRule (canonicalise r))
        l <- addRule r
        interreduce l r
        addCriticalPairs l r
      Hard -> do
        traceM (ExtraRule (canonicalise r))
        modify (\s -> s { extraRules = Index.insert r (extraRules s) })
      Easy -> return ()

data Join = Easy | Hard | Failed

groundJoin :: (Numbered f, Numbered v, Sized f, Minimal f, Ord f, Ord v, PrettyTerm f, Pretty v) =>
  [Branch f v] -> Oriented (Rule f v) -> State (KBC f v) Join
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
        return Hard
      (_, Just _):_ -> __
      (model, Nothing):_ -> do
        s <- get
        let Reduction t' _ = modelNormalise s model t
            Reduction u' _ = modelNormalise s model u
        case t' == u' of
          True -> do
            let rs = shrinkList model (\fs -> result (modelNormalise s fs t) == result (modelNormalise s fs u))
                nt = modelNormalise s rs t
                nu = modelNormalise s rs u
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
                Easy -> Hard
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

addRule :: (PrettyTerm f, Minimal f, Sized f, Ord f, Ord v, Numbered f, Numbered v, Pretty v) => Oriented (Rule f v) -> State (KBC f v) Label
addRule rule = do
  l <- newLabelM
  modify (\s -> s { labelledRules = Index.insert (Labelled l rule) (labelledRules s) })
  return l

deleteRule :: (Minimal f, Sized f, Ord f, Ord v, Numbered f, Numbered v) => Label -> Oriented (Rule f v) -> State (KBC f v) ()
deleteRule l rule =
  modify $ \s ->
    s { labelledRules = Index.delete (Labelled l rule) (labelledRules s),
        queue = deleteLabel l (queue s) }

data Simplification f v = Simplify (Oriented (Rule f v)) | Reorient (Oriented (Rule f v)) deriving Show

instance (PrettyTerm f, Pretty v) => Pretty (Simplification f v) where
  pPrint (Simplify rule) = text "Simplify" <+> pPrint rule
  pPrint (Reorient rule) = text "Reorient" <+> pPrint rule

interreduce :: (PrettyTerm f, Ord f, Minimal f, Sized f, Ord v, Numbered f, Numbered v, Pretty v) => Label -> Oriented (Rule f v) -> State (KBC f v) ()
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

simplifyRule :: (PrettyTerm f, Pretty v, Minimal f, Sized f, Ord f, Ord v, Numbered f, Numbered v) => Label -> Oriented (Rule f v) -> State (KBC f v) ()
simplifyRule l rule@(MkOriented ctx (Rule lhs rhs)) = do
  modify $ \s ->
    s {
      labelledRules =
         Index.insert (Labelled l (MkOriented ctx (Rule lhs (result (normalise s rhs)))))
           (Index.delete (Labelled l rule) (labelledRules s)) }

addCriticalPairs :: (PrettyTerm f, Ord f, Minimal f, Sized f, Ord v, Numbered f, Numbered v, Pretty v) => Label -> Oriented (Rule f v) -> State (KBC f v) ()
addCriticalPairs l new = do
  s <- get
  rules <- gets labelledRules
  size  <- gets maxSize
  queueCPs l $
    [ Labelled l' cp
    | Labelled l' old <- Index.elems rules,
      cp <- criticalPairs s size new old ++ criticalPairs s size old new ]

criticalPairs :: (PrettyTerm f, Pretty v, Minimal f, Sized f, Ord f, Ord v, Numbered v, Numbered f) => KBC f v -> Int -> Oriented (Rule f v) -> Oriented (Rule f v) -> [Constrained (Equation f v)]
criticalPairs s _ (MkOriented _ r1) (MkOriented _ r2) = do
  cp <- CP.cps [r1] [r2]
  let f (Left x)  = withNumber (number x*2) x
      f (Right x) = withNumber (number x*2+1) x
      left = rename f (CP.left cp)
      right = rename f (CP.right cp)

      inner = rename f (fromMaybe __ (subtermAt (CP.top cp) (CP.leftPos cp)))

  guard (null (nested (anywhere (rewrite (rules s))) inner))
  return (Constrained (And []) (left :==: right))
