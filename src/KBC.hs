-- Knuth-Bendix completion, with lots of exciting tricks for
-- unorientable equations.

{-# LANGUAGE CPP, TypeFamilies, FlexibleContexts, RecordWildCards, ScopedTypeVariables, UndecidableInstances, StandaloneDeriving, PatternGuards #-}
module KBC where

#include "errors.h"
import KBC.Base
import KBC.Constraints
import KBC.Rule
import qualified KBC.Index as Index
import KBC.Index(Index)
import KBC.Queue hiding (queue)
import KBC.Term
import KBC.Utils
import Control.Monad
import Data.Maybe
import Data.Ord
import qualified Data.Rewriting.Rule as T
import qualified Data.Rewriting.CriticalPair as CP
import qualified Debug.Trace
import Control.Monad.Trans.State.Strict
import Data.List
import Data.Function
import Text.Printf
import KBC.KBO

--------------------------------------------------------------------------------
-- Completion engine state.
--------------------------------------------------------------------------------

data KBC f =
  KBC {
    maxSize           :: Int,
    labelledRules     :: Index (Labelled (Modelled (Critical (Rule f)))),
    extraRules        :: Index (Rule f),
    subRules          :: Index (Tm f, Rule f),
    goals             :: [Tm f],
    totalCPs          :: Int,
    renormaliseAt     :: Int,
    queue             :: !(Queue (Passive f)),
    useInversionRules :: Bool,
    useSkolemPenalty  :: Bool }
  deriving Show

initialState :: Int -> [Tm f] -> KBC f
initialState maxSize goals =
  KBC {
    maxSize           = maxSize,
    labelledRules     = Index.empty,
    extraRules        = Index.empty,
    subRules          = Index.empty,
    goals             = goals,
    totalCPs          = 0,
    renormaliseAt     = 1000,
    queue             = empty,
    useInversionRules = False,
    useSkolemPenalty  = True }

report :: (Function f, Sized f) => KBC f -> String
report KBC{..} =
  printf "Rules: %d total, %d oriented, %d unoriented, %d permutative, %d weakly oriented. "
    (length rs)
    (length (filter ((== Oriented) . orientation) rs))
    (length (filter ((== Unoriented) . orientation) rs))
    (length [ r | r@(Rule (Permutative _) _ _) <- rs ])
    (length [ r | r@(Rule (WeaklyOriented _) _ _) <- rs ]) ++
  printf "%d extra. %d historical.\n"
    (length (Index.elems extraRules))
    n ++
  printf "Critical pairs: %d total, %d processed, %d queued compressed into %d."
    totalCPs
    (totalCPs - s)
    s
    (length (toList queue))
  where
    rs = map (critical . modelled . peel) (Index.elems labelledRules)
    Label n = nextLabel queue
    s = sum (map passiveCount (toList queue))

enqueueM :: (Function f, Sized f) => Passive f -> State (KBC f) ()
enqueueM cps = do
  traceM (NewCP cps)
  modify' $ \s -> s {
    queue    = enqueue cps (queue s),
    totalCPs = totalCPs s + passiveCount cps }

dequeueM :: (Function f, Sized f) => State (KBC f) (Maybe (Passive f))
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
    model    :: [Formula (ConstantOf a)],
    modelled :: a }

instance Eq a => Eq (Modelled a) where x == y = modelled x == modelled y
instance Ord a => Ord (Modelled a) where compare = comparing modelled

instance (PrettyTerm (ConstantOf a), Pretty a) => Pretty (Modelled a) where
  pPrint Modelled{..} = pPrint modelled

deriving instance (Show a, Show (ConstantOf a)) => Show (Modelled a)

instance Symbolic a => Symbolic (Modelled a) where
  type ConstantOf (Modelled a) = ConstantOf a

  termsDL Modelled{..} = termsDL modelled
  substf sub Modelled{..} = Modelled model (substf sub modelled)

--------------------------------------------------------------------------------
-- Rewriting.
--------------------------------------------------------------------------------

rules :: Ord f => KBC f -> Index (Rule f)
rules k =
  Index.mapMonotonic (critical . modelled . peel) (labelledRules k)
  `Index.union` extraRules k

normaliseQuickly :: (Function f, Sized f) => KBC f -> Tm f -> Reduction f
normaliseQuickly s = normaliseWith (rewrite simplifies (rules s))

normalise :: (Function f, Sized f) => KBC f -> Tm f -> Reduction f
normalise s = normaliseWith (rewrite reduces (rules s))

normaliseIn :: (Function f, Sized f) => KBC f -> [Formula f] -> Tm f -> Reduction f
normaliseIn s model =
  normaliseWith (rewrite (reducesInModel model) (rules s))

normaliseSub :: (Function f, Sized f) => KBC f -> Tm f -> Tm f -> Reduction f
normaliseSub s top t
  | lessEq t top && isNothing (unify t top) =
    normaliseWith (rewrite (reducesSub top) (rules s)) t
  | otherwise = Reduction t Refl

reduceCP ::
  (Function f, Sized f) =>
  KBC f -> (Tm f -> Tm f) ->
  Critical (Equation f) -> Maybe (Critical (Equation f))
reduceCP s f (Critical top (t :=: u))
  | t' == u' = Nothing
  | subsumed s True t' u' = Nothing
  | otherwise = Just (Critical top (t' :=: u'))
  where
    t' = f t
    u' = f u

    subsumed s root t u =
      or [ rhs x == u | x <- Index.lookup t rs ] ||
      or [ subst sub (rhs x) == t | (x, sub) <- Index.matches u rs, not root || not (isVariantOf (lhs x) u) ] ||
      case focus t u of
        Nothing -> False
        Just (t', u') -> subsumed s False t' u'
      where
        rs = rules s

    focus (Fun f ts) (Fun g us) | f == g = aux ts us
      where
        aux [] [] = Nothing
        aux (t:ts) (u:us)
          | t == u = aux ts us
          | ts == us = Just (t, u)
          | otherwise = Nothing
    focus _ _ = Nothing

normaliseCPQuickly, normaliseCP ::
  (Function f, Sized f) =>
  KBC f -> Critical (Equation f) -> Maybe (Critical (Equation f))
normaliseCPQuickly s cp =
  reduceCP s id cp >>=
  reduceCP s (result . normaliseQuickly s)

normaliseCP s cp@(Critical info _) =
  normaliseCPQuickly s cp >>=
  reduceCP s (result . normalise s) >>=
  reduceCP s (result . normaliseSub s (top info))

--------------------------------------------------------------------------------
-- Completion loop.
--------------------------------------------------------------------------------

complete :: (Function f, Sized f) => State (KBC f) ()
complete = do
  res <- complete1
  when res complete

complete1 :: (Function f, Sized f) => State (KBC f) Bool
complete1 = do
  KBC{..} <- get
  when (totalCPs >= renormaliseAt) $ do
    normaliseCPs
    modify (\s -> s { renormaliseAt = renormaliseAt * 3 })

  res <- dequeueM
  case res of
    Just (SingleCP (CP _ cp _ _)) -> do
      consider cp
      modify $ \s -> s { goals = map (result . normalise s) goals }
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

normaliseCPs :: forall f v. (Function f, Sized f) => State (KBC f) ()
normaliseCPs = do
  s@KBC{..} <- get
  traceM (NormaliseCPs s)
  put s { queue = emptyFrom queue }
  forM_ (toList queue) $ \cp ->
    case cp of
      SingleCP (CP _ cp l1 l2) -> queueCP l1 l2 cp
      ManyCPs (CPs _ _ lower upper _ rule) -> queueCPs lower upper rule
  modify (\s -> s { totalCPs = totalCPs })

consider ::
  (Function f, Sized f) =>
  Critical (Equation f) -> State (KBC f) ()
consider pair = do
  traceM (Consider pair)
  s <- get
  case normaliseCP s pair of
    Nothing -> return ()
    Just (Critical info eq) ->
      forM_ (orient eq) $ \r@(Rule _ t u) -> do
        s <- get
        case normaliseCP s (Critical info (t :=: u)) of
          Nothing -> return ()
          Just eq ->
            case groundJoin s (branches (And [])) eq of
              Right eqs -> do
                mapM_ consider eqs
                traceM (ExtraRule (canonicalise r))
                modify (\s -> s { extraRules = Index.insert r (extraRules s) })
                newSubRule r
              Left model -> do
                traceM (NewRule (canonicalise r))
                l <- addRule (Modelled model (Critical info r))
                queueCPsSplit noLabel l (Labelled l r)
                interreduce r

groundJoin :: (Function f, Sized f) =>
  KBC f -> [Branch f] -> Critical (Equation f) -> Either [Formula f] [Critical (Equation f)]
groundJoin s ctx r@(Critical info (t :=: u)) =
  case partition (isNothing . snd) (map (solve (usort (vars t ++ vars u))) ctx) of
    ([], instances) ->
      let rs = [ substf (evalSubst sub) r | (_, Just sub) <- instances ] in
      Right (usort (map canonicalise rs))
    ((model, Nothing):_, _)
      | isJust (normaliseCP s (Critical info (t' :=: u'))) -> Left model
      | otherwise ->
          let rs = shrinkList model (\fs -> isNothing (normaliseCP s (Critical info (result (normaliseIn s fs t) :=: result (normaliseIn s fs u)))))
              nt = normaliseIn s rs t
              nu = normaliseIn s rs u
              rs' = strengthen rs (\fs -> valid fs nt && valid fs nu)

              diag [] = Or []
              diag (r:rs) = negateFormula r ||| (weaken r &&& diag rs)
              weaken (LessEq t u) = Less t u
              weaken x = x
              ctx' = formAnd (diag rs') ctx in

          trace (Discharge r rs') $
          groundJoin s ctx' r
      where
        Reduction t' _ = normaliseIn s model t
        Reduction u' _ = normaliseIn s model u
    _ -> __

valid :: (Function f, Sized f) => [Formula f] -> Reduction f -> Bool
valid model red = all valid1 (steps red)
  where
    valid1 rule = reducesInModel model rule

shrinkList :: [a] -> ([a] -> Bool) -> [a]
shrinkList [] _ = []
shrinkList (x:xs) p
  | p xs = shrinkList xs p
  | otherwise = x:shrinkList xs (\ys -> p (x:ys))

strengthen :: [Formula f] -> ([Formula f] -> Bool) -> [Formula f]
strengthen [] _ = []
strengthen (Less t u:xs) p
  | p (LessEq t u:xs) = strengthen (LessEq t u:xs) p
  | otherwise = Less t u:strengthen xs (\ys -> p (Less t u:ys))
strengthen (x:xs) p = x:strengthen xs (\ys -> p (x:ys))

newSubRule :: (Function f, Sized f) => Rule f -> State (KBC f) ()
newSubRule r@(Rule _ t u) = do
  s <- get
  when (useInversionRules s) $
    put s { subRules = foldr ins (subRules s) (properSubterms t) }
  where
    ins v idx
      | isFun v && not (lessEq v u) && usort (vars u) `isSubsequenceOf` usort (vars v) = Index.insert (v, r) idx
      | otherwise = idx

addRule :: (Function f, Sized f) => Modelled (Critical (Rule f)) -> State (KBC f) Label
addRule rule = do
  l <- newLabelM
  modify (\s -> s { labelledRules = Index.insert (Labelled l rule) (labelledRules s) })
  newSubRule (critical (modelled rule))
  return l

deleteRule :: (Function f, Sized f) => Label -> Modelled (Critical (Rule f)) -> State (KBC f) ()
deleteRule l rule =
  modify $ \s ->
    s { labelledRules = Index.delete (Labelled l rule) (labelledRules s),
        queue = deleteLabel l (queue s) }

data Simplification f = Simplify [Formula f] (Modelled (Critical (Rule f))) | Reorient (Modelled (Critical (Rule f))) deriving Show

instance PrettyTerm f => Pretty (Simplification f) where
  pPrint (Simplify _ rule) = text "Simplify" <+> pPrint rule
  pPrint (Reorient rule) = text "Reorient" <+> pPrint rule

interreduce :: (Function f, Sized f) => Rule f -> State (KBC f) ()
interreduce new = do
  rules <- gets (Index.elems . labelledRules)
  forM_ rules $ \(Labelled l old) -> do
    s <- get
    case reduceWith s l new old of
      Nothing -> return ()
      Just red -> do
        traceM (Reduce red new)
        case red of
          Simplify model rule -> simplifyRule l model rule
          Reorient rule@(Modelled _ (Critical info (Rule _ t u))) -> do
            deleteRule l rule
            queueCP noLabel noLabel (Critical info (t :=: u))

reduceWith :: (Function f, Sized f) => KBC f -> Label -> Rule f -> Modelled (Critical (Rule f)) -> Maybe (Simplification f)
reduceWith s lab new old0@(Modelled model (Critical info old@(Rule _ l r)))
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
    s' = s { labelledRules = Index.delete (Labelled lab old0) (labelledRules s) }
    modelJoinable = isNothing (normaliseCP s' (Critical info (lm :=: rm)))
    lm = result (normaliseIn s' model l)
    rm = result (normaliseIn s' model r)
    tryGroundJoin =
      case groundJoin s' (branches (And [])) (Critical info (l :=: r)) of
        Left model' ->
          Just (Simplify model' old0)
        Right _ ->
          Just (Reorient old0)

simplifyRule :: (Function f, Sized f) => Label -> [Formula f] -> Modelled (Critical (Rule f)) -> State (KBC f) ()
simplifyRule l model rule@(Modelled _ (Critical info (Rule ctx lhs rhs))) = do
  modify $ \s ->
    s {
      labelledRules =
         Index.insert (Labelled l (Modelled model (Critical info (Rule ctx lhs (result (normalise s rhs))))))
           (Index.delete (Labelled l rule) (labelledRules s)) }
  newSubRule (Rule ctx lhs rhs)

newEquation :: (Function f, Sized f) => Equation f -> State (KBC f) ()
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
    top      :: Tm f,
    overlap  :: Int }

instance Eq a => Eq (Critical a) where x == y = critical x == critical y
instance Ord a => Ord (Critical a) where compare = comparing critical

instance (PrettyTerm (ConstantOf a), Pretty a) => Pretty (Critical a) where
  pPrint Critical{..} = pPrint critical

deriving instance (Show a, Show (ConstantOf a)) => Show (Critical a)
deriving instance Show f => Show (CritInfo f)

instance Symbolic a => Symbolic (Critical a) where
  type ConstantOf (Critical a) = ConstantOf a

  termsDL Critical{..} = termsDL critical `mplus` termsDL critInfo
  substf sub Critical{..} = Critical (substf sub critInfo) (substf sub critical)

instance Symbolic (CritInfo f) where
  type ConstantOf (CritInfo f) = f

  termsDL CritInfo{..} = termsDL top
  substf sub CritInfo{..} = CritInfo (substf sub top) overlap

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
    cpId :: (Tm f, Label),
    cpOK :: Bool,
    cpCP :: Labelled (Critical (Equation f)) }

filterCPs :: (Function f, Sized f) => [InitialCP f] -> [Labelled [Critical (Equation f)]]
filterCPs =
  map pick . filter (cpOK . head) . groupBy ((==) `on` cpId) . sortBy (comparing cpId)
  where
    pick xs@(x:_) = Labelled (labelOf (cpCP x)) (map (peel . cpCP) xs)

criticalPairs :: (Function f, Sized f) => KBC f -> Label -> Label -> Rule f -> [InitialCP f]
criticalPairs s lower upper rule =
  criticalPairs1 s (maxSize s) rule (Index.mapMonotonic (fmap (critical . modelled)) rules) ++
  [ cp
  | Labelled l' (Modelled _ (Critical _ old)) <- Index.elems rules,
    cp <- criticalPairs1 s (maxSize s) old (Index.singleton (Labelled l' rule)) ]
  where
    rules = Index.filter (p . labelOf) (labelledRules s)
    p l = lower <= l && l <= upper

criticalPairs1 :: (Function f, Sized f) => KBC f -> Int -> Rule f -> Index (Labelled (Rule f)) -> [InitialCP f]
criticalPairs1 s n (Rule or1 t u) idx = do
  Labelled l (Rule or2 t' u') <- Index.elems idx
  let r1 = T.Rule t u
      r2 = T.Rule t' u'
  cp <- CP.cps [r2] [r1]
  let f (Left x)  = withNumber (number x*2) x
      f (Right x) = withNumber (number x*2+1) x
      left = rename f (CP.left cp)
      right = rename f (CP.right cp)
      top = rename f (CP.top cp)

      inner = fromMaybe __ (subtermAt top (CP.leftPos cp))
      overlap = fromMaybe __ (subtermAt t (CP.leftPos cp))
      osz = size overlap + (size u - size t) + (size u' - size t')
      sz = size top

  guard (left /= top && right /= top)
  when (or1 == Unoriented) $ guard (not (lessEq top right))
  when (or2 == Unoriented) $ guard (not (lessEq top left))
  guard (size top <= n)
  return $
    InitialCP
      (canonicalise (fromMaybe __ (subtermAt t (CP.leftPos cp))), l)
      (null (nested (anywhere (rewrite reduces (rules s))) inner))
      (Labelled l (Critical (CritInfo top osz) (left :=: right)))

queueCP ::
  (Function f, Sized f) =>
  Label -> Label -> Critical (Equation f) -> State (KBC f) ()
queueCP l1 l2 eq = do
  s <- get
  case toCP s l1 l2 eq of
    Nothing -> return ()
    Just cp -> enqueueM (SingleCP cp)

queueCPs ::
  (Function f, Sized f) =>
  Label -> Label -> Labelled (Rule f) -> State (KBC f) ()
queueCPs lower upper rule = do
  s <- get
  let xs = toCPs s lower upper rule
  if length xs <= 20 then
    mapM_ (enqueueM . SingleCP) xs
  else
    let best = minimum xs in
    enqueueM (ManyCPs (CPs (info best) (l2 best) lower upper (length xs) rule))

queueCPsSplit ::
  (Function f, Sized f) =>
  Label -> Label -> Labelled (Rule f) -> State (KBC f) ()
queueCPsSplit l u rule = do
  queueCPs l (l + diff `div` k) rule
  forM_ [1..k-2] $ \i ->
    queueCPs (l + i*diff `div` k + 1) (l + (i+1)*diff `div` k) rule
  queueCPs (l + (k-1)*diff `div` k) u rule
  where
    k = 5
    diff = u-l

toCPs ::
  (Function f, Sized f) =>
  KBC f -> Label -> Label -> Labelled (Rule f) -> [CP f]
toCPs s lower upper (Labelled l rule) =
  usortBy (comparing (critical . cp)) . map minimum . filter (not . null) $
    [ catMaybes (map (toCP s l l') eqns) | Labelled l' eqns <- cps0 ]
  where
    cps0 = filterCPs (criticalPairs s lower upper rule)

toCP ::
  (Function f, Sized f) =>
  KBC f -> Label -> Label -> Critical (Equation f) -> Maybe (CP f)
toCP s l1 l2 cp = fmap toCP' (norm cp)
  where
    norm (Critical info (t :=: u)) = do
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
        (_, r1) <- Index.lookup t (subRules s)
        r2 <- Index.lookup (replace t u (rhs r1)) (rules s)

        guard (reducesSub top r1 && reducesSub top r2)
        let t' = rhs r1
            u' = rhs r2
        guard (subsumes True (t', u') (t, u))
        return (t', u')

    replace t u v | v == t = u
    replace t u (Fun f ts) = Fun f (map (replace t u) ts)
    replace _ _ t = t

    subsumes strict (t', u') (t, u) =
      (isJust (matchMany minimal [(t', t), (u', u)]) &&
       (not strict || isNothing (matchMany minimal [(t, t'), (u, u')]))) ||
      case focus t u of
        Just (t'', u'') -> subsumes False (t', u') (t'', u'')
        _ -> False
      where
        focus (Fun f ts) (Fun g us) | f == g = aux ts us
          where
            aux [] [] = Nothing
            aux (t:ts) (u:us)
              | t == u = aux ts us
              | ts == us = Just (t, u)
              | otherwise = Nothing
        focus _ _ = Nothing

    toCP' (Critical info (t :=: u)) =
      CP (CPInfo (weight t' u') (-(overlap info)) l2 l1) (Critical info' (t' :=: u')) l1 l2
      where
        Critical info' (t' :=: u') = canonicalise (Critical info (order (t :=: u)))

    weight t u
      | u `lessEq` t = f t u + penalty t u
      | otherwise    = (f t u `max` f u t) + penalty t u
      where
        f t u = size t + size u + length (vars u \\ vars t) + length (usort (vars t) \\ vars u)

    penalty t u
      | useSkolemPenalty s &&
        result (normalise s (skolemise t)) == result (normalise s (skolemise u)) =
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
  | Discharge (Critical (Equation f)) [Formula f]
  | NormaliseCPs (KBC f)

trace :: (Function f, Sized f) => Event f -> a -> a
trace (NewRule rule) = traceIf True (hang (text "New rule") 2 (pPrint rule))
trace (ExtraRule rule) = traceIf True (hang (text "Extra rule") 2 (pPrint rule))
trace (NewCP cp) = traceIf False (hang (text "Critical pair") 2 (pPrint cp))
trace (Reduce red rule) = traceIf True (sep [pPrint red, nest 2 (text "using"), nest 2 (pPrint rule)])
trace (Consider eq) = traceIf False (sep [text "Considering", nest 2 (pPrint eq)])
trace (Discharge eq fs) = traceIf True (sep [text "Discharge", nest 2 (pPrint eq), text "under", nest 2 (pPrint fs)])
trace (NormaliseCPs s) = traceIf True (text "" $$ text "Normalising unprocessed critical pairs." $$ text (report s) $$ text "")

traceM :: (Monad m, Function f, Sized f) => Event f -> m ()
traceM x = trace x (return ())

traceIf :: Bool -> Doc -> a -> a
traceIf True x = Debug.Trace.trace (show x)
traceIf False _ = id
