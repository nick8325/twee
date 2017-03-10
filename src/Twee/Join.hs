-- Tactics for joining critical pairs.
{-# LANGUAGE FlexibleContexts, BangPatterns, RecordWildCards, TypeFamilies, DeriveGeneric #-}
module Twee.Join where

import Twee.Base
import Twee.Rule
import Twee.Equation
import Twee.Proof(Proof, Derivation)
import qualified Twee.Proof as Proof
import Twee.CP
import Twee.Constraints
import qualified Twee.Index as Index
import Twee.Index(Index)
import Twee.Utils
import Data.Maybe
import Data.Either
import Data.Ord
import Data.List
import GHC.Generics

-- A critical pair together with information about how it was derived
data CriticalPair f =
  CriticalPair {
    cp_eqn   :: {-# UNPACK #-} !(Equation f),
    cp_top   :: !(Maybe (Term f)),
    cp_proof :: !(Derivation f) }
  deriving Generic

instance Symbolic (CriticalPair f) where
  type ConstantOf (CriticalPair f) = f

instance PrettyTerm f => Pretty (CriticalPair f) where
  pPrint CriticalPair{..} =
    vcat [
      pPrint cp_eqn,
      nest 2 (text "top:" <+> pPrint cp_top) ]

-- A critical pair oriented into a rewrite rule.
data CriticalRule f =
  CriticalRule {
    cr_rule  :: {-# UNPACK #-} !(Rule f),
    cr_top   :: !(Maybe (Term f)),
    cr_proof :: !(Derivation f) }

-- Turn a critical pair into a set of critical rules.
orientCP :: Function f => CriticalPair f -> [CriticalRule f]
orientCP CriticalPair{cp_eqn = l :=: r, ..}
  | l == r = []
  | otherwise =
    -- If we have something which is almost a rule, except that some
    -- variables appear only on the right-hand side, e.g.:
    --   f x y -> g x z
    -- then we replace it with the following two rules:
    --   f x y -> g x ?
    --   g x z -> g x ?
    -- where the second rule is weakly oriented and ? is the minimal
    -- constant.
    --
    -- If we have an unoriented equation with a similar problem, e.g.:
    --   f x y = g x z
    -- then we replace it with potentially three rules:
    --   f x ? = g x ?
    --   f x y -> f x ?
    --   g x z -> g x ?

    -- The main rule l -> r' or r -> l' or l' = r'
    [ CriticalRule {
        cr_rule  = makeRule l r',
        cr_top   = cp_top,
        cr_proof = erase rs cp_proof }
    | ord == Just GT ] ++
    [ CriticalRule {
        cr_rule  = makeRule r l',
        cr_top   = cp_top,
        cr_proof = Proof.symm (erase ls cp_proof) }
    | ord == Just LT ] ++
    [ CriticalRule {
        cr_rule  = makeRule l' r',
        cr_top   = cp_top,
        cr_proof = erase (ls++rs) cp_proof }
    | ord == Nothing ] ++
    [ CriticalRule {
        cr_rule  = makeRule r' l',
        cr_top   = cp_top,
        cr_proof = Proof.symm (erase (ls++rs) cp_proof) }
    | ord == Nothing ] ++

    -- Weak rules l -> l' or r -> r'
    [ CriticalRule {
        cr_rule  = makeRule l l',
        cr_top   = Just r, -- overlap of r -> l with itself
        cr_proof = cp_proof `Proof.trans` Proof.symm (erase ls cp_proof) }
    | not (null ls), ord /= Just GT ] ++
    [ CriticalRule {
        cr_rule  = makeRule r r',
        cr_top   = Just l, -- overlap of l -> r with itself
        cr_proof = Proof.symm cp_proof `Proof.trans` erase rs cp_proof }
    | not (null rs), ord /= Just LT ]
    where
      ord = orientTerms l' r'
      l' = erase ls l
      r' = erase rs r
      ls = usort (vars l) \\ usort (vars r)
      rs = usort (vars r) \\ usort (vars l)

-- Turn a critical rule back into a critical pair.
unorientCP :: CriticalRule f -> CriticalPair f
unorientCP CriticalRule{cr_rule = Rule _ l r, ..} =
  CriticalPair {
    cp_eqn = l :=: r,
    cp_top = cr_top,
    cp_proof = cr_proof }

{-# INLINEABLE makeCriticalPair #-}
makeCriticalPair ::
  (Has a (Rule f), Has a (Proof f), Has a Id) =>
  a -> a -> Overlap f -> CriticalPair f
makeCriticalPair r1 r2 overlap@Overlap{..} =
  CriticalPair overlap_eqn
    (Just overlap_top)
    (overlapProof r1 r2 overlap)

{-# INLINEABLE joinCriticalPair #-}
joinCriticalPair ::
  (Function f, Has a (Rule f), Has a (Proof f), Has a Id) =>
  Index f (Equation f) -> Index f a ->
  CriticalPair f ->
  Either
    -- Failed to join critical pair.
    -- Returns simplified critical pair and model in which it failed to hold.
    (CriticalPair f, Model f)
    -- Split critical pair into several instances.
    -- Returns list of instances which must be joined,
    -- and an optional equation which can be added to the joinable set
    -- after successfully joining all instances.
    (Maybe (CriticalPair f), [CriticalPair f])
joinCriticalPair eqns idx cp =
  {-# SCC joinCriticalPair #-}
  case allSteps eqns idx cp of
    Just cp ->
      case groundJoin eqns idx (branches (And [])) cp of
        Left model -> Left (cp, model)
        Right cps -> Right (Just cp, cps)
    Nothing ->
      Right (Nothing, [])

{-# INLINEABLE step1 #-}
{-# INLINEABLE step2 #-}
{-# INLINEABLE step3 #-}
{-# INLINEABLE allSteps #-}
step1, step2, step3, allSteps ::
  (Function f, Has a (Rule f), Has a (Proof f), Has a Id) =>
  Index f (Equation f) -> Index f a -> CriticalPair f -> Maybe (CriticalPair f)
allSteps eqns idx cp = step1 eqns idx cp >>= step2 eqns idx >>= step3 eqns idx
step1 eqns idx = joinWith eqns idx (normaliseWith (const True) (rewrite reducesOriented idx))
step2 eqns idx = joinWith eqns idx (normaliseWith (const True) (rewrite reduces idx))
step3 eqns idx cp =
  case cp_top cp of
    Just top ->
      case (join (cp, top), join (flipCP (cp, top))) of
        (Just _, Just _) -> Just cp
        _ -> Nothing
    _ -> Just cp
  where
    join (cp, top) =
      joinWith eqns idx (normaliseWith (`lessThan` top) (rewrite reducesSkolem idx)) cp

    flipCP :: Symbolic a => a -> a
    flipCP t = subst sub t
      where
        n = maximum (0:map fromEnum (vars t))
        sub (V x) = var (V (n - x))


{-# INLINEABLE joinWith #-}
joinWith ::
  (Has a (Rule f), Has a (Proof f), Has a Id) =>
  Index f (Equation f) -> Index f a -> (Term f -> Resulting f) -> CriticalPair f -> Maybe (CriticalPair f)
joinWith eqns idx reduce cp@CriticalPair{cp_eqn = lhs :=: rhs, ..}
  | subsumed eqns idx eqn = Nothing
  | otherwise =
    Just cp {
      cp_eqn = eqn,
      cp_proof =
        Proof.symm (reductionProof (reduction lred)) `Proof.trans`
        cp_proof `Proof.trans`
        reductionProof (reduction rred) }
  where
    lred = reduce lhs
    rred = reduce rhs
    eqn = result lred :=: result rred

{-# INLINEABLE subsumed #-}
subsumed ::
  (Has a (Rule f), Has a Id) =>
  Index f (Equation f) -> Index f a -> Equation f -> Bool
subsumed eqns idx (t :=: u)
  | t == u = True
  | or [ rhs rule == u | rule <- Index.lookup t idx ] = True
    -- No need to do this symmetrically because addJoinable adds
    -- both orientations of each equation
  | or [ u == subst sub u'
       | t' :=: u' <- Index.approxMatches t eqns,
         sub <- maybeToList (match t' t) ] = True
subsumed eqns idx (App f ts :=: App g us)
  | f == g =
    let
      sub Empty Empty = False
      sub (Cons t ts) (Cons u us) =
        subsumed eqns idx (t :=: u) && sub ts us
      sub _ _ = error "Function used with multiple arities"
    in
      sub ts us
subsumed _ _ _ = False

{-# INLINEABLE groundJoin #-}
groundJoin ::
  (Function f, Has a (Rule f), Has a (Proof f), Has a Id) =>
  Index f (Equation f) -> Index f a -> [Branch f] -> CriticalPair f -> Either (Model f) [CriticalPair f]
groundJoin eqns idx ctx r@CriticalPair{cp_eqn = t :=: u, ..} =
  case partitionEithers (map (solve (usort (atoms t ++ atoms u))) ctx) of
    ([], instances) ->
      let rs = [ subst sub r | sub <- instances ] in
      Right (usortBy (comparing (canonicalise . order . cp_eqn)) rs)
    (model:_, _)
      | modelOK model && isJust (allSteps eqns idx r { cp_eqn = t' :=: u' }) -> Left model
      | otherwise ->
          let model1 = optimise model weakenModel (\m -> not (modelOK m) || (valid m (reduction nt) && valid m (reduction nu)))
              model2 = optimise model1 weakenModel (\m -> not (modelOK m) || isNothing (allSteps eqns idx r { cp_eqn = result (normaliseIn m t) :=: result (normaliseIn m u) }))

              diag [] = Or []
              diag (r:rs) = negateFormula r ||| (weaken r &&& diag rs)
              weaken (LessEq t u) = Less t u
              weaken x = x
              ctx' = formAnd (diag (modelToLiterals model2)) ctx in

          groundJoin eqns idx ctx' r
      where
        normaliseIn m = normaliseWith (const True) (rewrite (reducesInModel m) idx)
        nt = normaliseIn model t
        nu = normaliseIn model u
        t' = result nt
        u' = result nu

        modelOK m =
          case cp_top of
            Nothing -> True
            Just top ->
              isNothing (lessIn m top t) && isNothing (lessIn m top u)

{-# INLINEABLE valid #-}
valid :: Function f => Model f -> Reduction f -> Bool
valid model red =
  and [ reducesInModel model rule sub
      | Step _ rule sub <- steps red ]

optimise :: a -> (a -> [a]) -> (a -> Bool) -> a
optimise x f p =
  case filter p (f x) of
    y:_ -> optimise y f p
    _   -> x
