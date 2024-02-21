-- | Term rewriting.
{-# LANGUAGE TypeFamilies, FlexibleContexts, RecordWildCards, BangPatterns, OverloadedStrings, MultiParamTypeClasses, ScopedTypeVariables, GeneralizedNewtypeDeriving #-}
module Twee.Rule where

import Twee.Base
import Twee.Constraints hiding (funs)
import qualified Twee.Index as Index
import Twee.Index(Index)
import Control.Monad
import Control.Monad.Trans.Class
import Control.Monad.Trans.State.Strict
import Data.Maybe
import Data.List hiding (singleton)
import Twee.Utils
import qualified Data.Map.Strict as Map
import Data.Map(Map)
import qualified Twee.Term as Term
import Data.Ord
import Twee.Equation
import qualified Twee.Proof as Proof
import Twee.Proof(Derivation, Proof)
import Data.Tuple
import Twee.Profile
import Data.MemoUgly
import Debug.Trace
import Twee.Pretty
import Data.Function
import Control.Arrow((***))
import GHC.Stack
import Test.QuickCheck hiding (Function, subterms, Fun)
import Twee.Profile
import Test.QuickCheck.Gen

--------------------------------------------------------------------------------
-- * Rewrite rules.
--------------------------------------------------------------------------------

-- | A rewrite rule.
data Rule f =
  Rule {
    -- | Information about whether and how the rule is oriented.
    orientation :: Orientation f,
    -- Invariant:
    -- For oriented rules: vars rhs `isSubsetOf` vars lhs
    -- For unoriented rules: vars lhs == vars rhs
    
    -- | A proof that the rule holds.
    rule_proof :: !(Proof f),

    -- | The left-hand side of the rule.
    lhs :: {-# UNPACK #-} !(Term f),
    -- | The right-hand side of the rule.
    rhs :: {-# UNPACK #-} !(Term f) }
  deriving Show
instance Eq (Rule f) where
  x == y = compare x y == EQ
instance Ord (Rule f) where
  compare = comparing (\rule -> (lhs rule, rhs rule))
instance f ~ g => Has (Rule f) (Rule g) where
  the = id
type RuleOf a = Rule (ConstantOf a)

ruleDerivation :: Rule f -> Derivation f
ruleDerivation r =
  case (matchEquation (Proof.equation (rule_proof r)) (lhs r :=: rhs r),
        matchEquation (Proof.equation (rule_proof r)) (rhs r :=: lhs r)) of
    (Just sub, _) -> Proof.lemma (rule_proof r) sub
    (_, Just sub) -> Proof.symm (Proof.lemma (rule_proof r) sub)
    _ -> error "rule out of sync with proof"

-- | A rule's orientation.
--
-- 'Oriented' and 'WeaklyOriented' rules are used only left-to-right.
-- 'Permutative' and 'Unoriented' rules are used bidirectionally.
data Orientation f =
    -- | An oriented rule.
    Oriented
    -- | A weakly oriented rule.
    -- The first argument is the minimal constant, the second argument is a list
    -- of terms which are weakly oriented in the rule.
    -- 
    -- A rule with orientation @'WeaklyOriented' k ts@ can be used unless
    -- all terms in @ts@ are equal to @k@.
  | WeaklyOriented {-# UNPACK #-} !(Fun f) [Term f]
    -- | A permutative rule.
    --
    -- A rule with orientation @'Permutative' ts@ can be used if
    -- @map fst ts@ is lexicographically greater than @map snd ts@.
  | Permutative [(Term f, Term f)]
    -- | An unoriented rule.
  | Unoriented
  deriving Show

instance Eq (Orientation f) where _ == _ = True
instance Ord (Orientation f) where compare _ _ = EQ

-- | Is a rule oriented or weakly oriented?
oriented :: Orientation f -> Bool
oriented Oriented{} = True
oriented WeaklyOriented{} = True
oriented _ = False

instance Symbolic (Rule f) where
  type ConstantOf (Rule f) = f
  termsDL (Rule _ _ t _) = termsDL t
  subst_ sub (Rule or pf t u) = Rule (subst_ sub or) pf (subst_ sub t) (subst_ sub u)

instance f ~ g => Has (Rule f) (Term g) where
  the = lhs

instance Symbolic (Orientation f) where
  type ConstantOf (Orientation f) = f

  termsDL Oriented = mzero
  termsDL (WeaklyOriented _ ts) = termsDL ts
  termsDL (Permutative ts) = termsDL ts
  termsDL Unoriented = mzero

  subst_ _   Oriented = Oriented
  subst_ sub (WeaklyOriented min ts) = WeaklyOriented min (subst_ sub ts)
  subst_ sub (Permutative ts) = Permutative (subst_ sub ts)
  subst_ _   Unoriented = Unoriented

instance (Labelled f, PrettyTerm f) => Pretty (Rule f) where
  pPrint (Rule or _ l r) =
    pPrint l <+> text (showOrientation or) <+> pPrint r
    where
      showOrientation Oriented = "->"
      showOrientation WeaklyOriented{} = "~>"
      showOrientation Permutative{} = "<->"
      showOrientation Unoriented = "="

-- | Turn a rule into an equation.
unorient :: Rule f -> Equation f
unorient (Rule _ _ l r) = l :=: r

-- | Turn an equation t :=: u into a rule t -> u by computing the
-- orientation info (e.g. oriented, permutative or unoriented).
--
-- Crashes if either @t < u@, or there is a variable in @u@ which is
-- not in @t@. To avoid this problem, combine with 'Twee.CP.split'.
orient :: Function f => Equation f -> Proof f -> Rule f
orient (t :=: u) pf = Rule o pf t u
  where
    o | lessEq u t =
        case unify t u of
          Nothing -> Oriented
          Just sub
            | allSubst (\_ (Cons t Empty) -> isMinimal t) sub ->
              WeaklyOriented minimal (map (build . var . fst) (substToList sub))
            | otherwise -> Unoriented
      | lessEq t u = error "wrongly-oriented rule"
      | not (null (usort (vars u) \\ usort (vars t))) =
        error "unbound variables in rule"
      | Just ts <- evalStateT (makePermutative t u) [],
        permutativeOK t u ts =
        Permutative ts
      | otherwise = Unoriented

    permutativeOK _ _ [] = True
    permutativeOK t u ((Var x, Var y):xs) =
      lessIn model u t == Just Strict &&
      permutativeOK t' u' xs
      where
        model = modelFromOrder [Variable y, Variable x]
        sub x' = if x == x' then var y else var x'
        t' = subst sub t
        u' = subst sub u

    makePermutative t u = do
      msub <- gets listToSubst
      sub  <- lift msub
      aux (subst sub t) (subst sub u)
        where
          aux (Var x) (Var y)
            | x == y = return []
            | otherwise = do
              modify ((x, build $ var y):)
              return [(build $ var x, build $ var y)]

          aux (App f ts) (App g us)
            | f == g =
              fmap concat (zipWithM makePermutative (unpack ts) (unpack us))

          aux _ _ = mzero

-- | Flip an unoriented rule so that it goes right-to-left.
backwards :: Rule f -> Rule f
backwards (Rule or pf t u) = Rule (back or) pf u t
  where
    back (Permutative xs) = Permutative (map swap xs)
    back Unoriented = Unoriented
    back _ = error "Can't turn oriented rule backwards"

--------------------------------------------------------------------------------
-- * Extra-fast rewriting, without proof output or unorientable rules.
--------------------------------------------------------------------------------

-- | Compute the normal form of a term wrt only oriented rules.
{-# INLINEABLE simplify #-}
simplify :: (Function f, Has a (Rule f)) => Index f a -> Term f -> Term f
simplify idx t = stamp "simplify" (simplifyOutermost idx t)

-- | Compute the normal form of a term wrt only oriented rules, using outermost reduction.
simplifyOutermost :: (Function f, Has a (Rule f)) => Index f a -> Term f -> Term f
simplifyOutermost !idx !t
  | t == u = t
  | otherwise = simplifyOutermost idx u
  where
    u = build (simp (singleton t))

    simp Empty = mempty
    simp (Cons (Var x) t) = var x `mappend` simp t
    simp (Cons t u)
      | Just (rule, sub) <- simpleRewrite idx t =
        Term.subst sub (rhs rule) `mappend` simp u
    simp (Cons (App f ts) us) =
      app f (simp ts) `mappend` simp us

-- | Compute the normal form of a term wrt only oriented rules, using innermost reduction.
simplifyInnermost :: (Function f, Has a (Rule f)) => Index f a -> Term f -> Term f
simplifyInnermost !idx !t = simp t
  where
    simp t =
      case [rw | u <- reverseSubterms t, Just rw <- [simpleRewrite idx u]] of
        [] -> t
        (rule, sub):_ ->
          let l = build (Term.subst sub (lhs rule))
              r = build (Term.subst sub (rhs rule))
          in simp (build (replace l r (singleton t)))

-- | Find a simplification step that applies to a term.
{-# INLINEABLE simpleRewrite #-}
simpleRewrite :: (Function f, Has a (Rule f)) => Index f a -> Term f -> Maybe (Rule f, Subst f)
simpleRewrite idx t =
  -- Use instead of maybeToList to make fusion work
  foldr (\x _ -> Just x) Nothing $ do
    (sub, rule0) <- Index.matches t idx
    let rule = the rule0
    guard (oriented (orientation rule))
    guard (reducesOriented rule sub)
    return (rule, sub)

--------------------------------------------------------------------------------
-- * Rewriting, with proof output.
--------------------------------------------------------------------------------

-- | A strategy gives a set of possible reductions for a term.
type Strategy f = Term f -> [Reduction f]

-- | A reduction proof is just a sequence of rewrite steps. In each
-- rewrite step, all subterms that are exactly equal to the LHS of the
-- rule are replaced by the RHS, i.e. the rewrite step is performed as
-- a parallel rewrite without matching.
type Reduction f = [(Rule f, Subst f)]

-- | Transitivity for reduction sequences.
trans :: Reduction f -> Reduction f -> Reduction f
trans p q = p ++ q

-- | Compute the final term resulting from a reduction, given the
-- starting term.
result :: Term f -> Reduction f -> Term f
result t [] = t
result t (r:rs) = result u rs
  where
    !u = ruleResult t r

-- | Turn a reduction into a proof.
reductionProof :: Function f => Term f -> Reduction f -> Derivation f
reductionProof t ps = red t (Proof.Refl t) ps
  where
    red _ p [] = p
    red t p (q:qs) =
      red (ruleResult t q) (p `Proof.trans` ruleProof t q) qs

-- Helpers for result and reductionProof.
ruleResult :: Term f -> (Rule f, Subst f) -> Term f
ruleResult t (r0, sub) = build (replace (lhs r) (rhs r) (singleton t))
  where
    r = subst sub r0

ruleProof :: Function f => Term f -> (Rule f, Subst f) -> Derivation f
ruleProof t (r0, sub)
  | t == lhs r = ruleDerivation r
  | len t < len (lhs r) = Proof.Refl t
  where
    r = subst sub r0
ruleProof (App f ts) rule =
  Proof.cong f [ruleProof u rule | u <- unpack ts]
ruleProof t _ = Proof.Refl t

--------------------------------------------------------------------------------
-- * Normalisation.
--------------------------------------------------------------------------------

-- | Normalise a term wrt a particular strategy.
{-# INLINE normaliseWith #-}
normaliseWith :: Function f => (Term f -> Bool) -> Strategy f -> Term f -> Reduction f
normaliseWith ok strat t = aux t
  where
    aux t =
      case anywhere strat t of
        (p:_) | u <- result t p, ok u -> p `trans` aux u
        _ -> []

-- | Compute all normal forms of a set of terms wrt a particular strategy.
normalForms :: Function f => Strategy f -> Map (Term f) (Reduction f) -> Map (Term f) (Term f, Reduction f)
normalForms strat ps = snd (successorsAndNormalForms strat ps)

-- | Compute all successors of a set of terms (a successor of a term @t@
-- is a term @u@ such that @t ->* u@).
successors :: Function f => Strategy f -> Map (Term f) (Reduction f) -> Map (Term f) (Term f, Reduction f)
successors strat ps =
  Map.union qs rs
  where
    (qs, rs) = successorsAndNormalForms strat ps

{-# INLINEABLE successorsAndNormalForms #-}
successorsAndNormalForms :: Function f => Strategy f -> Map (Term f) (Reduction f) ->
  (Map (Term f) (Term f, Reduction f), Map (Term f) (Term f, Reduction f))
successorsAndNormalForms strat ps =
  go Map.empty Map.empty (Map.mapWithKey (\t red -> (t, red)) ps)
  where
    go dead norm ps =
      case Map.minViewWithKey ps of
        Nothing -> (dead, norm)
        Just ((t, p), ps)
          | t `Map.member` dead -> go dead norm ps
          | t `Map.member` norm -> go dead norm ps
          | null qs -> go dead (Map.insert t p norm) ps
          | otherwise ->
            go (Map.insert t p dead) norm (Map.fromList qs `Map.union` ps)
          where
            qs =
              [ (result t q, (fst p, (snd p `trans` q)))
              | q <- anywhere strat t ]

-- | Apply a strategy anywhere in a term.
anywhere :: Strategy f -> Strategy f
anywhere = anywhereOutermost

-- | Apply a strategy anywhere in a term, preferring outermost reductions.
anywhereOutermost :: Strategy f -> Strategy f
anywhereOutermost strat t = concatMap strat (subterms t)

-- | Apply a strategy anywhere in a term, preferring innermost reductions.
anywhereInnermost :: Strategy f -> Strategy f
anywhereInnermost strat t = concatMap strat (reverseSubterms t)

--------------------------------------------------------------------------------
-- * Basic strategies. These only apply at the root of the term.
--------------------------------------------------------------------------------

-- | A strategy which rewrites using an index.
{-# INLINE rewrite #-}
rewrite :: (Function f, Has a (Rule f)) => (Rule f -> Subst f -> Bool) -> Index f a -> Strategy f
rewrite p rules t = do
  (sub, rule) <- Index.matches t rules
  guard (p (the rule) sub)
  return [(the rule, sub)]

-- | A strategy which applies one rule only.
{-# INLINEABLE tryRule #-}
tryRule :: (Function f, Has a (Rule f)) => (Rule f -> Subst f -> Bool) -> a -> Strategy f
tryRule p rule t = do
  sub <- maybeToList (match (lhs (the rule)) t)
  guard (p (the rule) sub)
  return [(the rule, sub)]

-- | Check if a rule can be applied, given an ordering <= on terms.
{-# INLINEABLE reducesWith #-}
reducesWith :: Function f => (Term f -> Term f -> Bool) -> Rule f -> Subst f -> Bool
reducesWith _ (Rule Oriented _ _ _) _ = True
reducesWith _ (Rule (WeaklyOriented min ts) _ _ _) sub =
  -- Be a bit careful here not to build new terms
  -- (reducesWith is used in simplify).
  -- This is the same as:
  --   any (not . isMinimal) (subst sub ts)
  any (not . isMinimal . expand) ts
  where
    expand t@(Var x) = fromMaybe t (Term.lookup x sub)
    expand t = t

    isMinimal (App f Empty) = f == min
    isMinimal _ = False
reducesWith p (Rule (Permutative ts) _ _ _) sub =
  aux ts
  where
    aux [] = False
    aux ((t, u):ts)
      | t' == u' = aux ts
      | otherwise = p u' t'
      where
        t' = subst sub t
        u' = subst sub u
reducesWith p (Rule Unoriented _ t u) sub =
  t' /= u' && p u' t'
  where
    t' = subst sub t
    u' = subst sub u

-- | Check if a rule can be applied normally.
{-# INLINEABLE reduces #-}
reduces :: Function f => Rule f -> Subst f -> Bool
reduces rule sub = reducesWith lessEq rule sub

-- | Check if a rule can be applied and is oriented.
{-# INLINEABLE reducesOriented #-}
reducesOriented :: Function f => Rule f -> Subst f -> Bool
reducesOriented rule sub =
  oriented (orientation rule) && reducesWith undefined rule sub

-- | Check if a rule can be applied in a particular model.
{-# INLINEABLE reducesInModel #-}
reducesInModel :: Function f => Model f -> Rule f -> Subst f -> Bool
reducesInModel cond rule sub =
  reducesWith (\t u -> isJust (lessIn cond t u)) rule sub

-- | Check if a rule can be applied to the Skolemised version of a term.
{-# INLINEABLE reducesSkolem #-}
reducesSkolem :: Function f => Rule f -> Subst f -> Bool
reducesSkolem rule sub =
  reducesWith (\t u -> lessEqSkolem t u) rule sub

--------------------------------------------------------------------------------
-- * Rewriting that performs only a single step at a time (not in parallel).
--------------------------------------------------------------------------------

-- | A reduction proof is a sequence of rewrite steps, stored as a
-- list. Each rewrite step is coded as a rule, a
-- substitution and a path to be rewritten.
type Reduction1 f = [(Rule f, Subst f, [Int])]

-- | Transitivity for reduction sequences.
trans1 :: Reduction1 f -> Reduction1 f -> Reduction1 f
trans1 p q = p ++ q

-- TODO: get rid of the below copy-and-pasting by introducing a typeclass

-- | Compute the final term resulting from a reduction, given the
-- starting term.
result1 :: HasCallStack => Term f -> Reduction1 f -> Term f
result1 t [] = t
result1 t (r:rs) = result1 u rs
  where
    !u = ruleResult1 t r

-- | Turn a reduction into a proof.
reductionProof1 :: Function f => Term f -> Reduction1 f -> Derivation f
reductionProof1 t ps = red t (Proof.Refl t) ps
  where
    red _ p [] = p
    red t p (q:qs) =
      red (ruleResult1 t q) (p `Proof.trans` ruleProof1 t q) qs

-- Helpers for result1 and reductionProof1.
ruleResult1 :: HasCallStack => Term f -> (Rule f, Subst f, [Int]) -> Term f
ruleResult1 t (r0, sub, p)
  | t `at` n == lhs r =
    build (replacePosition n (rhs r) (singleton t))
  | otherwise = error "ruleResult1: selected subterm is not equal to lhs of rule"
  where
    r = subst sub r0
    n = pathToPosition t p

ruleProof1 :: Function f => Term f -> (Rule f, Subst f, [Int]) -> Derivation f
ruleProof1 t (r0, sub, p)
  | t `atPath` p == lhs r =
    Proof.congPath p t (ruleDerivation r)    
  | otherwise = error "ruleProof1: selected subterm is not equal to lhs of rule"
  where
    r = subst sub r0

-- | A strategy gives a set of possible reductions for a term.
type Strategy1 f = Term f -> [Reduction1 f]

-- | Apply a strategy anywhere in a term.
anywhere1 :: Strategy1 f -> Strategy1 f
anywhere1 strat t =
  stamp "anywhere1 (whnf)"
  [ [(r, sub, p ++ p') | (r, sub, p') <- red]
  | n <- reverse [0..len t-1], -- innermost
    let p = positionToPath t n,
    red <- strat (t `at` n) ]

-- | Apply a basic strategy to a term.
basic :: Strategy f -> Strategy1 f
basic strat t = [[(r, sub, [])] | [(r, sub)] <- strat t]

-- | Normalise a term wrt a particular strategy.
{-# INLINE normaliseWith1 #-}
normaliseWith1 :: Function f => (Term f -> Bool) -> Strategy1 f -> Term f -> Reduction1 f
normaliseWith1 ok strat t = aux t
  where
    aux t =
      case anywhere1 strat t of
        (p:_) | u <- result1 t p, ok u ->
          p `trans1` aux u
        _ -> []

-- | Normalise a term wrt a particular strategy, picking random
-- rewrites at every step.
{-# INLINE normaliseWith1Random #-}
normaliseWith1Random :: Function f => (Term f -> Bool) -> Strategy1 f -> Term f -> Gen (Reduction1 f)
normaliseWith1Random ok strat t = aux t
  where
    aux t =
      let choices = [(p, u) | p <- anywhere1 strat t, let u = stamp "normaliseWith1Random.result1" (result1 t p), ok u] in
      case choices of
        [] -> return []
        _ -> do
          (p, u) <- elements choices
          fmap (p `trans1`) (aux u)

--------------------------------------------------------------------------------
-- * Testing whether a term has a unique normal form.
--------------------------------------------------------------------------------

data UNF f =
    -- Function has a unique normal form
    UniqueNormalForm
  | -- This pair of rules has an unjoinable critical pair
    HasCriticalPair (Rule f) (Rule f, Int) (Term f) (Term f)

instance Semigroup (UNF f) where
  -- mconcat finds the first HasCriticalPair in the list
  UniqueNormalForm <> x = x
  x@HasCriticalPair{} <> _ = x
instance Monoid (UNF f) where
  mempty = UniqueNormalForm

instance Function f => Pretty (UNF f) where
  pPrint UniqueNormalForm = text "unique normal form"
  pPrint (HasCriticalPair r1 (r2, n) _ _) = text "critical pair" <+> pPrint r1 <+> pPrint (r2, n)

hasUNF :: Function f => Strategy1 f -> Term f -> Gen (UNF f)
hasUNF strat =
  \t -> -- don't bind t in where-clause
  sized $ \n ->
  let res = magic 3 t -- always try at least 1 path
  in stampGen' (\res -> case res of { UniqueNormalForm -> "hasUNF.UNF"; HasCriticalPair{} -> "hasUNF.CP" }) res
  where
    trace _ x = x
    normFirstStep t = trace (prettyShow (t, take 1 $ anywhere1 strat t)) $ head (head (anywhere1 strat t))
    normSteps t = normaliseWith1 (const True) strat t
    norm = memo $ \t -> stamp "hasUNF.norm" (result1 t (normSteps t))

    magic n t = do
      rs <- mapM (magic n) (unpack (children t))
      r  <- here n t
      return (mconcat rs `mappend` r)

    here n t = fmap mconcat $ replicateM n $ stampGen "hasUNF.here" $ do
      r <- normaliseWith1Random (const True) strat t
      let u = stamp "hasUNF.result1" (result1 t r)
      return $
        if norm t == u then UniqueNormalForm else badPath t u r
      
    -- precondition: r is a proof of t->*u where norm t /= norm u
    badPath t u rs = stamp "badPath" (badPath' t u rs)
    badPath' t u rs
      | trace ("bad path " ++ prettyShow t ++ " -> " ++ prettyShow u ++ " (normal forms = " ++ prettyShow (norm t, norm u) ++ "): " ++ prettyShow rs) False = undefined
    badPath' _ _ [] = error "badPath: empty list"
    badPath' t u (r:rs)
      | norm v == norm u = conflict t r (normFirstStep t)
      | otherwise =
        trace ("v = " ++ prettyShow v ++ ", u = " ++ prettyShow u ++ ", norm v = " ++ prettyShow (norm v) ++ ", norm u = " ++ prettyShow (norm u)) $
        badPath' v u rs
      where
        v = result1 t [r]

    -- precondition: normR t r1 /= normR t r2
    conflict t r1 r2 = stamp "conflict" (conflict' t r1 r2)
    conflict' t r1 r2
      | trace "" $
        trace ("Conflicting term: " ++ prettyShow t) $
        trace ("Rule 1: " ++ prettyShow r1) $
        trace ("Rule 2: " ++ prettyShow r2) $
        trace "" False = undefined

    -- Both rewrites apply to the same subterm.
    -- Hypothesis: descending into the subterm will still find a conflict as long as norm is innermost
    conflict' t (r1, sub1, (p1:ps1)) (r2, sub2, (p2:ps2)) | p1 == p2 =
      conflict' (unpack (children t) !! p1) (r1, sub1, ps1) (r2, sub2, ps2)

    -- One rule is at the root (first normalise so that r1 is at the root)
    conflict' t (r1, sub1, p@(_:_)) (r2, sub2, []) =
      conflict' t (r2, sub2, []) (r1, sub1, p)
    conflict' t rr1@(r1, sub1, []) rr2@(r2, sub2, p)
      | criticalOverlap (lhs r1) p =
        trace ("Critical pair " ++ prettyShow (r1, r2, p)) $
        HasCriticalPair r1 (r2, pathToPosition (lhs r1) p) (norm (result1 t [rr1])) (norm (result1 t [rr2]))
      | otherwise = nonOverlapping t (r1, sub1, []) (r2, sub2, p)
    -- Rewrites apply to parallel subterms and can be easily commuted
    conflict' t r1 r2 = nonOverlapping t r1 r2

    -- Precondition: r1 can be commuted with some number of parallel
    -- rewrites of r2
    nonOverlapping t r1 r2 = stamp "nonOverlapping" (nonOverlapping' t r1 r2)
    nonOverlapping' t r1@(rule1, _, p1) r2@(rule2, _, p2)
      | trace "" $
        trace ("Non-overlapping reduction: " ++ prettyShow t) $
        trace ("First rule: " ++ prettyShow r1) $
        trace ("Second rule: " ++ prettyShow r2) $
        trace ("Reduction of first rule: " ++ prettyShow u) $
        trace ("Reduction of second rule: " ++ prettyShow v) $
        trace ("Positions before: " ++ prettyShow ps2Before) $
        trace ("Positions after: " ++ prettyShow ps2After) $
        trace ("Rules before: " ++ prettyShow rs2Before) $
        trace ("Rules after: " ++ prettyShow rs2After) $
        trace ("Final term: " ++ prettyShow w) $
        False = undefined
      | norm w /= norm u = trace "1" $ badPath u w conf1
      | norm w /= norm v = trace "2" $ badPath v w conf2
      where
        u = result1 t [r1]
        v = result1 t [r2]
        (ps2Before, ps2After) = track rule1 p1 p2
        rs2Before = [(rule2, rematch rule2 p t, p) | p <- ps2Before, p /= p2]
        rs2After = [(rule2, rematch rule2 p u, p) | p <- ps2After]

        -- Two paths:
        -- (1) r1; rs2After
        -- (2) rs2Before; r1
        -- But, in (2), if r1 is oriented the wrong way, we do this instead:
        -- (1) r1; rs2After; backwards r1
        -- (2) rs2Before

        -- TODO don't code term ordering
        correctlyOriented = reducesSkolem rule1 sub1After
        sub1After = rematch rule1 p1 (result1 v rs2Before)

        -- The two reductions are: [red1] `trans` conf1, [red2] `trans` conf2
        conf1 = rs2After `trans1` (if correctlyOriented then [] else [(backwards rule1, sub1After, p1)])
        conf2 = rs2Before `trans1` (if correctlyOriented then [(rule1, sub1After, p1)] else [])

        -- Check that both reductions give the same result
        w1 = result1 u conf1
        w2 = result1 v conf2
        w | w1 == w2 = w1
        
    criticalOverlap (Var _) _ = False
    criticalOverlap App{} [] = True
    criticalOverlap t (p:ps) = criticalOverlap (unpack (children t) !! p) ps

    -- find the substitution for a rewrite
    rematch r pos t = sub
      where
        Just sub = match (lhs r) (t `atPath` pos)

-- Given a path in a term which is below a variable, find the variable
-- and the part of the path below the variable
decomposePath (Var x) ps = (x, ps)
decomposePath t (p:ps) = decomposePath (unpack (children t) !! p) ps

-- positions of a variable in a term
varPos :: Var -> Term f -> [Int]
varPos x t = [n | n <- [0..len t-1], t `at` n == build (var x)]

-- Consider a rewrite t -> u at position pr in a term, and a position
-- pt that does not overlap with the rewrite:
-- (1) Suppose that right now the rewrite could be applied, but
--     instead do a different rewrite at position pt. What other
--     positions must be also rewrite for the original rewrite to
--     still be applicable?
--     (e.g.: if the rule is f(x,x)->..., and the position is one of
--     the "x"s, if we rewrite one "x" we must also rewrite the other)
-- (2) Where does the position pt "move to" after the rewrite?
track :: Rule f -> [Int] -> [Int] -> ([[Int]], [[Int]])
track r (p:pr) (p':pt)
    -- common prefix
  | p == p' = (map (p:) *** map (p:)) (track r pr pt)
    -- parallel prefix
  | otherwise = ([p':pt], [p':pt])
track _ (_:_) [] =
  -- position being tracked < position of rewrite
  ([[]], [[]])
track Rule{lhs = lhs, rhs = rhs} [] pt =
  -- strategy: find what variable position pt occurs under in the lhs of the rule,
  -- then find all occurrences of that variable in the rhs of the rule
  let
    (x, p) = decomposePath lhs pt
  in
    ([positionToPath lhs n ++ p | n <- varPos x lhs],
     [positionToPath rhs n ++ p | n <- varPos x rhs])

{-
hasUNFSlow :: Function f => Strategy1 f -> Term f -> UNF f
hasUNFSlow strat t0 =
  head $
    -- optimisation: check if any subterm has a non-unique normal form first
    [r | r@HasCriticalPair{} <- map magic (sortBy (comparing len) (properSubterms t0))] ++
    [magic t0]
  where
    magic = memo $ \t ->
      --trace ("magic " ++ prettyShow t) $
      let
        as = [(red, {-trace ("recursing from " ++ prettyShow t ++ " to " ++ prettyShow (result1 t red) ++ " via " ++ prettyShow red) $-} magic (result1 t red)) | red <- strat t, if result1 t red == t then error "oops" else True]

        conflict (r1, []) (r2, p) = HasCriticalPair r1 (r2, pathToPosition (lhs r1) p)
        conflict (r1, p) (r2, []) = HasCriticalPair r2 (r1, pathToPosition (lhs r2) p)
        conflict (r1, (m:ms)) (r2, (n:ns)) | m == n = conflict (r1, ms) (r2, ns)
        conflict _ _ = error "something has gone wrong in the magic function"

        res = head $
          [r | r@HasCriticalPair{} <- map snd as] ++
          case nubBy ((==) `on` snd) ([(red, t) | (red, UniqueNormalForm t) <- as]) of
            [] -> [UniqueNormalForm t]
            [(_, t)] -> [UniqueNormalForm t]
            ((r1, _, n1):_, t1):((r2, _, n2):_, t2):_ ->
              [conflict (r1, positionToPath t n1) (r2, positionToPath t n2)]
      in {-traceShow (pPrint res)-} res
-}
