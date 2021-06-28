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
{-# SCC simplify #-}
simplify :: (Function f, Has a (Rule f)) => Index f a -> Term f -> Term f
simplify = simplifyOutermost

-- | Compute the normal form of a term wrt only oriented rules, using outermost reduction.
simplifyOutermost :: (Function f, Has a (Rule f)) => Index f a -> Term f -> Term f
simplifyOutermost !idx !t
  | t == u = t
  | otherwise = simplify idx u
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
{-# SCC simpleRewrite #-}
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

-- | A reduction proof is just a sequence of rewrite steps, stored
-- as a list in reverse order. In each rewrite step, all subterms that
-- are exactly equal to the LHS of the rule are replaced by the RHS,
-- i.e. the rewrite step is performed as a parallel rewrite without
-- matching.
type Reduction f = [Rule f]

-- | Transitivity for reduction sequences.
trans :: Reduction f -> Reduction f -> Reduction f
trans p q = q ++ p

-- | Compute the final term resulting from a reduction, given the
-- starting term.
result :: Term f -> Reduction f -> Term f
result t [] = t
result t (r:rs) = ruleResult u r
  where
    u = result t rs

-- | Turn a reduction into a proof.
reductionProof :: Function f => Term f -> Reduction f -> Derivation f
reductionProof t ps = red t (Proof.Refl t) (reverse ps)
  where
    red _ p [] = p
    red t p (q:qs) =
      red (ruleResult t q) (p `Proof.trans` ruleProof t q) qs

-- Helpers for result and reductionProof.
ruleResult :: Term f -> Rule f -> Term f
ruleResult t r = build (replace (lhs r) (rhs r) (singleton t))

ruleProof :: Function f => Term f -> Rule f -> Derivation f
ruleProof t r@(Rule _ _ lhs _)
  | t == lhs = ruleDerivation r
  | len t < len lhs = Proof.Refl t
ruleProof (App f ts) rule =
  Proof.cong f [ruleProof u rule | u <- unpack ts]
ruleProof t _ = Proof.Refl t

--------------------------------------------------------------------------------
-- * Normalisation.
--------------------------------------------------------------------------------

-- | Normalise a term wrt a particular strategy.
{-# INLINE normaliseWith #-}
{-# SCC normaliseWith #-}
normaliseWith :: Function f => (Term f -> Bool) -> Strategy f -> Term f -> Reduction f
normaliseWith ok strat t = res
  where
    res = aux 0 [] t
    aux 1000 p _ =
      error $
        "Possibly nonterminating rewrite:\n" ++ prettyShow p
    aux n p t =
      case anywhere strat t of
        (q:_) | u <- result t q, ok u ->
          aux (n+1) (p `trans` q) u
        _ -> p

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
{-# SCC successorsAndNormalForms #-}
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
  return [subst sub (the rule)]

-- | A strategy which applies one rule only.
{-# INLINEABLE tryRule #-}
tryRule :: (Function f, Has a (Rule f)) => (Rule f -> Subst f -> Bool) -> a -> Strategy f
tryRule p rule t = do
  sub <- maybeToList (match (lhs (the rule)) t)
  guard (p (the rule) sub)
  return [subst sub (the rule)]

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
