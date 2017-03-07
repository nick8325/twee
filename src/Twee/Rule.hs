{-# LANGUAGE TypeFamilies, FlexibleContexts, RecordWildCards, CPP, BangPatterns, OverloadedStrings, DeriveGeneric, MultiParamTypeClasses, ScopedTypeVariables, GeneralizedNewtypeDeriving #-}
module Twee.Rule where

#include "errors.h"
import Twee.Base
import Twee.Constraints
import qualified Twee.Index as Index
import Twee.Index(Index)
import Control.Monad
import Control.Monad.Trans.Class
import Control.Monad.Trans.State.Strict
import Data.Maybe
import Data.List
import Twee.Utils
import qualified Data.Set as Set
import Data.Set(Set)
import qualified Twee.Term as Term
import GHC.Generics
import Data.Ord
import Twee.Equation
import qualified Twee.Proof as Proof
import Twee.Proof(Proof, Derivation, Lemma(..))

--------------------------------------------------------------------------------
-- Rewrite rules.
--------------------------------------------------------------------------------

data Rule f =
  Rule {
    orientation :: !(Orientation f),
    -- Invariant:
    -- For oriented rules: vars rhs `isSubsetOf` vars lhs
    -- For unoriented rules: vars lhs == vars rhs
    lhs :: {-# UNPACK #-} !(Term f),
    rhs :: {-# UNPACK #-} !(Term f) }
  deriving (Eq, Ord, Show, Generic)
type RuleOf a = Rule (ConstantOf a)

data Orientation f =
    -- Oriented rules: used only left-to-right
    Oriented
  | WeaklyOriented {-# UNPACK #-} !(Fun f) [Term f]
    -- Unoriented rules: used bidirectionally
  | Permutative [(Term f, Term f)]
  | Unoriented
  deriving Show

instance Eq (Orientation f) where _ == _ = True
instance Ord (Orientation f) where compare _ _ = EQ

oriented :: Orientation f -> Bool
oriented Oriented{} = True
oriented WeaklyOriented{} = True
oriented _ = False

weaklyOriented :: Orientation f -> Bool
weaklyOriented WeaklyOriented{} = True
weaklyOriented _ = False

instance Symbolic (Rule f) where
  type ConstantOf (Rule f) = f

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

instance PrettyTerm f => Pretty (Rule f) where
  pPrint (Rule or l r) =
    pPrint l <+> text (showOrientation or) <+> pPrint r
    where
      showOrientation Oriented = "->"
      showOrientation WeaklyOriented{} = "~>"
      showOrientation Permutative{} = "<->"
      showOrientation Unoriented = "="

-- Turn a rule into an equation.
unorient :: Rule f -> Equation f
unorient (Rule _ l r) = l :=: r

-- Turn a pair of terms t and u into a rule t -> u by computing the
-- orientation info (e.g. oriented, permutative or unoriented).
makeRule :: Function f => Term f -> Term f -> Rule f
makeRule t u = Rule o t u
  where
    o | lessEq u t =
        case unify t u of
          Nothing -> Oriented
          Just sub
            | allSubst (\_ (Cons t Empty) -> isMinimal t) sub ->
              WeaklyOriented minimal (map (build . var . fst) (listSubst sub))
            | otherwise -> Unoriented
      | lessEq t u = ERROR("wrongly-oriented rule")
      | not (null (usort (vars u) \\ usort (vars t))) =
        ERROR("unbound variables in rule")
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
      msub <- gets flattenSubst
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

--------------------------------------------------------------------------------
-- Extra-fast rewriting, without proof output or unorientable rules.
--------------------------------------------------------------------------------

-- Compute the normal form of a term wrt only oriented rules.
{-# INLINEABLE simplify #-}
simplify :: (Function f, Has a (Rule f)) => Index f a -> Term f -> Term f
simplify !idx !t = {-# SCC simplify #-} simplify1 idx t

{-# INLINEABLE simplify1 #-}
simplify1 :: (Function f, Has a (Rule f)) => Index f a -> Term f -> Term f
simplify1 idx t
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

-- Check if a term can be simplified.
{-# INLINEABLE canSimplify #-}
canSimplify :: (Function f, Has a (Rule f)) => Index f a -> Term f -> Bool
canSimplify idx t = canSimplifyList idx (singleton t)

{-# INLINEABLE canSimplifyList #-}
canSimplifyList :: (Function f, Has a (Rule f)) => Index f a -> TermList f -> Bool
canSimplifyList idx t =
  {-# SCC canSimplifyList #-}
  any (isJust . simpleRewrite idx) (filter isApp (subtermsList t))

-- Find a simplification step that applies to a term.
{-# INLINEABLE simpleRewrite #-}
simpleRewrite :: (Function f, Has a (Rule f)) => Index f a -> Term f -> Maybe (Rule f, Subst f)
simpleRewrite idx t =
  -- Use instead of maybeToList to make fusion work
  foldr (\x _ -> Just x) Nothing $ do
    rule <- the <$> Index.approxMatches t idx
    guard (oriented (orientation rule))
    sub <- maybeToList (match (lhs rule) t)
    guard (reducesOriented rule sub)
    return (rule, sub)

--------------------------------------------------------------------------------
-- Rewriting, with proof output.
--------------------------------------------------------------------------------

type Strategy f = Term f -> [Reduction f]

-- A multi-step rewrite proof t ->* u
data Reduction f =
    -- Apply a single rewrite rule to the root of a term
    Step {-# UNPACK #-} !(Lemma f) !(Rule f) !(Subst f)
    -- Reflexivity
  | Refl {-# UNPACK #-} !(Term f)
    -- Transivitity
  | Trans !(Reduction f) !(Reduction f)
    -- Congruence
  | Cong {-# UNPACK #-} !(Fun f) ![Reduction f]
  deriving Show

instance Symbolic (Reduction f) where
  type ConstantOf (Reduction f) = f
  termsDL (Step _ _ sub) = termsDL sub
  termsDL (Refl t) = termsDL t
  termsDL (Trans p q) = termsDL p `mplus` termsDL q
  termsDL (Cong _ ps) = termsDL ps

  subst_ sub (Step lemma rule s) = Step lemma rule (subst_ sub s)
  subst_ sub (Refl t) = Refl (subst_ sub t)
  subst_ sub (Trans p q) = Trans (subst_ sub p) (subst_ sub q)
  subst_ sub (Cong f ps) = Cong f (subst_ sub ps)

instance Function f => Pretty (Reduction f) where
  pPrint = pPrint . reductionProof

-- Smart constructors for Trans and Cong which simplify Refl.
trans :: Reduction f -> Reduction f -> Reduction f
trans Refl{} p = p
trans p Refl{} = p
-- Make right-associative to improve performance of 'result'
trans p (Trans q r) = Trans (Trans p q) r
trans p q = Trans p q

cong :: Fun f -> [Reduction f] -> Reduction f
cong f ps
  | all isRefl ps = Refl (result (reduce (Cong f ps)))
  | otherwise = Cong f ps
  where
    isRefl Refl{} = True
    isRefl _ = False

-- Applies a reduction at a particular path in a term.
congPath :: [Int] -> Term f -> Reduction f -> Reduction f
congPath [] _ p = p
congPath (n:ns) (App f t) p | n <= length ts =
  cong f $
    map Refl (take n ts) ++
    [congPath ns (ts !! n) p] ++
    map Refl (drop (n+1) ts)
  where
    ts = unpack t
congPath _ _ _ = error "bad path"

-- The list of all rewrite rules used in a rewrite proof
steps :: Reduction f -> [Reduction f]
steps r = aux r []
  where
    aux step@Step{} = (step:)
    aux (Refl _) = id
    aux (Trans p q) = aux p . aux q
    aux (Cong _ ps) = foldr (.) id (map aux ps)

-- Turn a reduction into a proof.
reductionProof :: Reduction f -> Derivation f
reductionProof (Step lemma _ sub) =
  Proof.lemma lemma sub
reductionProof (Refl t) = Proof.Refl t
reductionProof (Trans p q) =
  Proof.trans (reductionProof p) (reductionProof q)
reductionProof (Cong f ps) = Proof.cong f (map reductionProof ps)

-- Construct a basic rewrite step.
{-# INLINE step #-}
step :: (Has a VersionedId, Has a (Rule f), Has a (Proof f)) => a -> Subst f -> Reduction f
step x sub = Step (Lemma (the x) (the x)) (the x) sub

----------------------------------------------------------------------
-- A rewrite proof with the final term attached.
-- Has an Ord instance which compares the final term.
----------------------------------------------------------------------

data Resulting f =
  Resulting {
    result :: {-# UNPACK #-} !(Term f),
    reduction :: !(Reduction f) }
  deriving (Show, Generic)

instance Eq (Resulting f) where x == y = compare x y == EQ
instance Ord (Resulting f) where compare = comparing result

instance Symbolic (Resulting f) where
  type ConstantOf (Resulting f) = f

instance Function f => Pretty (Resulting f) where
  pPrint = pPrint . reduction

reduce :: Reduction f -> Resulting f
reduce p =
  Resulting (res p) p
  where
    res (Trans _ q) = res q
    res (Refl t) = t
    res p = {-# SCC res_emitRes #-} build (emitResult p)

    emitResult (Step _ r sub) = Term.subst sub (rhs r)
    emitResult (Refl t) = builder t
    emitResult (Trans _ q) = emitResult q
    emitResult (Cong f ps) = app f (map emitResult ps)

--------------------------------------------------------------------------------
-- Strategy combinators.
--------------------------------------------------------------------------------

-- Normalise a term wrt a particular strategy.
{-# INLINE normaliseWith #-}
normaliseWith :: Function f => (Term f -> Bool) -> Strategy f -> Term f -> Resulting f
normaliseWith ok strat t = {-# SCC normaliseWith #-} res
  where
    res = aux 0 (Refl t) t
    aux 1000 p _ =
      ERROR("Possibly nonterminating rewrite:\n" ++
            prettyShow p)
    aux n p t =
      case parallel strat t of
        (q:_) | u <- result (reduce q), ok u ->
          aux (n+1) (p `trans` q) u
        _ -> Resulting t p

-- Compute all normal forms of a term wrt a particular strategy.
{-# INLINEABLE normalForms #-}
normalForms :: Function f => Strategy f -> [Resulting f] -> Set (Resulting f)
normalForms strat ps =
  {-# SCC normalForms #-} go Set.empty Set.empty ps
  where
    go _ norm [] = norm
    go dead norm (p:ps)
      | p `Set.member` dead = go dead norm ps
      | p `Set.member` norm = go dead norm ps
      | null qs = go dead (Set.insert p norm) ps
      | otherwise =
        go (Set.insert p dead) norm (qs ++ ps)
      where
        qs =
          [ reduce (reduction p `Trans` q)
          | q <- anywhere strat (result p) ]

-- Apply a strategy anywhere in a term.
anywhere :: Strategy f -> Strategy f
anywhere strat t = strat t ++ nested (anywhere strat) t

-- Apply a strategy to some child of the root function.
nested :: Strategy f -> Strategy f
nested _ Var{} = []
nested strat (App f ts) =
  cong f <$> inner [] ts
  where
    inner _ Empty = []
    inner before (Cons t u) =
      [ reverse before ++ [p] ++ map Refl (unpack u)
      | p <- strat t ] ++
      inner (Refl t:before) u

-- Apply a strategy in parallel in as many places as possible.
-- Takes only the first rewrite of each strategy.
{-# INLINE parallel #-}
parallel :: PrettyTerm f => Strategy f -> Strategy f
parallel strat t =
  case par t of
    Refl{} -> []
    p -> [p]
  where
    par t | p:_ <- strat t = p
    par (App f ts) = cong f (inner [] ts)
    par t = Refl t

    inner before Empty = reverse before
    inner before (Cons t u) = inner (par t:before) u

--------------------------------------------------------------------------------
-- Basic strategies. These only apply at the root of the term.
--------------------------------------------------------------------------------

-- A strategy which rewrites using an index.
{-# INLINE rewrite #-}
rewrite :: (Function f, Has a (Rule f), Has a (Proof f), Has a VersionedId) => (Rule f -> Subst f -> Bool) -> Index f a -> Strategy f
rewrite p rules t = do
  rule <- Index.approxMatches t rules
  tryRule p rule t

-- A strategy which applies one rule only.
{-# INLINEABLE tryRule #-}
tryRule :: (Function f, Has a (Rule f), Has a (Proof f), Has a VersionedId) => (Rule f -> Subst f -> Bool) -> a -> Strategy f
tryRule p rule t = do
  sub <- maybeToList (match (lhs (the rule)) t)
  guard (p (the rule) sub)
  return (step rule sub)

-- Check if a rule can be applied, given an ordering <= on terms.
{-# INLINEABLE reducesWith #-}
reducesWith :: Function f => (Term f -> Term f -> Bool) -> Rule f -> Subst f -> Bool
reducesWith _ (Rule Oriented _ _) _ = True
reducesWith _ (Rule (WeaklyOriented min ts) _ _) sub =
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
reducesWith p (Rule (Permutative ts) _ _) sub =
  aux ts
  where
    aux [] = False
    aux ((t, u):ts)
      | t' == u' = aux ts
      | otherwise = p u' t'
      where
        t' = subst sub t
        u' = subst sub u
reducesWith p (Rule Unoriented t u) sub =
  p u' t' && u' /= t'
  where
    t' = subst sub t
    u' = subst sub u

-- Check if a rule can be applied normally.
{-# INLINEABLE reduces #-}
reduces :: Function f => Rule f -> Subst f -> Bool
reduces rule sub = reducesWith lessEq rule sub

-- Check if a rule can be applied and is oriented.
{-# INLINEABLE reducesOriented #-}
reducesOriented :: Function f => Rule f -> Subst f -> Bool
reducesOriented rule sub =
  oriented (orientation rule) && reducesWith undefined rule sub

-- Check if a rule can be applied in various circumstances.
{-# INLINEABLE reducesInModel #-}
reducesInModel :: Function f => Model f -> Rule f -> Subst f -> Bool
reducesInModel cond rule sub =
  reducesWith (\t u -> isJust (lessIn cond t u)) rule sub

{-# INLINEABLE reducesSkolem #-}
reducesSkolem :: Function f => Rule f -> Subst f -> Bool
reducesSkolem rule sub =
  reducesWith (\t u -> lessEq (subst skolemise t) (subst skolemise u)) rule sub
  where
    skolemise = con . skolem
