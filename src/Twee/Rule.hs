{-# LANGUAGE TypeFamilies, FlexibleContexts, RecordWildCards, CPP, BangPatterns, OverloadedStrings, DeriveGeneric #-}
module Twee.Rule where

#include "errors.h"
import Twee.Base
import Twee.Constraints
import qualified Twee.Index.Simple as Index
import Twee.Index.Simple(Index)
import Control.Monad
import Control.Monad.Trans.Class
import Control.Monad.Trans.State.Strict
import Data.Maybe
import Data.List
import Twee.Utils
import qualified Data.Set as Set
import Data.Set(Set)
import qualified Twee.Term as Term
import Twee.Profile
import GHC.Generics

--------------------------------------------------------------------------------
-- Rewrite rules.
--------------------------------------------------------------------------------

data Rule f =
  Rule {
    orientation :: Orientation f,
    lhs :: Term f,
    rhs :: Term f }
  deriving (Eq, Ord, Show, Generic)

data Orientation f =
    Oriented [Term f]
  | Permutative [(Term f, Term f)]
  | Unoriented
  deriving (Show, Generic)

instance Eq (Orientation f) where _ == _ = True
instance Ord (Orientation f) where compare _ _ = EQ

oriented :: Orientation f -> Bool
oriented Oriented{} = True
oriented _ = False

instance Symbolic (Rule f) where
  type ConstantOf (Rule f) = f
instance Singular (Rule f) where
  term = lhs

instance Symbolic (Orientation f) where
  type ConstantOf (Orientation f) = f

instance PrettyTerm f => Pretty (Rule f) where
  pPrint (Rule (Oriented []) l r) = pPrintRule l r
  pPrint (Rule (Oriented ts) l r) = hang (pPrintRule l r) 2 (text "(weak on" <+> pPrint ts <> text ")")
  pPrint (Rule (Permutative ts) l r) = hang (pPrintRule l r) 2 (text "(permutative on" <+> pPrint ts <> text ")")
  pPrint (Rule Unoriented l r) = hang (pPrintRule l r) 2 (text "(unoriented)")

pPrintRule :: PrettyTerm f => Term f -> Term f -> Doc
pPrintRule l r = hang (pPrint l <+> text "->") 2 (pPrint r)

--------------------------------------------------------------------------------
-- Equations.
--------------------------------------------------------------------------------

data Equation f = Term f :=: Term f deriving (Eq, Ord, Show, Generic)
type EquationOf a = Equation (ConstantOf a)

instance Symbolic (Equation f) where
  type ConstantOf (Equation f) = f

instance PrettyTerm f => Pretty (Equation f) where
  pPrint (x :=: y) = hang (pPrint x <+> text "=") 2 (pPrint y)

instance Sized f => Sized (Equation f) where
  size (x :=: y) = size x + size y

-- Order an equation roughly left-to-right.
-- However, there is no guarantee that the result is oriented.
order :: Function f => Equation f -> Equation f
order (l :=: r)
  | l == r = l :=: r
  | otherwise =
    case compare (size l) (size r) of
      LT -> r :=: l
      GT -> l :=: r
      EQ -> if lessEq l r then r :=: l else l :=: r

-- Turn a rule into an equation.
unorient :: Rule f -> Equation f
unorient (Rule _ l r) = l :=: r

-- Turn an equation into a set of rules.
orient :: Function f => Equation f -> [Rule f]
orient (l :=: r) | l == r = []
orient (l :=: r) =
  -- If we have an equation where some variables appear only on one side, e.g.:
  --   f x y = g x z
  -- then replace it with the equations:
  --   f x y = f x k
  --   g x z = g x k
  --   f x k = g x k
  -- where k is an arbitrary constant
  [ rule l r' | ord /= Just LT && ord /= Just EQ ] ++
  [ rule r l' | ord /= Just GT && ord /= Just EQ ] ++
  [ rule l l' | not (null ls), ord /= Just GT ] ++
  [ rule r r' | not (null rs), ord /= Just LT ]
  where
    ord = orientTerms l' r'
    l' = erase ls l
    r' = erase rs r
    ls = usort (vars l) \\ usort (vars r)
    rs = usort (vars r) \\ usort (vars l)

    erase [] t = t
    erase xs t = subst sub t
      where
        sub = fromMaybe __ $ flattenSubst [(x, minimalTerm) | x <- xs]

-- Turn a pair of terms t and u into a rule t -> u by computing the
-- orientation info (e.g. oriented, permutative or unoriented).
rule :: Function f => Term f -> Term f -> Rule f
rule t u = Rule o t u
  where
    o | lessEq u t =
        case unify t u of
          Nothing -> Oriented []
          Just sub
            | allSubst (\_ (Cons t Empty) -> isMinimal t) sub ->
              Oriented (map (build . var . fst) (listSubst sub))
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

-- Apply a function to both sides of an equation.
bothSides :: (Term f -> Term f') -> Equation f -> Equation f'
bothSides f (t :=: u) = f t :=: f u

-- Is an equation of the form t = t?
trivial :: Eq f => Equation f -> Bool
trivial (t :=: u) = t == u

--------------------------------------------------------------------------------
-- Rewriting, with proof output.
--------------------------------------------------------------------------------

type Strategy f = Term f -> [Reduction f]

-- A multi-step rewrite proof t ->* u
data Reduction f =
    -- Apply a single rewrite rule to the root of a term
    Step (Rule f) (Subst f)
    -- Reflexivity
  | Trans (Reduction f) (Reduction f)
    -- Parallel rewriting given a list of (position, rewrite) pairs
    -- and the initial term
  | Parallel [(Int, Reduction f)] (Term f)
  deriving Show

instance PrettyTerm f => Pretty (Reduction f) where
  pPrint = pPrintReduction

pPrintReduction :: PrettyTerm f => Reduction f -> Doc
pPrintReduction p =
  case flatten p of
    [p] -> pp p
    ps -> pPrint (map pp ps)
  where
    flatten (Trans p q) = flatten p ++ flatten q
    flatten p = [p]

    pp p = sep [pp0 p, nest 2 (text "giving" <+> pPrint (result p))]
    pp0 (Step rule sub) =
      sep [pPrint rule,
           nest 2 (text "at" <+> pPrint sub)]
    pp0 (Parallel [] _) = text "refl"
    pp0 (Parallel [(0, p)] _) = pp0 p
    pp0 (Parallel ps _) =
      sep (punctuate (text " and")
        [hang (pPrint n <+> text "->") 2 (pPrint p) | (n, p) <- ps])

-- Find the initial term of a rewrite proof
initial :: Reduction f -> Term f
initial (Step r sub) = subst sub (lhs r)
initial (Trans p _) = initial p
initial (Parallel _ t) = t

-- Find the final term of a rewrite proof
result :: Reduction f -> Term f
result (Parallel [] t) = t
result (Trans _ p) = result p
result t = stamp "executing rewrite" (build (emitReduction t))
  where
    emitReduction (Step r sub) = Term.subst sub (rhs r)
    emitReduction (Trans _ p) = emitReduction p
    emitReduction (Parallel ps t) = emitParallel 0 ps (singleton t)

    emitParallel !_ _ _ | False = __
    emitParallel _ _ Empty = mempty
    emitParallel _ [] t = builder t
    emitParallel n ((m, _):_) t  | m >= n + lenList t = builder t
    emitParallel n ps@((m, _):_) (Cons t u) | m >= n + len t =
      builder t `mappend` emitParallel (n + len t) ps u
    emitParallel n ((m, _):ps) t | m < n = emitParallel n ps t
    emitParallel n ((m, p):ps) (Cons t u) | m == n =
      emitReduction p `mappend` emitParallel (n + len t) ps u
    emitParallel n ps (Cons (Var x) u) =
      var x `mappend` emitParallel (n + 1) ps u
    emitParallel n ps (Cons (App f t) u) =
      app f (emitParallel (n+1) ps t) `mappend`
      emitParallel (n + 1 + lenList t) ps u

-- The list of all rewrite rules used in a proof
steps :: Reduction f -> [(Rule f, Subst f)]
steps r = aux r []
  where
    aux (Step r sub) = ((r, sub):)
    aux (Trans p q) = aux p . aux q
    aux (Parallel ps _) = foldr (.) id (map (aux . snd) ps)

--------------------------------------------------------------------------------
-- Extra-fast rewriting, without proof output or unorientable rules.
--------------------------------------------------------------------------------

-- Compute the normal form of a term wrt only oriented rules.
simplify :: Function f => Index (Rule f) -> Term f -> Term f
simplify idx t
  | t == u = t
  | otherwise = simplify idx u
  where
    u = build (simp (singleton t))

    simp Empty = mempty
    simp (Cons (Var x) t) = var x `mappend` simp t
    simp (Cons t u)
      | ((rule, sub):_) <- rewrite t =
          Term.subst sub (rhs rule) `mappend` simp u
    simp (Cons (App f ts) us) =
      app f (simp ts) `mappend` simp us

    rewrite t = do
      rule <- Index.matches t idx
      guard (oriented (orientation rule))
      sub <- maybeToList (match (lhs rule) t)
      guard (reducesOriented rule sub)
      return (rule, sub)

--------------------------------------------------------------------------------
-- Strategy combinators.
--------------------------------------------------------------------------------

-- Normalise a term wrt a particular strategy.
{-# INLINE normaliseWith #-}
normaliseWith :: PrettyTerm f => Strategy f -> Term f -> Reduction f
normaliseWith strat t = stamp (describe res) res
  where
    describe (Parallel [] _) = "normalising terms (already in normal form)"
    describe _ = "normalising terms (not in normal form)"

    res = aux 0 (Parallel [] t)
    aux 1000 p =
      ERROR("Possibly nonterminating rewrite:\n" ++
            prettyShow p)
    aux n p =
      case anywhere1 strat (singleton t) of
        [] -> p
        rs -> aux (n+1) (p `Trans` Parallel rs t)
      where t = result p

-- Compute all normal forms of a term wrt a particular strategy.
normalForms :: Function f => Strategy f -> [Term f] -> Set (Term f)
normalForms strat ts = stamp "computing all normal forms" $ go Set.empty Set.empty ts
  where
    go _ norm [] = norm
    go dead norm (t:ts)
      | t `Set.member` dead = go dead norm ts
      | t `Set.member` norm = go dead norm ts
      | null us = go dead (Set.insert t norm) ts
      | otherwise =
        go (Set.insert t dead) norm (us ++ ts)
      where
        us = map result (anywhere strat t)

-- Apply a strategy anywhere in a term.
anywhere :: Strategy f -> Strategy f
anywhere strat t = aux 0 (singleton t)
  where
    aux !_ Empty = []
    aux n (Cons Var{} u) = aux (n+1) u
    aux n (ConsSym u v) =
      [Parallel [(n,p)] t | p <- strat u] ++ aux (n+1) v

-- Apply a strategy to all children of the root function.
nested :: Strategy f -> Strategy f
nested strat t = [Parallel [(1,p)] t | p <- aux 0 (children t)]
  where
    aux !_ Empty = []
    aux n (Cons Var{} u) = aux (n+1) u
    aux n (Cons u v) =
      [Parallel [(n,p)] t | p <- strat u] ++ aux (n+len t) v

-- A version of 'anywhere' which does parallel reduction.
{-# INLINE anywhere1 #-}
anywhere1 :: PrettyTerm f => Strategy f -> TermList f -> [(Int, Reduction f)]
anywhere1 strat t = aux [] 0 t
  where
    aux _ !_ !_ | False = __
    aux ps _ Empty = reverse ps
    aux ps n (Cons (Var _) t) = aux ps (n+1) t
    aux ps n (Cons t u) | q:_ <- strat t =
      aux ((n, q):ps) (n+len t) u
    aux ps n (ConsSym _ t) =
      aux ps (n+1) t

--------------------------------------------------------------------------------
-- Basic strategies. These only apply at the root of the term.
--------------------------------------------------------------------------------

-- A strategy which rewrites using an index.
{-# INLINE rewrite #-}
rewrite :: Function f => String -> (Rule f -> Subst f -> Bool) -> Index (Rule f) -> Strategy f
rewrite _phase p rules t = do
  rule <- Index.matches t rules
  tryRule p rule t

-- A strategy which applies one rule only.
tryRule :: Function f => (Rule f -> Subst f -> Bool) -> Rule f -> Strategy f
tryRule p rule t = do
  sub <- maybeToList (match (lhs rule) t)
  guard (p rule sub)
  return (Step rule sub)

-- Check if a rule can be applied, given an ordering <= on terms.
reducesWith :: Function f => (Term f -> Term f -> Bool) -> Rule f -> Subst f -> Bool
reducesWith _ (Rule (Oriented ts) _ _) sub =
  -- Be a bit careful here not to build new terms
  -- (reducesWith is used in simplify).
  -- This is the same as:
  --   any (not . isMinimal) (subst sub ts)
  any (not . isMinimal . expand) ts
  where
    expand t@(Var x) = fromMaybe t (Term.lookup x sub)
    expand t = t
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
reduces :: Function f => Rule f -> Subst f -> Bool
reduces rule sub = reducesWith lessEq rule sub

-- Check if a rule can be applied and is oriented.
reducesOriented :: Function f => Rule f -> Subst f -> Bool
reducesOriented rule sub =
  oriented (orientation rule) && reducesWith undefined rule sub

-- Check if a rule can be applied in various circumstances.
reducesInModel :: Function f => Model f -> Rule f -> Subst f -> Bool
reducesInModel cond rule sub =
  reducesWith (\t u -> isJust (lessIn cond t u)) rule sub

reducesSkolem :: Function f => Rule f -> Subst f -> Bool
reducesSkolem rule sub =
  reducesWith (\t u -> lessEq (subst skolemise t) (subst skolemise u)) rule sub
  where
    skolemise = con . skolem

reducesSub :: Function f => Term f -> Rule f -> Subst f -> Bool
reducesSub top rule sub =
  reducesSkolem rule sub && lessEq u top && isNothing (unify u top)
  where
    u = subst sub (rhs rule)
