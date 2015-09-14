{-# LANGUAGE TypeFamilies, StandaloneDeriving, FlexibleContexts, UndecidableInstances, RecordWildCards, PatternGuards, CPP, BangPatterns #-}
module KBC.Rule where

#include "errors.h"
import KBC.Base
import KBC.Constraints
import qualified KBC.Index as Index
import KBC.Index(Frozen)
import Control.Monad
import Control.Monad.Trans.State.Strict
import Data.Maybe
import Data.List
import KBC.Utils
import qualified Data.Set as Set
import Data.Set(Set)
import Data.Monoid hiding ((<>))

--------------------------------------------------------------------------------
-- Rewrite rules.
--------------------------------------------------------------------------------

data Rule f =
  Rule {
    orientation :: Orientation f,
    lhs :: Term f,
    rhs :: Term f }
  deriving (Eq, Show)

data Orientation f =
    Oriented
  | WeaklyOriented [Term f]
  | Permutative [(Term f, Term f)]
  | Unoriented
  deriving Show

instance Eq (Orientation f) where _ == _ = True

instance Symbolic (Rule f) where
  type ConstantOf (Rule f) = f
  term = lhs
  symbols fun var Rule{..} = symbols fun var (lhs, (rhs, orientation))
  subst sub (Rule or l r) = Rule (subst sub or) (subst sub l) (subst sub r)

instance Symbolic (Orientation f) where
  type ConstantOf (Orientation f) = f
  term = __
  symbols _ _ Oriented = mempty
  symbols fun var (WeaklyOriented ts) = symbols fun var ts
  symbols fun var (Permutative ts) = symbols fun var ts
  symbols _ _ Unoriented = mempty
  subst sub Oriented = Oriented
  subst sub (WeaklyOriented ts) = WeaklyOriented (subst sub ts)
  subst sub (Permutative ts) = Permutative (subst sub ts)
  subst sub Unoriented = Unoriented

instance PrettyTerm f => Pretty (Rule f) where
  pPrint (Rule Oriented l r) = pPrintRule l r
  pPrint (Rule (WeaklyOriented ts) l r) = pPrintRule l r <+> text "(weak on" <+> pPrint ts <> text ")"
  pPrint (Rule (Permutative ts) l r) = pPrintRule l r <+> text "(permutative on" <+> pPrint ts <> text ")"
  pPrint (Rule Unoriented l r) = pPrintRule l r <+> text "(unoriented)"

pPrintRule :: PrettyTerm f => Term f -> Term f -> Doc
pPrintRule l r = hang (pPrint l <+> text "->") 2 (pPrint r)

--------------------------------------------------------------------------------
-- Equations.
--------------------------------------------------------------------------------

data Equation f = Term f :=: Term f deriving (Eq, Ord, Show)
type EquationOf a = Equation (ConstantOf a)

instance Symbolic (Equation f) where
  type ConstantOf (Equation f) = f
  term = __
  symbols fun var (t :=: u) = symbols fun var (t, u)
  subst sub (t :=: u) = subst sub t :=: subst sub u

instance PrettyTerm f => Pretty (Equation f) where
  pPrint (x :=: y) = hang (pPrint x <+> text "=") 2 (pPrint y)

order :: Function f => Equation f -> Equation f
order (l :=: r)
  | l == r = l :=: r
  | otherwise =
    case compare (size l) (size r) of
      LT -> r :=: l
      GT -> l :=: r
      EQ -> if lessEq l r then r :=: l else l :=: r

unorient :: Rule f -> Equation f
unorient (Rule _ l r) = l :=: r

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
        sub = flattenSubst [(x, minimalTerm) | x <- xs]

rule :: Function f => Term f -> Term f -> Rule f
rule t u = Rule o t u
  where
    o | lessEq u t =
        case unify t u of
          Nothing -> Oriented
          Just sub
            | allSubst (\_ (Cons t Empty) -> isMinimal t) sub ->
              WeaklyOriented (map (var . fst) (substToList sub))
            | otherwise -> Unoriented
      | lessEq t u = ERROR("wrongly-oriented rule")
      | not (null (usort (vars u) \\ usort (vars t))) =
        ERROR("unbound variables in rule")
      | Just ts <- evalStateT (makePermutative t u) [] =
        Permutative ts
      | otherwise = Unoriented

    makePermutative t u = do
      sub <- gets flattenSubst
      aux (subst sub t) (subst sub u)
        where
          aux (Var x) (Var y)
            | x == y = return []
            | otherwise = do
              modify ((x, var y):)
              return [(var x, var y)]

          aux (Fun f ts) (Fun g us)
            | f == g &&
              sort (vars ts) `isSubsequenceOf` sort (vars us) =
              fmap concat (zipWithM makePermutative (fromTermList ts) (fromTermList us))

          aux _ _ = mzero

bothSides :: (Term f -> Term f') -> Equation f -> Equation f'
bothSides f (t :=: u) = f t :=: f u

trivial :: Eq f => Equation f -> Bool
trivial (t :=: u) = t == u

--------------------------------------------------------------------------------
-- Rewriting.
--------------------------------------------------------------------------------

type Strategy f = Term f -> [Reduction f]

data Reduction f =
    Step (Rule f) (Subst f)
  | Trans (Reduction f) (Reduction f)
  | Parallel [(Int, Reduction f)] (Term f)
  deriving Show

result :: Reduction f -> Term f
result t = buildTerm 32 (emitReduction t)
  where
    emitReduction (Step r sub) = emitSubst sub (rhs r)
    emitReduction (Trans _ p) = emitReduction p
    emitReduction (Parallel ps t) = emitParallel 0 ps (singleton t)

    emitParallel !_ _ _ | False = __
    emitParallel _ _ Empty = return ()
    emitParallel _ [] t = emitTermList t
    emitParallel n ((m, _):_) t  | m >= n + lenList t = emitTermList t
    emitParallel n ps@((m, _):_) (Cons t u) | m >= n + len t = do
      emitTerm t
      emitParallel (n + len t) ps u
    emitParallel n ((m, _):ps) t | m < n = emitParallel n ps t
    emitParallel n ((m, p):ps) (Cons t u) | m == n = do
      emitReduction p
      emitParallel (n + len t) ps u
    emitParallel n ps (Cons (Var x) u) = do
      emitVar x
      emitParallel (n + 1) ps u
    emitParallel n ps (Cons (Fun f t) u) = do
      emitFun f (emitParallel (n+1) ps t)
      emitParallel (n + 1 + lenList t) ps u

instance PrettyTerm f => Pretty (Reduction f) where
  pPrint (Step rule sub) = pPrint (subst sub rule)
  pPrint (Trans p q) = hang (pPrint p <+> text "then") 2 (pPrint q)
  pPrint (Parallel ps t) =
    pPrint [pPrint n <> text ":" <> pPrint r | (n, r) <- ps] <+> text "in" <+> pPrint t <+> text "to" <+> pPrint (result (Parallel ps t))

steps :: Reduction f -> [(Rule f, Subst f)]
steps r = aux r []
  where
    aux (Step r sub) = ((r, sub):)
    aux (Trans p q) = aux p . aux q
    aux (Parallel ps _) = foldr (.) id (map (aux . snd) ps)

normaliseWith :: PrettyTerm f => Strategy f -> Term f -> Reduction f
normaliseWith strat t = {-# SCC normaliseWith #-} aux [] 0 (singleton t) t
  where
    aux _ !_ _ _ | False = __
    aux [] _ Empty t = Parallel [] t
    aux ps _ Empty t =
      let p = Parallel (reverse ps) t
          u = result p
      in p `Trans` aux [] 0 (singleton u) u
    aux ps n (Cons (Var _) t) u = aux ps (n+1) t u
    aux ps n (Cons t u) v | p:_ <- strat t =
      aux ((n, p):ps) (n+len t) u v
    aux ps n (ConsSym (Fun _ _) t) u =
      aux ps (n+1) t u

normalForms :: Function f => Strategy f -> [Term f] -> Set (Term f)
normalForms strat ts = go Set.empty Set.empty ts
  where
    go dead norm [] = norm
    go dead norm (t:ts)
      | t `Set.member` dead = go dead norm ts
      | t `Set.member` norm = go dead norm ts
      | null us = go dead (Set.insert t norm) ts
      | otherwise =
        go (Set.insert t dead) norm (us ++ ts)
      where
        us = map result (anywhere strat t)

anywhere :: Strategy f -> Strategy f
anywhere strat t = aux 0 (singleton t)
  where
    aux !_ Empty = []
    aux n (Cons Var{} u) = aux (n+1) u
    aux n (ConsSym u v) =
      [Parallel [(n,p)] t | p <- strat u] ++ aux (n+1) v

nested :: Strategy f -> Strategy f
nested strat t = [Parallel [(1,p)] t | p <- aux 0 (children t)]
  where
    aux !_ Empty = []
    aux n (Cons Var{} u) = aux (n+1) u
    aux n (Cons u v) =
      [Parallel [(n,p)] t | p <- strat u] ++ aux (n+len t) v

{-# INLINE rewrite #-}
rewrite :: Function f => String -> (Rule f -> Subst f -> Bool) -> Frozen (Rule f) -> Strategy f
rewrite phase p rules t = do
  Index.Match rules sub <- Index.matches t rules
  rule <- rules
  guard (p rule sub)
  return (Step rule sub)

tryRule :: Function f => (Rule f -> Subst f -> Bool) -> Rule f -> Strategy f
tryRule p rule t = do
  sub <- maybeToList (match (lhs rule) t)
  guard (p rule sub)
  return (Step rule sub)

simplifies :: Function f => Rule f -> Subst f -> Bool
simplifies (Rule Oriented _ _) _ = True
simplifies (Rule (WeaklyOriented ts) _ _) sub =
  or [ not (isMinimal t) | t <- subst sub ts ]
simplifies (Rule (Permutative _) _ _) _ = False
simplifies (Rule Unoriented _ _) _ = False

reducesWith :: Function f => (Term f -> Term f -> Bool) -> Rule f -> Subst f -> Bool
reducesWith _ (Rule Oriented _ _) _ = True
reducesWith _ (Rule (WeaklyOriented ts) _ _) sub =
  or [ not (isMinimal t) | t <- subst sub ts ]
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

reduces :: Function f => Rule f -> Subst f -> Bool
reduces rule = reducesWith lessEq rule

reducesInModel :: Function f => Model f -> Rule f -> Subst f -> Bool
reducesInModel cond rule = reducesWith (\t u -> isJust (lessIn cond t u)) rule

reducesSkolem :: Function f => Rule f -> Subst f -> Bool
reducesSkolem = reducesWith (\t u -> lessEq (subst (skolemise t) t) (subst (skolemise u) u))

reducesSub :: Function f => Term f -> Rule f -> Subst f -> Bool
reducesSub top rule sub =
  reducesSkolem rule sub && lessEq u top && isNothing (unify u top)
  where
    u = subst sub (rhs rule)
