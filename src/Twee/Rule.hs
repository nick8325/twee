{-# LANGUAGE TypeFamilies, StandaloneDeriving, FlexibleContexts, UndecidableInstances, RecordWildCards, PatternGuards, CPP, BangPatterns #-}
module Twee.Rule where

#include "errors.h"
import Twee.Base
import Twee.Constraints
import qualified Twee.Index as Index
import Twee.Index(Frozen)
import Control.Monad
import Control.Monad.Trans.Class
import Control.Monad.Trans.State.Strict
import Data.Maybe
import Data.List
import Twee.Utils
import qualified Data.Set as Set
import Data.Set(Set)
import qualified Twee.Term as Term

--------------------------------------------------------------------------------
-- Rewrite rules.
--------------------------------------------------------------------------------

data Rule f =
  Rule {
    orientation :: Orientation f,
    lhs :: Term f,
    rhs :: Term f }
  deriving (Eq, Ord, Show)

data Orientation f =
    Oriented
  | WeaklyOriented [Term f]
  | Permutative [(Term f, Term f)]
  | Unoriented
  deriving Show

instance Eq (Orientation f) where _ == _ = True
instance Ord (Orientation f) where compare _ _ = EQ

oriented :: Orientation f -> Bool
oriented Oriented = True
oriented (WeaklyOriented _) = True
oriented _ = False

instance Symbolic (Rule f) where
  type ConstantOf (Rule f) = f
  term = lhs
  termsDL Rule{..} = termsDL (lhs, (rhs, orientation))
  replace f (Rule or l r) = Rule (replace f or) (replace f l) (replace f r)

instance Symbolic (Orientation f) where
  type ConstantOf (Orientation f) = f
  term = __
  termsDL Oriented = mempty
  termsDL (WeaklyOriented ts) = termsDL ts
  termsDL (Permutative ts) = termsDL ts
  termsDL Unoriented = mempty
  replace _ Oriented = Oriented
  replace f (WeaklyOriented ts) = WeaklyOriented (replace f ts)
  replace f (Permutative ts) = Permutative (replace f ts)
  replace _ Unoriented = Unoriented

instance (Numbered f, PrettyTerm f) => Pretty (Rule f) where
  pPrint (Rule Oriented l r) = pPrintRule l r
  pPrint (Rule (WeaklyOriented ts) l r) = pPrintRule l r <+> text "(weak on" <+> pPrint ts <> text ")"
  pPrint (Rule (Permutative ts) l r) = pPrintRule l r <+> text "(permutative on" <+> pPrint ts <> text ")"
  pPrint (Rule Unoriented l r) = pPrintRule l r <+> text "(unoriented)"

pPrintRule :: (Numbered f, PrettyTerm f) => Term f -> Term f -> Doc
pPrintRule l r = hang (pPrint l <+> text "->") 2 (pPrint r)

--------------------------------------------------------------------------------
-- Equations.
--------------------------------------------------------------------------------

data Equation f = Term f :=: Term f deriving (Eq, Ord, Show)
type EquationOf a = Equation (ConstantOf a)

instance Symbolic (Equation f) where
  type ConstantOf (Equation f) = f
  term = __
  termsDL (t :=: u) = termsDL (t, u)
  replace f (t :=: u) = replace f t :=: replace f u

instance (Numbered f, PrettyTerm f) => Pretty (Equation f) where
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
        sub = fromMaybe __ $ flattenSubst [(x, minimalTerm) | x <- xs]

rule :: Function f => Term f -> Term f -> Rule f
rule t u = Rule o t u
  where
    o | lessEq u t =
        case unify t u of
          Nothing -> Oriented
          Just sub
            | allSubst (\_ (Cons t Empty) -> isMinimal t) sub ->
              WeaklyOriented (map (build . var . fst) (listSubst sub))
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

          aux (Fun f ts) (Fun g us)
            | f == g =
              fmap concat (zipWithM makePermutative (fromTermList ts) (fromTermList us))

          aux _ _ = mzero

bothSides :: (Term f -> Term f') -> Equation f -> Equation f'
bothSides f (t :=: u) = f t :=: f u

trivial :: Eq f => Equation f -> Bool
trivial (t :=: u) = t == u

instance (Sized f, Numbered f) => Sized (Equation f) where
  size (t :=: u) = size t + size u

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
result t = build (emitReduction t)
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
    emitParallel n ps (Cons (Fun f t) u) =
      fun f (emitParallel (n+1) ps t) `mappend`
      emitParallel (n + 1 + lenList t) ps u

instance (Numbered f, PrettyTerm f) => Pretty (Reduction f) where
  pPrint = pPrintReduction

pPrintReduction :: (Numbered f, PrettyTerm f) => Reduction f -> Doc
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

steps :: Reduction f -> [(Rule f, Subst f)]
steps r = aux r []
  where
    aux (Step r sub) = ((r, sub):)
    aux (Trans p q) = aux p . aux q
    aux (Parallel ps _) = foldr (.) id (map (aux . snd) ps)

normaliseWith :: (Numbered f, PrettyTerm f) => Strategy f -> Term f -> Reduction f
normaliseWith strat t = aux 0 [] 0 (singleton t) (Parallel [] t) t
  where
    aux !_ _ !_ !_ _ !_ | False = __
    aux 1000 _ _ _ p _ =
      ERROR("Possibly nonterminating rewrite:\n" ++
            prettyShow p)
    aux _ [] _ Empty p _ = p
    aux n ps _ Empty p t =
      let q = Parallel (reverse ps) t
          u = result q
      in aux (n+1) [] 0 (singleton u) (p `Trans` q) u
    aux m ps n (Cons (Var _) t) p u = aux m ps (n+1) t p u
    aux m ps n (Cons t u) p v | q:_ <- strat t =
      aux m ((n, q):ps) (n+len t) u p v
    aux m ps n (ConsSym (Fun _ _) t) p u =
      aux m ps (n+1) t p u

normalForms :: Function f => Strategy f -> [Term f] -> Set (Term f)
normalForms strat ts = go Set.empty Set.empty ts
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
rewrite _phase p rules t = do
  Index.Match rule sub <- Index.matches t rules
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
reducesSkolem = reducesWith (\t u -> lessEq (subst skolemise t) (subst skolemise u))
  where
    skolemise = con . skolem

reducesSub :: Function f => Term f -> Rule f -> Subst f -> Bool
reducesSub top rule sub =
  reducesSkolem rule sub && lessEq u top && isNothing (unify u top)
  where
    u = subst sub (rhs rule)
