{-# LANGUAGE TypeFamilies, StandaloneDeriving, FlexibleContexts, UndecidableInstances, RecordWildCards, PatternGuards, CPP #-}
module KBC.Rule where

#include "errors.h"
import KBC.Base
import qualified KBC.Term.Nested as Nested
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
  deriving Show

data Orientation f =
    Oriented
  | WeaklyOriented [Nested.Term f]
  | Permutative [(Nested.Term f, Nested.Term f)]
  | Unoriented
  deriving Show

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

data Equation f = Term f :=: Term f deriving Show
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
  [ Rule (WeaklyOriented (map Nested.Var ls)) l l' | not (null ls), ord /= Just GT ] ++
  [ Rule (WeaklyOriented (map Nested.Var rs)) r r' | not (null rs), ord /= Just LT ]
  where
    ord = orientTerms l' r'
    l' = erase ls l
    r' = erase rs r
    ls = usort (vars l) \\ usort (vars r)
    rs = usort (vars r) \\ usort (vars l)

    erase [] t = t
    erase xs t = subst sub t
      where
        sub = Nested.flattenSubst [(x, minimalTerm) | x <- xs]

    rule t u = Rule o t u
      where
        o | lessEq u t =
            case unify t u of
              Nothing -> Oriented
              Just sub
                | allSubst (\_ (Cons t Empty) -> isMinimal t) sub ->
                  WeaklyOriented (map (Nested.Var . fst) (substToList sub))
                | otherwise -> Unoriented
          | Just ts <- evalStateT (makePermutative t u) [] =
            Permutative ts
          | otherwise = Unoriented

    makePermutative t u = do
      sub <- gets Nested.flattenSubst
      aux (subst sub t) (subst sub u)
        where
          aux (Var x) (Var y)
            | x == y = return []
            | otherwise = do
              modify ((x, Nested.Var y):)
              return [(Nested.Var x, Nested.Var y)]

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
  Reduction {
    result :: Nested.Term f,
    proof  :: Proof f }
  deriving Show

instance PrettyTerm f => Pretty (Reduction f) where
  pPrint Reduction{..} = hang (pPrint result <+> text "by") 2 (pPrint proof)

data Proof f =
    Refl
  | Step (Rule f)
  | Trans (Proof f) (Proof f)
  | Parallel (Fun f) [Proof f]
  deriving Show

instance PrettyTerm f => Pretty (Proof f) where
  pPrint Refl = text "_"
  pPrint (Step rule) = pPrint rule
  pPrint (Trans p q) = hang (pPrint p <+> text "then") 2 (pPrint q)
  pPrint (Parallel f ps) =
    pPrint f <> parens (sep (punctuate (text ",") (map pPrint ps)))

steps :: Reduction f -> [Rule f]
steps r = aux (proof r) []
  where
    aux Refl = id
    aux (Step r) = (r:)
    aux (Trans p q) = aux p . aux q
    aux (Parallel _ ps) = foldr (.) id (map aux ps)

refl :: Term f -> Reduction f
refl t = Reduction (Nested.Flat t) Refl

step :: Rule f -> Reduction f
step r = Reduction (Nested.Flat (rhs r)) (Step r)

trans :: Reduction f -> Reduction f -> Reduction f
trans ~(Reduction _ p) (Reduction t q) = Reduction t (p `Trans` q)

parallel :: Fun f -> [Reduction f] -> Reduction f
parallel f rs =
  Reduction
    (Nested.Fun f (map result rs))
    (Parallel f (map proof rs))

normaliseWith :: PrettyTerm f => Strategy f -> Term f -> Reduction f
normaliseWith strat t =
  case strat t of
    p:_ -> continue p
    [] ->
      case t of
        Fun f ts | not (all (null . steps) ns) ->
          continue (parallel f ns)
          where
            ns = map (normaliseWith strat) (fromTermList ts)
        _ -> refl t
  where
    continue p = p `trans` normaliseWith strat (Nested.flatten (result p))

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
        us = map (Nested.flatten . result) (anywhere strat t)

anywhere :: Strategy f -> Strategy f
anywhere strat t = strat t ++ nested (anywhere strat) t

nested _ Var{} = []
nested strat (Fun f xs) =
  [ parallel f $
      map refl (take i ys) ++ [p] ++ map refl (drop (i+1) ys)
  | (i, x) <- zip [0..] ys,
    p <- strat x ]
  where
    ys = fromTermList xs

{-# INLINE rewrite #-}
rewrite :: Function f => (Rule f -> Bool) -> Frozen (Rule f) -> Strategy f
rewrite p rules t = do
  rule <- Index.lookup t rules
  guard (p rule)
  return (step rule)

tryRule :: Function f => (Rule f -> Bool) -> Rule f -> Strategy f
tryRule p rule t = do
  sub <- maybeToList (match (lhs rule) t)
  let rule' = subst sub rule
  guard (p rule')
  return (step rule')

simplifies :: Function f => Rule f -> Bool
simplifies (Rule Oriented _ _) = True
simplifies (Rule (WeaklyOriented ts) _ _) =
  or [ not (isMinimal (Nested.flatten t)) | t <- ts ]
simplifies (Rule (Permutative _) _ _) = False
simplifies (Rule Unoriented _ _) = False

reducesWith :: Function f => (Term f -> Term f -> Bool) -> Rule f -> Bool
reducesWith _ (Rule Oriented _ _) = True
reducesWith _ (Rule (WeaklyOriented ts) _ _) =
  or [ not (isMinimal (Nested.flatten t)) | t <- ts ]
reducesWith p (Rule (Permutative ts) _ _) =
  aux ts
  where
    aux [] = False
    aux ((t, u):ts)
      | t' == u' = aux ts
      | otherwise = p u' t'
      where
        t' = Nested.flatten t
        u' = Nested.flatten u
reducesWith p (Rule Unoriented t u) =
  p u t && u /= t

reduces :: Function f => Rule f -> Bool
reduces rule = reducesWith lessEq rule

reducesInModel :: Function f => Model f -> Rule f -> Bool
reducesInModel cond rule = reducesWith (\t u -> isJust (lessIn cond t u)) rule

reducesSkolem :: Function f => Rule f -> Bool
reducesSkolem = reducesWith (\t u -> lessEq (subst (skolemise t) t) (subst (skolemise u) u))

reducesSub :: Function f => Term f -> Rule f -> Bool
reducesSub top rule =
  reducesSkolem rule && lessEq u top && isNothing (unify u top)
  where
    u = rhs rule
