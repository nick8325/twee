{-# LANGUAGE TypeFamilies, StandaloneDeriving, FlexibleContexts, UndecidableInstances, PartialTypeSignatures, RecordWildCards, PatternGuards #-}
module KBC.Rule where

import KBC.Base
import KBC.Constraints
import qualified KBC.Index as Index
import KBC.Index(Index)
import Control.Monad
import Data.Maybe
import Data.List
import KBC.Utils
import qualified Data.Map.Strict as Map
import qualified Data.Rewriting.Substitution.Type as Subst
import qualified Data.Set as Set
import Data.Set(Set)

--------------------------------------------------------------------------------
-- Rewrite rules.
--------------------------------------------------------------------------------

data Rule f =
  Rule {
    orientation :: Orientation f,
    lhs :: Tm f,
    rhs :: Tm f }
  deriving (Eq, Ord, Show)

data Orientation f =
    Oriented
  | WeaklyOriented [Tm f]
  | Permutative [(Tm f, Tm f)]
  | Unoriented deriving (Eq, Ord, Show)

instance Symbolic (Rule f) where
  type ConstantOf (Rule f) = f
  termsDL Rule{..} = termsDL lhs `mplus` termsDL rhs
  substf sub (Rule or l r) = Rule (substf sub or) (substf sub l) (substf sub r)

instance Symbolic (Orientation f) where
  type ConstantOf (Orientation f) = f
  termsDL Oriented = mzero
  termsDL (WeaklyOriented ts) = msum (map termsDL ts)
  termsDL (Permutative ts) = msum (map termsDL ts)
  termsDL Unoriented = mzero
  substf sub Oriented = Oriented
  substf sub (WeaklyOriented ts) = WeaklyOriented (map (substf sub) ts)
  substf sub (Permutative ts) = Permutative (map (substf sub) ts)
  substf sub Unoriented = Unoriented

instance PrettyTerm f => Pretty (Rule f) where
  pPrint (Rule Oriented l r) = pPrintRule l r
  pPrint (Rule (WeaklyOriented ts) l r) = pPrintRule l r <+> text "(weak on" <+> pPrint ts <> text ")"
  pPrint (Rule (Permutative ts) l r) = pPrintRule l r <+> text "(permutative on" <+> pPrint ts <> text ")"
  pPrint (Rule Unoriented l r) = pPrintRule l r <+> text "(unoriented)"

pPrintRule :: PrettyTerm f => Tm f -> Tm f -> Doc
pPrintRule l r = hang (pPrint l <+> text "->") 2 (pPrint r)

--------------------------------------------------------------------------------
-- Equations.
--------------------------------------------------------------------------------

data Equation f = Tm f :=: Tm f deriving (Eq, Ord, Show)
type EquationOf a = Equation (ConstantOf a)

instance Symbolic (Equation f) where
  type ConstantOf (Equation f) = f
  termsDL (t :=: u) = termsDL t `mplus` termsDL u
  substf sub (t :=: u) = substf sub t :=: substf sub u

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
  [ Rule (WeaklyOriented (map Var ls)) l l' | not (null ls), ord /= Just GT ] ++
  [ Rule (WeaklyOriented (map Var rs)) r r' | not (null rs), ord /= Just LT ]
  where
    ord = orientTerms l' r'
    l' = erase ls l
    r' = erase rs r
    ls = usort (vars l) \\ usort (vars r)
    rs = usort (vars r) \\ usort (vars l)

    erase [] t = t
    erase xs t = substf (\x -> if x `elem` xs then Fun minimal [] else Var x) t

    rule t u = Rule o t u
      where
        o | lessEq u t =
            case unify t u of
              Nothing -> Oriented
              Just sub
                | all (== minimalTerm) (Map.elems (Subst.toMap sub)) ->
                  WeaklyOriented (map Var (Map.keys (Subst.toMap sub)))
                | otherwise -> Unoriented
          | sort (vars t) == sort (vars u),
            Just ts <- makePermutative t u =
            Permutative (reduce (filter (uncurry (/=)) ts))
          | otherwise = Unoriented

    makePermutative (Var x) (Var y) = Just [(Var x, Var y)]
    makePermutative (Fun f ts) (Fun g us) | f == g =
      fmap concat (zipWithM makePermutative ts us)
    makePermutative _ _ = Nothing
    reduce [] = []
    reduce ((x,y):xs)
      | x == y = reduce xs
      | otherwise = (x,y):reduce (substf (\z -> if Var z == y then x else Var z) xs)

bothSides :: (Tm f -> Tm f') -> Equation f -> Equation f'
bothSides f (t :=: u) = f t :=: f u

trivial :: Eq f => Equation f -> Bool
trivial (t :=: u) = t == u

--------------------------------------------------------------------------------
-- Rewriting.
--------------------------------------------------------------------------------

type Strategy f = Tm f -> [Reduction f]

data Reduction f =
  Reduction {
    result :: Tm f,
    proof  :: Proof f }
  deriving Show

instance PrettyTerm f => Pretty (Reduction f) where
  pPrint Reduction{..} = hang (pPrint result <+> text "by") 2 (pPrint proof)

data Proof f =
    Refl
  | Step (Rule f)
  | Trans (Proof f) (Proof f)
  | Parallel f [Proof f]
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

refl :: Tm f -> Reduction f
refl t = Reduction t Refl

step :: Rule f -> Reduction f
step r = Reduction (rhs r) (Step r)

trans :: Reduction f -> Reduction f -> Reduction f
trans ~(Reduction _ p) (Reduction t q) = Reduction t (p `Trans` q)

parallel :: f -> [Reduction f] -> Reduction f
parallel f rs =
  Reduction
    (Fun f (map result rs))
    (Parallel f (map proof rs))

normaliseWith :: PrettyTerm f => Strategy f -> Tm f -> Reduction f
normaliseWith strat t =
  case strat t of
    p:_ -> continue p
    [] ->
      case t of
        Fun f ts | not (all (null . steps) ns) ->
          continue (parallel f ns)
          where
            ns = map (normaliseWith strat) ts
        _ -> refl t
  where
    continue p = p `trans` normaliseWith strat (result p)

normalForms :: Function f => Strategy f -> [Tm f] -> Set (Tm f)
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
anywhere strat t = strat t ++ nested (anywhere strat) t

nested _ Var{} = []
nested strat (Fun f xs) =
  [ parallel f $
      map refl (take i xs) ++ [p] ++ map refl (drop (i+1) xs)
  | (i, x) <- zip [0..] xs,
    p <- strat x ]

rewrite :: Function f => (Rule f -> Bool) -> Index (Rule f) -> Strategy f
rewrite p rules t = do
  rule <- Index.lookup t rules
  guard (p rule)
  return (step rule)

tryRule :: Function f => (Rule f -> Bool) -> Rule f -> Strategy f
tryRule p rule t = do
  sub <- maybeToList (match (lhs rule) t)
  let rule' = substf (evalSubst sub) rule
  guard (p rule')
  return (step rule')

simplifies :: Function f => Rule f -> Bool
simplifies (Rule Oriented _ _) = True
simplifies (Rule (WeaklyOriented ts) _ _) =
  or [ t /= minimalTerm | t <- ts ]
simplifies (Rule (Permutative _) _ _) = False
simplifies (Rule Unoriented _ _) = False

reducesWith :: Function f => (Tm f -> Tm f -> Bool) -> Rule f -> Bool
reducesWith _ (Rule Oriented _ _) = True
reducesWith _ (Rule (WeaklyOriented ts) _ _) =
  or [ t /= minimalTerm | t <- ts ]
reducesWith p (Rule (Permutative ts) _ _) =
  aux ts
  where
    aux [] = False
    aux ((t, u):ts)
      | t == u = aux ts
      | otherwise = p u t
reducesWith p (Rule Unoriented t u) =
  p u t && u /= t

reduces :: Function f => Rule f -> Bool
reduces rule = reducesWith lessEq rule

reducesInModel :: Function f => Model f -> Rule f -> Bool
reducesInModel cond rule = reducesWith (\t u -> isJust (lessIn cond t u)) rule

reducesSkolem :: Function f => Rule f -> Bool
reducesSkolem = reducesWith (\t u -> lessEq (skolemise t) (skolemise u))

reducesSub :: Function f => Tm f -> Rule f -> Bool
reducesSub top rule =
  reducesSkolem rule && lessEq u top && isNothing (unify u top)
  where
    u = rhs rule
