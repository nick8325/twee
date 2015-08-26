{-# LANGUAGE TypeFamilies, StandaloneDeriving, FlexibleContexts, UndecidableInstances, PartialTypeSignatures #-}
module KBC.Rewrite where

import KBC.Base
import KBC.Constraints
import qualified KBC.Index as Index
import KBC.Index(Index)
import KBC.Term
import Data.Rewriting.Rule
import Control.Monad
import Data.Maybe

data Oriented a = MkOriented { orientation :: Orientation (ConstantOf a), rule :: a }
deriving instance (Eq (ConstantOf a), Eq a) => Eq (Oriented a)
deriving instance (Ord (ConstantOf a), Ord a) => Ord (Oriented a)
deriving instance (Show (ConstantOf a), Show a) => Show (Oriented a)
data Orientation f = Oriented | WeaklyOriented [Tm f] | Unoriented deriving (Eq, Ord, Show)

instance Symbolic a => Symbolic (Oriented a) where
  type ConstantOf (Oriented a) = ConstantOf a
  termsDL = termsDL . rule
  substf sub (MkOriented Oriented x) = MkOriented Oriented (substf sub x)
  substf sub (MkOriented (WeaklyOriented ts) x) = MkOriented (WeaklyOriented (map (substf sub) ts)) (substf sub x)
  substf sub (MkOriented Unoriented x) = MkOriented Unoriented (substf sub x)

instance (PrettyTerm (ConstantOf a), Pretty a) => Pretty (Oriented a) where
  pPrint (MkOriented Oriented x) = pPrint x
  pPrint (MkOriented (WeaklyOriented ts) x) = pPrint x <+> text "(weak on" <+> pPrint ts <> text ")"
  pPrint (MkOriented Unoriented x) = pPrint x <+> text "(unoriented)"

type Strategy f = Tm f -> [Reduction f]

data Reduction f =
  Reduction {
    result :: Tm f,
    proof  :: Proof f }
  deriving Show

data Proof f =
    Refl
  | Step (Oriented (Rule f Var))
  | Trans (Proof f) (Proof f)
  | Parallel f [Proof f]
  deriving Show

steps :: Reduction f -> [Oriented (Rule f Var)]
steps r = aux (proof r) []
  where
    aux Refl = id
    aux (Step r) = (r:)
    aux (Trans p q) = aux p . aux q
    aux (Parallel _ ps) = foldr (.) id (map aux ps)

refl :: Tm f -> Reduction f
refl t = Reduction t Refl

step :: Oriented (Rule f Var) -> Reduction f
step r = Reduction (rhs (rule r)) (Step r)

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

anywhere :: Strategy f -> Strategy f
anywhere strat t = strat t ++ nested (anywhere strat) t

nested _ Var{} = []
nested strat (Fun f xs) =
  [ parallel f $
      map refl (take (i-1) xs) ++ [p] ++ map refl (drop i xs)
  | (i, x) <- zip [0..] xs,
    p <- strat x ]

allowedInModel :: (Ord f, Sized f, Minimal f, PrettyTerm f) =>
  [Formula f] -> Oriented (Rule f Var) -> Bool
allowedInModel _ (MkOriented Oriented _) = True
allowedInModel _ (MkOriented (WeaklyOriented xs) _) =
  or [x /= minimalTerm | x <- xs]
allowedInModel cond (MkOriented Unoriented (Rule t u)) =
  lessEqIn cond u t && t /= u

allowedSkolem :: (Ord f, Sized f, Minimal f, PrettyTerm f) =>
  Oriented (Rule f Var) -> Bool
allowedSkolem (MkOriented Oriented _) = True
allowedSkolem (MkOriented (WeaklyOriented xs) _) =
  or [x /= minimalTerm | x <- xs]
allowedSkolem (MkOriented Unoriented (Rule t u)) =
  lessEq (skolemise u) (skolemise t) && t /= u

allowedSub :: (Ord f, Numbered f, Sized f, Minimal f, PrettyTerm f) =>
  Tm f -> Oriented (Rule f Var) -> Bool
allowedSub top orule =
  allowedSkolem orule && lessEq u top && isNothing (unify u top)
  where
    u = rhs (rule orule)

rewriteInModel :: (Ord f, Numbered f, Sized f, Minimal f, PrettyTerm f) =>
  Index (Oriented (Rule f Var)) -> [Formula f] -> Strategy f
rewriteInModel rules model t = do
  orule <- Index.lookup t rules
  guard (allowedInModel model orule)
  return (step orule)

rewriteSub :: (Ord f, Numbered f, Sized f, Minimal f, PrettyTerm f) =>
  Index (Oriented (Rule f Var)) -> Tm f -> Strategy f
rewriteSub rules top t = do
  orule <- Index.lookup t rules
  guard (allowedSub top orule)
  return (step orule)

simplify :: (PrettyTerm f, Numbered f, Sized f, Minimal f, Ord f) => Index (Oriented (Rule f Var)) -> Strategy f
simplify rules t = do
  orule <- Index.lookup t rules
  case orientation orule of
    Oriented -> return ()
    WeaklyOriented ts -> guard (or [ t /= minimalTerm | t <- ts ])
    Unoriented -> mzero
  return (step orule)

rewrite :: (PrettyTerm f, Numbered f, Sized f, Minimal f, Ord f) => Index (Oriented (Rule f Var)) -> Strategy f
rewrite rules t = do
  orule <- Index.lookup t rules
  case orientation orule of
    Oriented -> return ()
    WeaklyOriented ts -> guard (or [ t /= minimalTerm | t <- ts ])
    Unoriented -> guard (lessEq (rhs (rule orule)) (lhs (rule orule)) && rhs (rule orule) /= lhs (rule orule))
  return (step orule)

tryRule :: (Ord f, Sized f, Minimal f) => Oriented (Rule f Var) -> Strategy f
tryRule orule t = do
  sub <- maybeToList (match (lhs (rule orule)) t)
  let orule' = substf (evalSubst sub) orule
  case orientation orule' of
    Oriented -> return ()
    WeaklyOriented ts -> guard (or [ t /= minimalTerm | t <- ts ])
    Unoriented -> guard (lessEq (rhs (rule orule')) (lhs (rule orule')) && rhs (rule orule') /= lhs (rule orule'))
  return (step orule')

tryRuleInModel :: (Ord f, Sized f, Minimal f, PrettyTerm f) => [Formula f] -> Oriented (Rule f Var) -> Strategy f
tryRuleInModel model orule t = do
  sub <- maybeToList (match (lhs (rule orule)) t)
  let orule' = substf (evalSubst sub) orule
  guard (allowedInModel model orule')
  return (step orule')
