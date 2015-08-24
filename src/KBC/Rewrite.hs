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

data Oriented a = MkOriented { orientation :: Orientation (ConstantOf a) (VariableOf a), rule :: a }
deriving instance (Eq (ConstantOf a), Eq (VariableOf a), Eq a) => Eq (Oriented a)
deriving instance (Ord (ConstantOf a), Ord (VariableOf a), Ord a) => Ord (Oriented a)
deriving instance (Show (ConstantOf a), Show (VariableOf a), Show a) => Show (Oriented a)
data Orientation f v = Oriented | WeaklyOriented [Term f v] | Unoriented deriving (Eq, Ord, Show)

instance Symbolic a => Symbolic (Oriented a) where
  type VariableOf (Oriented a) = VariableOf a
  type ConstantOf (Oriented a) = ConstantOf a
  termsDL = termsDL . rule
  substf sub (MkOriented Oriented x) = MkOriented Oriented (substf sub x)
  substf sub (MkOriented (WeaklyOriented ts) x) = MkOriented (WeaklyOriented (map (substf sub) ts)) (substf sub x)
  substf sub (MkOriented Unoriented x) = MkOriented Unoriented (substf sub x)

instance (Pretty (VariableOf a), PrettyTerm (ConstantOf a), Pretty a) => Pretty (Oriented a) where
  pPrint (MkOriented Oriented x) = pPrint x
  pPrint (MkOriented (WeaklyOriented ts) x) = pPrint x <+> text "(weak on" <+> pPrint ts <> text ")"
  pPrint (MkOriented Unoriented x) = pPrint x <+> text "(unoriented)"

type Strategy f v = Tm f v -> [Oriented (Rule f v)]

data Reduction f v =
  Reduction {
    result :: Tm f v,
    steps  :: [Oriented (Rule f v)] }
  deriving Show

normaliseWith :: (PrettyTerm f, Pretty v) => Strategy f v -> Tm f v -> Reduction f v
normaliseWith strat t =
  aux [] t
  where
    aux rs t =
      case anywhere strat t of
        [] -> Reduction t (reverse rs)
        (r@(MkOriented _ (Rule _ u)):_) -> aux (r:rs) u

anywhere :: Strategy f v -> Strategy f v
anywhere strat t = strat t ++ nested (anywhere strat) t

nested :: Strategy f v -> Strategy f v
nested _ Var{} = []
nested strat (Fun f xs) =
  [ MkOriented orn (Rule (Fun f ts) (Fun f us))
  | (orn, ts, us) <- inner xs ]
  where
    inner [] = []
    inner (x:xs) =
      [ (orn, y:xs, z:xs)
      | MkOriented orn (Rule y z) <- strat x ] ++
      [ (orn, x:ys, x:zs) | (orn, ys, zs) <- inner xs ]

allowedInModel :: (Ord f, Ord v, Sized f, Minimal f, PrettyTerm f, Pretty v) =>
  [Formula f v] -> Oriented (Rule f v) -> Bool
allowedInModel _ (MkOriented Oriented _) = True
allowedInModel _ (MkOriented (WeaklyOriented xs) _) =
  or [x /= minimalTerm | x <- xs]
allowedInModel cond (MkOriented Unoriented (Rule t u)) =
  lessEqIn cond u t && t /= u

allowedSkolem :: (Ord f, Ord v, Sized f, Minimal f, PrettyTerm f, Pretty v, Numbered v) =>
  Oriented (Rule f v) -> Bool
allowedSkolem (MkOriented Oriented _) = True
allowedSkolem (MkOriented (WeaklyOriented xs) _) =
  or [x /= minimalTerm | x <- xs]
allowedSkolem (MkOriented Unoriented (Rule t u)) =
  lessEq (skolemise u) (skolemise t) && t /= u

allowedSub :: (Ord f, Ord v, Numbered f, Numbered v, Sized f, Minimal f, PrettyTerm f, Pretty v) =>
  Tm f v -> Oriented (Rule f v) -> Bool
allowedSub top orule =
  allowedSkolem orule && lessEq u top && isNothing (unify u top)
  where
    u = rhs (rule orule)

rewriteInModel :: (Ord f, Ord v, Numbered f, Numbered v, Sized f, Minimal f, PrettyTerm f, Pretty v) =>
  Index (Oriented (Rule f v)) -> [Formula f v] -> Tm f v -> [Oriented (Rule f v)]
rewriteInModel rules model t = do
  orule <- Index.lookup t rules
  guard (allowedInModel model orule)
  return orule

rewriteSub :: (Ord f, Ord v, Numbered f, Numbered v, Sized f, Minimal f, PrettyTerm f, Pretty v) =>
  Index (Oriented (Rule f v)) -> Tm f v -> Tm f v -> [Oriented (Rule f v)]
rewriteSub rules top t = do
  orule <- Index.lookup t rules
  guard (allowedSub top orule)
  return orule

simplify :: (PrettyTerm f, Pretty v, Numbered f, Sized f, Minimal f, Ord f, Numbered v, Ord v) => Index (Oriented (Rule f v)) -> Strategy f v
simplify rules t = do
  orule <- Index.lookup t rules
  case orientation orule of
    Oriented -> return ()
    WeaklyOriented ts -> guard (or [ t /= minimalTerm | t <- ts ])
    Unoriented -> mzero
  return orule

rewrite :: (PrettyTerm f, Pretty v, Numbered f, Sized f, Minimal f, Ord f, Numbered v, Ord v) => Index (Oriented (Rule f v)) -> Strategy f v
rewrite rules t = do
  orule <- Index.lookup t rules
  case orientation orule of
    Oriented -> return ()
    WeaklyOriented ts -> guard (or [ t /= minimalTerm | t <- ts ])
    Unoriented -> guard (lessEq (rhs (rule orule)) (lhs (rule orule)) && rhs (rule orule) /= lhs (rule orule))
  return orule

tryRule :: (Ord f, Sized f, Minimal f, Ord v) => Oriented (Rule f v) -> Strategy f v
tryRule orule t = do
  sub <- maybeToList (match (lhs (rule orule)) t)
  let orule' = substf (evalSubst sub) orule
  case orientation orule' of
    Oriented -> return ()
    WeaklyOriented ts -> guard (or [ t /= minimalTerm | t <- ts ])
    Unoriented -> guard (lessEq (rhs (rule orule')) (lhs (rule orule')) && rhs (rule orule') /= lhs (rule orule'))
  return orule'

tryRuleInModel :: (Ord f, Sized f, Minimal f, Ord v, PrettyTerm f, Pretty v) => [Formula f v] -> Oriented (Rule f v) -> Strategy f v
tryRuleInModel model orule t = do
  sub <- maybeToList (match (lhs (rule orule)) t)
  let orule' = substf (evalSubst sub) orule
  guard (allowedInModel model orule')
  return orule'
