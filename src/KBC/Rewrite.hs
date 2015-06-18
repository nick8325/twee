{-# LANGUAGE TypeFamilies, StandaloneDeriving, FlexibleContexts, UndecidableInstances #-}
module KBC.Rewrite where

import KBC.Base
import KBC.Constraints
import qualified KBC.Index as Index
import KBC.Index(Index)
import KBC.Term
import Data.Rewriting.Rule
import Data.Map.Strict(Map)
import Data.Set(Set)
import qualified Data.Set as Set
import Control.Monad
import Data.Maybe

data Oriented a = MkOriented { orientation :: Orientation (ConstantOf a) (VariableOf a), rule :: a }
deriving instance (Eq (ConstantOf a), Eq (VariableOf a), Eq a) => Eq (Oriented a)
deriving instance (Ord (ConstantOf a), Ord (VariableOf a), Ord a) => Ord (Oriented a)
deriving instance (Show (ConstantOf a), Show (VariableOf a), Show a) => Show (Oriented a)
data Orientation f v = Oriented | WeaklyOriented [Term f v] | Unoriented deriving (Eq, Ord, Show)

ruleConstraint :: (Minimal f, Sized f, Ord f, Ord v) => Oriented (Rule f v) -> Formula Simple f v
ruleConstraint (MkOriented Oriented _) = true
ruleConstraint (MkOriented (WeaklyOriented ts) _) =
  disj [ less Strict (Fun minimal []) t | t <- ts ]
ruleConstraint (MkOriented Unoriented (Rule t u)) = less Strict u t

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

normaliseWith :: Strategy f v -> Tm f v -> Reduction f v
normaliseWith strat t =
  aux [] t
  where
    aux rs t =
      case strat t of
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

rewriteInModel :: (PrettyTerm f, Pretty v, Numbered f, Sized f, Minimal f, Ord f, Numbered v, Ord v) => Index (Oriented (Rule f v)) -> Map v (Extended f v) -> Strategy f v
rewriteInModel rules model t = do
  orule <- Index.lookup t rules
  case orientation orule of
    Oriented -> return ()
    WeaklyOriented ts -> guard (any (/= Fun minimal []) ts)
    Unoriented -> guard (trueIn model (Less (rhs (rule orule)) (lhs (rule orule))))
  return orule

rewrite :: (Numbered f, Sized f, Minimal f, Ord f, Numbered v, Ord v) => Index (Oriented (Rule f v)) -> Strategy f v
rewrite rules t = do
  orule <- Index.lookup t rules
  case orientation orule of
    Oriented -> return ()
    WeaklyOriented ts -> guard (or [ isFun t && t /= Fun minimal [] | t <- ts ])
    Unoriented -> guard (lessThan Strict (rhs (rule orule)) (lhs (rule orule)))
  return orule

rewriteAllowing :: (Numbered f, Sized f, Minimal f, Ord f, Numbered v, Ord v) => Index (Oriented (Rule f v)) -> Set (Formula Simple f v) -> Strategy f v
rewriteAllowing rules forms t = do
  orule <- Index.lookup t rules
  case orientation orule of
    Oriented -> return ()
    WeaklyOriented ts -> guard (or [ isFun t && t /= Fun minimal [] | t <- ts ] || or [ Less (Fun minimal []) t `Set.member` forms | t <- ts ])
    Unoriented -> guard (lessThan Strict (rhs (rule orule)) (lhs (rule orule)) || less Strict (rhs (rule orule)) (lhs (rule orule)) `Set.member` forms)
  return orule

tryRule :: (Ord f, Sized f, Minimal f, Ord v) => Oriented (Rule f v) -> Strategy f v
tryRule orule t = do
  sub <- maybeToList (match (lhs (rule orule)) t)
  let orule' = substf (evalSubst sub) orule
  case orientation orule' of
    Oriented -> return ()
    WeaklyOriented ts -> guard (or [ isFun t && t /= Fun minimal [] | t <- ts ])
    Unoriented -> guard (lessThan Strict (rhs (rule orule')) (lhs (rule orule')))
  return orule'

tryRuleInModel :: (Ord f, Sized f, Minimal f, Ord v) => Map v (Extended f v) -> Oriented (Rule f v) -> Strategy f v
tryRuleInModel model orule t = do
  sub <- maybeToList (match (lhs (rule orule)) t)
  let orule' = substf (evalSubst sub) orule
  case orientation orule' of
    Oriented -> return ()
    WeaklyOriented ts -> guard (any (/= Fun minimal []) ts)
    Unoriented -> guard (trueIn model (Less (rhs (rule orule')) (lhs (rule orule'))))
  return orule'
