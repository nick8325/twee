{-# LANGUAGE TypeFamilies, FlexibleContexts #-}
module KBC.Equation where

import KBC.Base
import KBC.Constraints
import KBC.Term
import KBC.Utils
import Control.Monad
import Data.Rewriting.Rule hiding (isVariantOf, vars)
import Data.List

data Equation f v = Tm f v :==: Tm f v deriving (Eq, Ord, Show)
type EquationOf a = Equation (ConstantOf a) (VariableOf a)

instance Symbolic (Equation f v) where
  type ConstantOf (Equation f v) = f
  type VariableOf (Equation f v) = v
  termsDL (t :==: u) = termsDL t `mplus` termsDL u
  substf sub (t :==: u) = substf sub t :==: substf sub u

instance (PrettyTerm f, Pretty v) => Pretty (Equation f v) where
  pPrint (x :==: y) = hang (pPrint x <+> text "=") 2 (pPrint y)

order :: (Sized f, Ord f, Ord v) => Equation f v -> Equation f v
order (l :==: r)
  | l == r || termSize l >= termSize r = l :==: r
  | otherwise = r :==: l

unorient :: Rule f v -> Equation f v
unorient (Rule l r) = l :==: r

orient :: (Minimal f, Sized f, Ord f, Ord v, Numbered v) => Equation f v -> [Constrained (Rule f v)]
orient (l :==: r) =
  -- If we have an equation where some variables appear only on one side, e.g.:
  --   f x y = g x z
  -- then replace it with the equations:
  --   f x y = f x k
  --   g x z = g x k
  --   f x k = g x k
  -- where k is an arbitrary constant
  [ rule l r' | ord /= Just LT && ord /= Just EQ ] ++
  [ rule r l' | ord /= Just GT && ord /= Just EQ ] ++
  [ rule l l' | not (null ls), ord /= Just LT ] ++
  [ rule r r' | not (null rs), ord /= Just GT ]
  where
    ord = orientTerms l' r'
    l' = erase ls l
    r' = erase rs r
    ls = usort (vars l) \\ usort (vars r)
    rs = usort (vars r) \\ usort (vars l)

    erase [] t = t
    erase xs t = substf (\x -> if x `elem` xs then Fun minimal [] else Var x) t

    rule t u = Constrained (toConstraint (less Strict u t)) (Rule t u)

bothSides :: (Tm f v -> Tm f' v') -> Equation f v -> Equation f' v'
bothSides f (t :==: u) = f t :==: f u

trivial :: (Ord f, Ord v) => Equation f v -> Bool
trivial (t :==: u) = t == u

equationSize :: Sized f => Equation f v -> Int
equationSize (t :==: u) = size t `max` size u
