{-# LANGUAGE DeriveGeneric, TypeFamilies #-}
module Twee.Equation where

import Twee.Base
import GHC.Generics

--------------------------------------------------------------------------------
-- Equations.
--------------------------------------------------------------------------------

data Equation f =
  (:=:) {
    eqn_lhs :: {-# UNPACK #-} !(Term f),
    eqn_rhs :: {-# UNPACK #-} !(Term f) }
  deriving (Eq, Ord, Show, Generic)
type EquationOf a = Equation (ConstantOf a)

instance Symbolic (Equation f) where
  type ConstantOf (Equation f) = f

instance PrettyTerm f => Pretty (Equation f) where
  pPrint (x :=: y) = pPrint x <+> text "=" <+> pPrint y

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

-- Apply a function to both sides of an equation.
bothSides :: (Term f -> Term f') -> Equation f -> Equation f'
bothSides f (t :=: u) = f t :=: f u

-- Is an equation of the form t = t?
trivial :: Eq f => Equation f -> Bool
trivial (t :=: u) = t == u
