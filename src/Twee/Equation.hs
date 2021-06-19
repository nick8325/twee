-- | Equations.
{-# LANGUAGE TypeFamilies #-}
module Twee.Equation where

import Twee.Base
import Control.Monad
import Data.List
import Data.Ord

--------------------------------------------------------------------------------
-- * Equations.
--------------------------------------------------------------------------------

data Equation f =
  (:=:) {
    eqn_lhs :: {-# UNPACK #-} !(Term f),
    eqn_rhs :: {-# UNPACK #-} !(Term f) }
  deriving (Eq, Ord, Show)
type EquationOf a = Equation (ConstantOf a)

instance Symbolic (Equation f) where
  type ConstantOf (Equation f) = f
  termsDL (t :=: u) = termsDL t `mplus` termsDL u
  subst_ sub (t :=: u) = subst_ sub t :=: subst_ sub u

instance (Labelled f, PrettyTerm f) => Pretty (Equation f) where
  pPrint (x :=: y) = pPrint x <+> text "=" <+> pPrint y

-- | Order an equation roughly left-to-right, and
-- canonicalise its variables.
-- There is no guarantee that the result is oriented.
order :: Function f => Equation f -> Equation f
order (l :=: r)
  | l == r = l :=: r
  | otherwise =
    minimumBy cmp $
    filter (\(t :=: u) -> ground u `lessEq` ground t) $
    map canonicalise
    [l :=: r, r :=: l]
  where
    cmp eq1 eq2
      | eq1 == eq2 = EQ
      | orderedSimplerThan eq1 eq2 = LT
      | otherwise = GT

-- Helper for 'order' and 'simplerThan'
orderedSimplerThan :: Function f => Equation f -> Equation f -> Bool
orderedSimplerThan (t1 :=: u1) (t2 :=: u2) =
  t1 `lessEqSkolem` t2 && (t1 /= t2 || ((u1 `lessEqSkolem` u2 && u1 /= u2)))

-- | Apply a function to both sides of an equation.
bothSides :: (Term f -> Term f') -> Equation f -> Equation f'
bothSides f (t :=: u) = f t :=: f u

-- | Is an equation of the form t = t?
trivial :: Eq f => Equation f -> Bool
trivial (t :=: u) = t == u

-- | A total order on equations. Equations with lesser terms are smaller.
simplerThan :: Function f => Equation f -> Equation f -> Bool
eq1 `simplerThan` eq2 =
  order eq1 `orderedSimplerThan` order eq2

-- | Match one equation against another.
matchEquation :: Equation f -> Equation f -> Maybe (Subst f)
matchEquation (pat1 :=: pat2) (t1 :=: t2) = do
  sub <- match pat1 t1
  matchIn sub pat2 t2
