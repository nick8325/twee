{-# LANGUAGE TypeFamilies, FlexibleContexts #-}
module KBC.Equation where

import KBC.Base
import KBC.Term
import KBC.Utils
import KBC.Rewrite
import Control.Monad
import Data.Rewriting.Rule hiding (isVariantOf, vars)
import Data.List
import qualified Data.Map.Strict as Map
import qualified Data.Rewriting.Substitution.Type as Subst

data Equation f = Tm f :=: Tm f deriving (Eq, Ord, Show)
type EquationOf a = Equation (ConstantOf a)

instance Symbolic (Equation f) where
  type ConstantOf (Equation f) = f
  termsDL (t :=: u) = termsDL t `mplus` termsDL u
  substf sub (t :=: u) = substf sub t :=: substf sub u

instance PrettyTerm f => Pretty (Equation f) where
  pPrint (x :=: y) = hang (pPrint x <+> text "=") 2 (pPrint y)

order :: (Minimal f, Sized f, Ord f) => Equation f -> Equation f
order (l :=: r)
  | l == r = l :=: r
  | otherwise =
    case compare (size l) (size r) of
      LT -> r :=: l
      GT -> l :=: r
      EQ -> if lessEq l r then r :=: l else l :=: r

unorient :: Rule f Var -> Equation f
unorient (Rule l r) = l :=: r

orient :: (Minimal f, Sized f, Ord f) => Equation f -> [Oriented (Rule f Var)]
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
  [ MkOriented (WeaklyOriented (map Var ls)) (Rule l l') | not (null ls), ord /= Just GT ] ++
  [ MkOriented (WeaklyOriented (map Var rs)) (Rule r r') | not (null rs), ord /= Just LT ]
  where
    ord = orientTerms l' r'
    l' = erase ls l
    r' = erase rs r
    ls = usort (vars l) \\ usort (vars r)
    rs = usort (vars r) \\ usort (vars l)

    erase [] t = t
    erase xs t = substf (\x -> if x `elem` xs then Fun minimal [] else Var x) t

    rule t u = MkOriented o (Rule t u)
      where
        o | lessEq u t =
            case unify t u of
              Nothing -> Oriented
              Just sub
                | all (== minimalTerm) (Map.elems (Subst.toMap sub)) ->
                  WeaklyOriented (map Var (Map.keys (Subst.toMap sub)))
                | otherwise -> Unoriented
          | otherwise = Unoriented

bothSides :: (Tm f -> Tm f') -> Equation f -> Equation f'
bothSides f (t :=: u) = f t :=: f u

trivial :: Eq f => Equation f -> Bool
trivial (t :=: u) = t == u

equationSize :: Sized f => Equation f -> Int
equationSize (t :=: u) = size t `max` size u
