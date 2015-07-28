{-# LANGUAGE TypeFamilies, CPP, FlexibleContexts, UndecidableInstances, StandaloneDeriving, RecordWildCards, GADTs, ScopedTypeVariables #-}
module KBC.Constraints where

#include "errors.h"
import KBC.Base hiding (equals)
import KBC.Term
import Control.Monad
import qualified Data.Map.Strict as Map
import KBC.Utils
import Data.Maybe
import Data.List
import qualified Data.Rewriting.Substitution.Type as Subst
import qualified Solver.FourierMotzkin as FM
import qualified Solver.FourierMotzkin.Internal as FM
import Data.Graph

-- Constrained things.
data Constrained a =
  Constrained {
    constraint  :: Formula (ConstantOf a) (VariableOf a),
    constrained :: a }

instance (Pretty (ConstantOf a), Minimal (ConstantOf a), Pretty (VariableOf a), Pretty a) => Pretty (Constrained a) where
  pPrint (Constrained (And []) x) = pPrint x
  pPrint (Constrained ctx x) =
    hang (pPrint x) 2 (text "when" <+> pPrint ctx)

deriving instance (Eq a, Eq (ConstantOf a), Eq (VariableOf a)) => Eq (Constrained a)
deriving instance (Ord a, Ord (ConstantOf a), Ord (VariableOf a)) => Ord (Constrained a)
deriving instance (Show a, Show (VariableOf a), Show (ConstantOf a)) => Show (Constrained a)

instance (Minimal (ConstantOf a), Sized (ConstantOf a), Ord (ConstantOf a), Ord (VariableOf a), Symbolic a) => Symbolic (Constrained a) where
  type ConstantOf (Constrained a) = ConstantOf a
  type VariableOf (Constrained a) = VariableOf a

  termsDL x =
    termsDL (constrained x) `mplus`
    termsDL (constraint x)

  substf sub (Constrained ctx x) =
    Constrained (substf sub ctx) (substf sub x)

data Formula f v =
    Less   v v
  | LessEq v v
  | Minimal v
  | Nonminimal v
  | And [Formula f v]
  | Or  [Formula f v]
  deriving (Eq, Ord, Show)

instance (Minimal f, Pretty f, Pretty v) => Pretty (Formula f v) where
  pPrintPrec _ _ (Less t u) = hang (pPrint t <+> text "<") 2 (pPrint u)
  pPrintPrec _ _ (LessEq t u) = hang (pPrint t <+> text "<=") 2 (pPrint u)
  pPrintPrec _ _ (Minimal t) = hang (pPrint t <+> text "=") 2 (pPrint (minimal :: f))
  pPrintPrec _ _ (Nonminimal u) = hang (pPrint (minimal :: f) <+> text "<") 2 (pPrint u)
  pPrintPrec _ _ (And []) = text "true"
  pPrintPrec _ _ (Or []) = text "false"
  pPrintPrec l p (And xs) =
    pPrintParen (p > 10)
      (fsep (punctuate (text " &") (nest_ (map (pPrintPrec l 11) xs))))
    where
      nest_ (x:xs) = x:map (nest 2) xs
      nest_ [] = __
  pPrintPrec l p (Or xs) =
    pPrintParen (p > 10)
      (fsep (punctuate (text " |") (nest_ (map (pPrintPrec l 11) xs))))
    where
      nest_ (x:xs) = x:map (nest 2) xs
      nest_ [] = __

instance (Minimal f, Eq f, Ord v) => Symbolic (Formula f v) where
  type ConstantOf (Formula f v) = f
  type VariableOf (Formula f v) = v

  termsDL (Less t u) = termsDL (Var t, Var u :: Tm f v)
  termsDL (LessEq t u) = termsDL (Var t, Var u :: Tm f v)
  termsDL (Minimal t) = termsDL (Var t :: Tm f v)
  termsDL (Nonminimal t) = termsDL (Var t :: Tm f v)
  termsDL (And ts) = msum (map termsDL ts)
  termsDL (Or ts) = msum (map termsDL ts)

  substf sub (Less t u)
    | su == minimalTerm = Or []
    | st == minimalTerm = Nonminimal (unVar su)
    | otherwise = Less (unVar st) (unVar su)
    where
      st = sub t
      su = sub u
  substf sub (LessEq t u)
    | st == minimalTerm = And []
    | su == minimalTerm = Minimal (unVar st)
    | otherwise = LessEq (unVar st) (unVar su)
    where
      st = sub t
      su = sub u
  substf sub (Minimal t)
    | st == minimalTerm = And []
    | otherwise = Minimal (unVar st)
    where
      st = sub t
  substf sub (Nonminimal t)
    | st == minimalTerm = Or []
    | otherwise = Nonminimal (unVar st)
    where
      st = sub t
  substf sub (And ts) = conj (map (substf sub) ts)
  substf sub (Or ts) = disj (map (substf sub) ts)

unVar :: Tm f v -> v
unVar (Var x) = x
unVar _ = ERROR("function symbol appeared in constraint substitution")

negateFormula :: Formula f v -> Formula f v
negateFormula (Less t u) = LessEq u t
negateFormula (LessEq t u) = Less u t
negateFormula (Minimal t) = Nonminimal t
negateFormula (Nonminimal t) = Minimal t
negateFormula (And ts) = Or (map negateFormula ts)
negateFormula (Or ts) = And (map negateFormula ts)

conj forms
  | false `elem` forms' = false
  | otherwise =
    case forms' of
      [x] -> x
      xs  -> And xs
  where
    flatten (And xs) = xs
    flatten x = [x]
    forms' = filter (/= true) (usort (concatMap flatten forms))
disj forms
  | true `elem` forms' = true
  | otherwise =
    case forms' of
      [x] -> x
      xs  -> Or xs
  where
    flatten (Or xs) = xs
    flatten x = [x]
    forms' = filter (/= false) (usort (concatMap flatten forms))

x &&& y = conj [x, y]
x ||| y = disj [x, y]
true  = And []
false = Or []

data Branch f v =
  -- Branches are kept normalised wrt equals
  Branch {
    less        :: [(v, v)],
    equals      :: [(v, v)], -- greatest variable first
    minimals    :: [v],
    nonminimals :: [v] }
  deriving (Eq, Ord)

norm :: Ord v => Branch f v -> v -> v
norm Branch{..} x = fromMaybe x (lookup x equals)

contradictory :: (Eq f, Eq v) => Branch f v -> Bool
contradictory Branch{..} =
  or [x == y | (x, y) <- less] ||
  or [x `elem` map snd less | x <- minimals] ||
  or [x `elem` nonminimals  | x <- minimals]

formAnd :: (Ord f, Ord v) => Formula f v -> [Branch f v] -> [Branch f v]
formAnd f bs = usort (bs >>= add f)
  where
    add (Less t u) b = addLess t u b
    add (LessEq t u) b = addLess t u b ++ addEquals t u b
    add (Minimal t) b = addMinimal t b
    add (Nonminimal t) b = addNonminimal t b
    add (And []) b = [b]
    add (And (f:fs)) b = add f b >>= add (And fs)
    add (Or fs) b = usort (concat [ add f b | f <- fs ])

branches :: (Ord f, Ord v) => Formula f v -> [Branch f v]
branches x = aux [x]
  where
    aux [] = [Branch [] [] [] []]
    aux (And xs:ys) = aux (xs ++ ys)
    aux (Or xs:ys) = usort $ concat [aux (x:ys) | x <- xs]
    aux (Less t u:xs) = usort $ concatMap (addLess t u) (aux xs)
    aux (LessEq t u:xs) =
      usort $
      concatMap (addLess t u) (aux xs) ++
      concatMap (addEquals u t) (aux xs)
    aux (Minimal t:xs) = usort $ concatMap (addMinimal t) (aux xs)
    aux (Nonminimal t:xs) = usort $ concatMap (addNonminimal t) (aux xs)

addLess :: (Ord f, Ord v) => v -> v -> Branch f v -> [Branch f v]
addLess t0 u0 b@Branch{..} =
  filter (not . contradictory)
    [b {
      less = usort $ newLess ++ less,
      nonminimals = usort $ newNonminimals ++ nonminimals }]
  where
    t = norm b t0
    u = norm b u0
    newLess =
      (t, u):
      [(t, v) | (u', v) <- less, u == u'] ++
      [(v, u) | (v, t') <- less, t == t']
    newNonminimals =
      [u | t `elem` nonminimals]

addEquals :: (Ord f, Ord v) => v -> v -> Branch f v -> [Branch f v]
addEquals t0 u0 b@Branch{..}
  | (t, u) `elem` equals || t == u = [b]
  | otherwise =
    filter (not . contradictory)
      [b {
         equals      = usort $ (t, u):[(x', y') | (x, y) <- equals, let (y', x') = sort2 (sub x, sub y), x' /= y'],
         less        = usort $ [(sub x, sub y) | (x, y) <- less],
         minimals    = usort $ map sub minimals,
         nonminimals = usort $ map sub nonminimals }]
  where
    sort2 (x, y) = (min x y, max x y)
    (u, t) = sort2 (norm b t0, norm b u0)

    sub x
      | x == t = u
      | otherwise = x

addMinimal :: (Ord f, Ord v) => v -> Branch f v -> [Branch f v]
addMinimal t0 b@Branch{..}
  | t `elem` minimals = [b]
  | otherwise =
    filter (not . contradictory)
      [b { minimals = t:minimals }]
  where
    t = norm b t0

addNonminimal :: (Ord f, Ord v) => v -> Branch f v -> [Branch f v]
addNonminimal t0 b@Branch{..} =
  filter (not . contradictory)
    [b {
      nonminimals = usort $ newNonminimals ++ nonminimals }]
  where
    t = norm b t0
    newNonminimals =
      [u | (t', u) <- less, t == t']

solve :: (Ord v, Minimal f) => [v] -> Branch f v -> ([Formula f v], Maybe (Subst f v))
solve xs Branch{..}
  | null equals && null minimals = (forms', Nothing)
  | otherwise = (forms, Just sub)
    where
      sub = Subst.fromMap . Map.fromList $
        [(x, minimalTerm) | x <- minimals] ++
        [(x, Var y) | (x, y) <- equals]
      forms =
        [Less x y | (x, y) <- less] ++
        [Nonminimal x | x <- nonminimals]
      vs = reverse (flattenSCCs (stronglyConnComp [(x, x, [y | (x', y) <- less, x == x']) | x <- xs]))
      forms' =
        [Less x y | (x:xs) <- tails vs, y <- xs] ++
        [Nonminimal x | x <- vs]

lessEqIn :: (Sized f, Minimal f, Ord f, Ord v) => [Formula f v] -> Tm f v -> Tm f v -> Bool
lessEqIn _ t _       |  t == minimalTerm = True
lessEqIn _ (Var x) (Var y) | x == y = True
lessEqIn cond (Var x) (Var y) = Less x y `elem` cond || LessEq x y `elem` cond
lessEqIn _ _ (Var _) = False
lessEqIn cond (Var x) t = x `elem` vars t || or [ y `elem` vars t | Less x' y <- cond, x == x' ] || or [ y `elem` vars t | LessEq x' y <- cond, x == x' ]
lessEqIn cond t@(Fun f ts) u@(Fun g us)
  | f < g     = nonstrict
  | f > g     = strict
  | otherwise = nonstrict && (strict || lexLess ts us)
  where
    nonstrict =
      (xs `isSubsequenceOf` ys && st <= su) || termSizeIs (FM.>/=)
    strict    =
      (xs `isSubsequenceOf` ys && st <  su) || termSizeIs (FM.>==)

    termSizeIs op = isNothing (FM.solve prob)
      where
        prob = FM.addConstraints [sz `op` 0] prob0
        sz = termSize t - termSize u

    prob0 =
      FM.problem $
        [FM.var x FM.<== FM.var y | Less x y <- cond] ++
        [FM.var x FM.<== FM.var y | LessEq x y <- cond] ++
        [FM.var x FM.>== 1 | x <- Map.keys (FM.vars (termSize t - termSize u))]

    termSize (Var x) = FM.var x
    termSize (Fun f xs) = FM.scalar (fromIntegral (funSize f)) + sum (map termSize xs)

    lexLess [] [] = True
    lexLess (t:ts) (u:us) =
      lessEqIn cond t u &&
      case unify t u of
        Nothing -> True
        Just sub
          | Map.null (Subst.toMap sub) -> lexLess ts us
          | otherwise ->
            lexLess (substf (evalSubst sub) ts) (substf (evalSubst sub) us)
    lexLess _ _ = ERROR("incorrect function arity")
    xs = sort (vars t)
    ys = sort (vars u)
    st = fromIntegral (size t)
    su = fromIntegral (size u)
