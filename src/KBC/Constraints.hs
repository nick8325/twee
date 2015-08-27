{-# LANGUAGE TypeFamilies, CPP, FlexibleContexts, UndecidableInstances, StandaloneDeriving, RecordWildCards, GADTs, ScopedTypeVariables #-}
module KBC.Constraints where

#include "errors.h"
import KBC.Base hiding (equals)
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
    constraint  :: Formula (ConstantOf a),
    constrained :: a }

instance (Function (ConstantOf a), Pretty a) => Pretty (Constrained a) where
  pPrint (Constrained (And []) x) = pPrint x
  pPrint (Constrained ctx x) =
    hang (pPrint x) 2 (text "when" <+> pPrint ctx)

deriving instance (Eq a, Eq (ConstantOf a)) => Eq (Constrained a)
deriving instance (Ord a, Ord (ConstantOf a)) => Ord (Constrained a)
deriving instance (Show a, Show (ConstantOf a)) => Show (Constrained a)

instance (Function (ConstantOf a), Symbolic a) => Symbolic (Constrained a) where
  type ConstantOf (Constrained a) = ConstantOf a

  termsDL x =
    termsDL (constrained x) `mplus`
    termsDL (constraint x)

  substf sub (Constrained ctx x) =
    Constrained (substf sub ctx) (substf sub x)

data Formula f =
    Less   Var Var
  | LessEq Var Var
  | Minimal Var
  | Nonminimal Var
  | And [Formula f]
  | Or  [Formula f]
  deriving (Eq, Ord, Show)

instance Function f => Pretty (Formula f) where
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

instance Function f => Symbolic (Formula f) where
  type ConstantOf (Formula f) = f

  termsDL (Less t u) = termsDL (Var t, Var u :: Tm f)
  termsDL (LessEq t u) = termsDL (Var t, Var u :: Tm f)
  termsDL (Minimal t) = termsDL (Var t :: Tm f)
  termsDL (Nonminimal t) = termsDL (Var t :: Tm f)
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

unVar :: Tm f -> Var
unVar (Var x) = x
unVar _ = ERROR("function symbol appeared in constraint substitution")

negateFormula :: Formula f -> Formula f
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

data Branch f =
  -- Branches are kept normalised wrt equals
  Branch {
    less        :: [(Var, Var)],
    equals      :: [(Var, Var)], -- greatest variable first
    minimals    :: [Var],
    nonminimals :: [Var] }
  deriving (Eq, Ord)

instance Function f => Pretty (Branch f) where
  pPrint Branch{..} =
    braces $ fsep $ punctuate (text ",") $
      [pPrint x <+> text "<" <+> pPrint y | (x, y) <- less ] ++
      [pPrint x <+> text "<" <+> pPrint (minimalTerm :: Tm f) | x <- nonminimals ] ++
      [pPrint x <+> text "=" <+> pPrint y | (x, y) <- equals ] ++
      [pPrint x <+> text "=" <+> pPrint (minimalTerm :: Tm f) | x <- minimals ]

trueBranch :: Branch f
trueBranch = Branch [] [] [] []

norm :: Branch f -> Var -> Var
norm Branch{..} x = fromMaybe x (lookup x equals)

contradictory :: Eq f => Branch f -> Bool
contradictory Branch{..} =
  or [x == y | (x, y) <- less] ||
  or [x `elem` map snd less | x <- minimals] ||
  or [x `elem` nonminimals  | x <- minimals]

formAnd :: Ord f => Formula f -> [Branch f] -> [Branch f]
formAnd f bs = usort (bs >>= add f)
  where
    add (Less t u) b = addLess t u b
    add (LessEq t u) b = addLess t u b ++ addEquals t u b
    add (Minimal t) b = addMinimal t b
    add (Nonminimal t) b = addNonminimal t b
    add (And []) b = [b]
    add (And (f:fs)) b = add f b >>= add (And fs)
    add (Or fs) b = usort (concat [ add f b | f <- fs ])

branches :: Ord f => Formula f -> [Branch f]
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

addLess :: Ord f => Var -> Var -> Branch f -> [Branch f]
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

addEquals :: Ord f => Var -> Var -> Branch f -> [Branch f]
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

addMinimal :: Ord f => Var -> Branch f -> [Branch f]
addMinimal t0 b@Branch{..}
  | t `elem` minimals = [b]
  | otherwise =
    filter (not . contradictory)
      [b { minimals = t:minimals }]
  where
    t = norm b t0

addNonminimal :: Ord f => Var -> Branch f -> [Branch f]
addNonminimal t0 b@Branch{..} =
  filter (not . contradictory)
    [b {
      nonminimals = usort $ newNonminimals ++ nonminimals }]
  where
    t = norm b t0
    newNonminimals =
      [u | (t', u) <- less, t == t']

solve :: (Function f, Sized f) => [Var] -> Branch f -> ([Formula f], Maybe (Subst f))
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
