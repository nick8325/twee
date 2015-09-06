{-# LANGUAGE TypeFamilies, CPP, FlexibleContexts, UndecidableInstances, StandaloneDeriving, RecordWildCards, GADTs, ScopedTypeVariables, PatternGuards, PatternSynonyms #-}
module KBC.Constraints where

#include "errors.h"
import KBC.Base hiding (equals, Term(..), pattern Fun, pattern Var, lookup)
import qualified KBC.Term as Flat
import KBC.Term.Nested
import qualified KBC.Term.Nested as Nested
import Control.Monad
import qualified Data.Map.Strict as Map
import KBC.Utils
import Data.Maybe
import Data.List
import Data.Graph
import qualified Data.Map.Strict as Map
import Data.Map.Strict(Map)
import Data.Ord

data Atom f = Constant (Fun f) | Variable Var deriving (Eq, Ord, Show)

toTerm :: Atom f -> Term f
toTerm (Constant f) = Fun f []
toTerm (Variable x) = Var x

fromTerm :: Flat.Term f -> Maybe (Atom f)
fromTerm (Flat.Fun f Empty) = Just (Constant f)
fromTerm (Flat.Var x) = Just (Variable x)
fromTerm _ = Nothing

instance Function f => Pretty (Atom f) where
  pPrint = pPrint . toTerm

data Formula f =
    Less   (Atom f) (Atom f)
  | LessEq (Atom f) (Atom f)
  | And [Formula f]
  | Or  [Formula f]
  deriving (Eq, Ord, Show)

instance Function f => Pretty (Formula f) where
  pPrintPrec _ _ (Less t u) = hang (pPrint t <+> text "<") 2 (pPrint u)
  pPrintPrec _ _ (LessEq t u) = hang (pPrint t <+> text "<=") 2 (pPrint u)
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

negateFormula :: Formula f -> Formula f
negateFormula (Less t u) = LessEq u t
negateFormula (LessEq t u) = Less u t
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
    less        :: [(Atom f, Atom f)],
    equals      :: [(Atom f, Atom f)] } -- greatest atom first
  deriving (Eq, Ord)

instance Function f => Pretty (Branch f) where
  pPrint Branch{..} =
    braces $ fsep $ punctuate (text ",") $
      [pPrint x <+> text "<" <+> pPrint y | (x, y) <- less ] ++
      [pPrint x <+> text "=" <+> pPrint y | (x, y) <- equals ]

trueBranch :: Branch f
trueBranch = Branch [] []

norm :: Eq f => Branch f -> Atom f -> Atom f
norm Branch{..} x = fromMaybe x (lookup x equals)

contradictory :: Function f => Branch f -> Bool
contradictory Branch{..} =
  or [x == y | (x, y) <- less] ||
  or [fun g [] `lessEq` fun f [] | (Constant f, Constant g) <- less] ||
  or [f == minimal | (_, Constant f) <- less] ||
  or [f /= g | (Constant f, Constant g) <- equals]

formAnd :: Function f => Formula f -> [Branch f] -> [Branch f]
formAnd f bs = usort (bs >>= add f)
  where
    add (Less t u) b = addLess t u b
    add (LessEq t u) b = addLess t u b ++ addEquals t u b
    add (And []) b = [b]
    add (And (f:fs)) b = add f b >>= add (And fs)
    add (Or fs) b = usort (concat [ add f b | f <- fs ])

branches :: Function f => Formula f -> [Branch f]
branches x = aux [x]
  where
    aux [] = [Branch [] []]
    aux (And xs:ys) = aux (xs ++ ys)
    aux (Or xs:ys) = usort $ concat [aux (x:ys) | x <- xs]
    aux (Less t u:xs) = usort $ concatMap (addLess t u) (aux xs)
    aux (LessEq t u:xs) =
      usort $
      concatMap (addLess t u) (aux xs) ++
      concatMap (addEquals u t) (aux xs)

addLess :: Function f => Atom f -> Atom f -> Branch f -> [Branch f]
addLess t0 u0 b@Branch{..} =
  filter (not . contradictory)
    [b {
      less = usort $ newLess ++ less }]
  where
    t = norm b t0
    u = norm b u0
    newLess =
      (t, u):
      [(t, v) | (u', v) <- less, u == u'] ++
      [(v, u) | (v, t') <- less, t == t']

addEquals :: Function f => Atom f -> Atom f -> Branch f -> [Branch f]
addEquals t0 u0 b@Branch{..}
  | t == u || (t, u) `elem` equals = [b]
  | otherwise =
    filter (not . contradictory)
      [b {
         equals      = usort $ (t, u):[(x', y') | (x, y) <- equals, let (y', x') = sort2 (sub x, sub y), x' /= y'],
         less        = usort $ [(sub x, sub y) | (x, y) <- less] }]
  where
    sort2 (x, y) = (min x y, max x y)
    (u, t) = sort2 (norm b t0, norm b u0)

    sub x
      | x == t = u
      | otherwise = x

newtype Model f = Model (Map (Atom f) (Int, Int))
  deriving Show
-- Representation: map from atom to (major, minor)
-- x <  y if major x < major y
-- x <= y if major x = major y and minor x < minor y

instance Function f => Pretty (Model f) where
  pPrint (Model m)
    | Map.size m <= 1 = text "empty"
    | otherwise = fsep (go (sortBy (comparing snd) (Map.toList m)))
      where
        go [(x, _)] = [pPrint x]
        go ((x, (i, _)):xs@((_, (j, _)):_)) =
          (pPrint x <+> text rel):go xs
          where
            rel = if i == j then "<=" else "<"

modelToLiterals :: Model f -> [Formula f]
modelToLiterals (Model m) = go (sortBy (comparing snd) (Map.toList m))
  where
    go []  = []
    go [_] = []
    go ((x, (i, _)):xs@((y, (j, _)):_)) =
      rel x y:go xs
      where
        rel = if i == j then LessEq else Less

modelFromOrder :: Function f => [Atom f] -> Model f
modelFromOrder xs =
  Model (Map.fromList [(x, (i, i)) | (x, i) <- zip xs [0..]])

weakenModel :: Ord f => Model f -> [Model f]
weakenModel (Model m) =
  [ Model (Map.delete x m)  | x <- Map.keys m ] ++
  [ Model (Map.fromList xs) | xs <- glue (sortBy (comparing snd) (Map.toList m)) ]
  where
    glue [] = []
    glue [_] = []
    glue (a@(x, (i1, j1)):b@(y, (i2, _)):xs) =
      [ (a:(y, (i1, j1+1)):xs) | i1 < i2 ] ++
      map (a:) (glue (b:xs))

varInModel :: Function f => Model f -> Var -> Bool
varInModel (Model m) x = Variable x `Map.member` m

varGroups :: Function f => Model f -> [(Fun f, [Var], Maybe (Fun f))]
varGroups (Model m) = filter nonempty (go minimal (map fst (sortBy (comparing snd) (Map.toList m))))
  where
    go f xs =
      case span isVariable xs of
        (_, []) -> [(f, map unVariable xs, Nothing)]
        (ys, Constant g:zs) ->
          (f, map unVariable ys, Just g):go g zs
    isVariable (Constant _) = False
    isVariable (Variable _) = True
    unVariable (Variable x) = x
    nonempty (_, [], _) = False
    nonempty _ = True

lessEqInModel :: Ord f => Model f -> Atom f -> Atom f -> Maybe Strictness
lessEqInModel (Model m) x y
  | Just (a, _) <- Map.lookup x m,
    Just (b, _) <- Map.lookup y m,
    a < b = Just Strict
  | Just a <- Map.lookup x m,
    Just b <- Map.lookup y m,
    a < b = Just Nonstrict
  | otherwise = Nothing

solve :: Function f => [Var] -> Branch f -> Either (Model f) (Subst f)
solve xs b@Branch{..}
  | null equals = Left model
  | otherwise = Right sub
    where
      sub = Nested.flattenSubst $
        [(x, toTerm y) | (Variable x, y) <- equals] ++
        [(y, toTerm x) | (x@Constant{}, Variable y) <- equals]
      vs = reverse (flattenSCCs (stronglyConnComp [(x, x, [y | (x', y) <- less, x == x']) | x <- as]))
      as = usort $ map Variable xs ++ filter (/= Constant minimal) (map fst less ++ map snd less)
      model = modelFromOrder vs
