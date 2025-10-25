{-# LANGUAGE FlexibleContexts, UndecidableInstances, RecordWildCards #-}
-- | Solving constraints on variable ordering.
module Twee.Constraints where

--import Twee.Base hiding (equals, Term, pattern Fun, pattern Var, lookup, funs)
import qualified Twee.Term as Flat
import qualified Data.Map.Strict as Map
import Twee.Pretty hiding (equals)
import Twee.Utils
import Data.Maybe
import Data.List hiding (singleton)
import Data.Function
import Data.Graph
import Data.Map.Strict(Map)
import Data.Ord
import Twee.Term hiding (lookup)
import Test.QuickCheck(shuffle)
import Test.QuickCheck.Gen(unGen)
import Test.QuickCheck.Random(mkQCGen)

data Atom f = Constant (Fun f) | Variable Var deriving (Show, Eq, Ord)

{-# INLINE atoms #-}
atoms :: Term f -> [Atom f]
atoms t = aux (singleton t)
  where
    aux Nil = []
    aux (Cons (App f Nil) t) = Constant f:aux t
    aux (Cons (Var x) t) = Variable x:aux t
    aux ConsSym{rest = t} = aux t

toTerm :: Atom f -> Term f
toTerm (Constant f) = build (con f)
toTerm (Variable x) = build (var x)

fromTerm :: Flat.Term f -> Maybe (Atom f)
fromTerm (App f Nil) = Just (Constant f)
fromTerm (Var x) = Just (Variable x)
fromTerm _ = Nothing

instance (Labelled f, PrettyTerm f) => Pretty (Atom f) where
  pPrint = pPrint . toTerm

data Formula f =
    Less   (Atom f) (Atom f)
  | LessEq (Atom f) (Atom f)
  | And [Formula f]
  | Or  [Formula f]
  deriving (Eq, Ord, Show)

instance (Labelled f, PrettyTerm f) => Pretty (Formula f) where
  pPrintPrec _ _ (Less t u) = hang (pPrint t <+> text "<") 2 (pPrint u)
  pPrintPrec _ _ (LessEq t u) = hang (pPrint t <+> text "<=") 2 (pPrint u)
  pPrintPrec _ _ (And []) = text "true"
  pPrintPrec _ _ (Or []) = text "false"
  pPrintPrec l p (And xs) =
    maybeParens (p > 10)
      (fsep (punctuate (text " &") (nest_ (map (pPrintPrec l 11) xs))))
    where
      nest_ (x:xs) = x:map (nest 2) xs
      nest_ [] = undefined
  pPrintPrec l p (Or xs) =
    maybeParens (p > 10)
      (fsep (punctuate (text " |") (nest_ (map (pPrintPrec l 11) xs))))
    where
      nest_ (x:xs) = x:map (nest 2) xs
      nest_ [] = undefined

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
    funs        :: [Fun f],
    less        :: [(Atom f, Atom f)],  -- sorted
    equals      :: [(Atom f, Atom f)] } -- sorted, greatest atom first in each pair
  deriving (Eq, Ord)

instance (Labelled f, PrettyTerm f) => Pretty (Branch f) where
  pPrint Branch{..} =
    braces $ fsep $ punctuate (text ",") $
      [pPrint x <+> text "<" <+> pPrint y | (x, y) <- less ] ++
      [pPrint x <+> text "=" <+> pPrint y | (x, y) <- equals ]

trueBranch :: Branch f
trueBranch = Branch [] [] []

norm :: Eq f => Branch f -> Atom f -> Atom f
norm Branch{..} x = fromMaybe x (lookup x equals)

contradictory :: (Minimal f, Ord f, Labelled f) => Branch f -> Bool
contradictory Branch{..} =
  or [f == minimal | (_, Constant f) <- less] ||
  or [f /= g | (Constant f, Constant g) <- equals] ||
  any cyclic (stronglyConnComp
    [(x, x, [y | (x', y) <- less, x == x']) | x <- usort (map fst less)])
  where
    cyclic (AcyclicSCC _) = False
    cyclic (CyclicSCC _) = True

formAnd :: (Minimal f, Ordered f, Labelled f) => Formula f -> [Branch f] -> [Branch f]
formAnd f bs = usort (bs >>= add f)
  where
    add (Less t u) b = addLess t u b
    add (LessEq t u) b = addLess t u b ++ addEquals t u b
    add (And []) b = [b]
    add (And (f:fs)) b = add f b >>= add (And fs)
    add (Or fs) b = usort (concat [ add f b | f <- fs ])

branches :: (Minimal f, Ordered f, Labelled f) => Formula f -> [Branch f]
branches x = aux [x]
  where
    aux [] = [Branch [] [] []]
    aux (And xs:ys) = aux (xs ++ ys)
    aux (Or xs:ys) = usort $ concat [aux (x:ys) | x <- xs]
    aux (Less t u:xs) = usort $ concatMap (addLess t u) (aux xs)
    aux (LessEq t u:xs) =
      usort $
      concatMap (addLess t u) (aux xs) ++
      concatMap (addEquals u t) (aux xs)

addLess :: (Minimal f, Ordered f, Labelled f) => Atom f -> Atom f -> Branch f -> [Branch f]
addLess _ (Constant min) _ | min == minimal = []
addLess (Constant min) _ b | min == minimal = [b]
addLess t0 u0 b@Branch{..} =
  filter (not . contradictory)
    [addTerm t (addTerm u b{less = usort ((t, u):less)})]
  where
    t = norm b t0
    u = norm b u0

addEquals :: (Minimal f, Ordered f, Labelled f) => Atom f -> Atom f -> Branch f -> [Branch f]
addEquals t0 u0 b@Branch{..}
  | t == u || (t, u) `elem` equals = [b]
  | otherwise =
    filter (not . contradictory)
      [addTerm t (addTerm u b {
         equals      = usort $ (t, u):[(x', y') | (x, y) <- equals, let (y', x') = sort2 (sub x, sub y), x' /= y'],
         less        = usort $ [(sub x, sub y) | (x, y) <- less] })]
  where
    sort2 (x, y) = (min x y, max x y)
    (u, t) = sort2 (norm b t0, norm b u0)

    sub x
      | x == t = u
      | otherwise = x

addTerm :: (Minimal f, Ordered f, Labelled f) => Atom f -> Branch f -> Branch f
addTerm (Constant f) b
  | f `notElem` funs b =
    b {
      funs = f:funs b,
      less =
        usort $
          [ (Constant f, Constant g) | g <- funs b, f << g ] ++
          [ (Constant g, Constant f) | g <- funs b, g << f ] ++ less b }
addTerm _ b = b

newtype Model f = Model (Map (Atom f) (Int, Int))
  deriving (Eq, Show)
-- Representation: map from atom to (major, minor)
-- x <  y if major x < major y
-- x <= y if major x = major y and minor x < minor y

instance (Labelled f, PrettyTerm f) => Pretty (Model f) where
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

modelFromOrder :: (Minimal f, Ord f) => [Atom f] -> Model f
modelFromOrder xs =
  Model (Map.fromList [(x, (i, i)) | (x, i) <- zip xs [0..]])

weakenModel :: Model f -> [Model f]
weakenModel (Model m) =
  [ Model (Map.delete x m) | x <- Map.keys m ] ++
  [ Model (Map.fromList xs)
  | xs <- glue (sortBy (comparing snd) (Map.toList m)),
    all ok (groupBy ((==) `on` (fst . snd)) xs) ]
  where
    glue [] = []
    glue [_] = []
    glue (a@(_x, (i1, j1)):b@(y, (i2, _)):xs) =
      [ (a:(y, (i1, j1+1)):xs) | i1 < i2 ] ++
      map (a:) (glue (b:xs))

    -- We must never make two constants equal
    ok xs = length [x | (Constant x, _) <- xs] <= 1

varInModel :: (Minimal f, Ord f) => Model f -> Var -> Bool
varInModel (Model m) x = Variable x `Map.member` m

modelVarMaxBound :: Model f -> Int
modelVarMaxBound (Model m) =
  maximum (0:map (succ . fst) (Map.elems m))

modelVarValue :: Model f -> Var -> Maybe Var
modelVarValue (Model m) x = V . fst <$> Map.lookup (Variable x) m

varGroups :: (Minimal f, Ord f) => Model f -> [(Fun f, [Var], Maybe (Fun f))]
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

class Minimal f where
  minimal :: Fun f
  skolem :: Int -> Fun f

{-# INLINE lessEqInModel #-}
lessEqInModel :: (Minimal f, Ordered f, Labelled f) => Model f -> Atom f -> Atom f -> Maybe Strictness
lessEqInModel (Model m) x y
  | Just (a, _) <- Map.lookup x m,
    Just (b, _) <- Map.lookup y m,
    a < b = Just Strict
  | Just a <- Map.lookup x m,
    Just b <- Map.lookup y m,
    a < b = Just Nonstrict
  | x == y = Just Nonstrict
  | Constant a <- x, Constant b <- y, a << b = Just Strict
  | Constant a <- x, a == minimal = Just Nonstrict
  | otherwise = Nothing

solve :: (Minimal f, Ordered f, PrettyTerm f, Labelled f) => [Atom f] -> Branch f -> Either (Model f) (Subst f)
solve xs branch@Branch{..}
  | null equals && not (all true less) =
    error $ "Model " ++ prettyShow model ++ " is not a model of " ++ prettyShow branch ++ " (edges = " ++ prettyShow edges ++ ", vs = " ++ prettyShow vs ++ ")"
  | null equals = Left model
  | otherwise = Right sub
    where
      sub = fromMaybe undefined . listToSubst $
        [(x, toTerm y) | (Variable x, y) <- equals] ++
        [(y, toTerm x) | (x@Constant{}, Variable y) <- equals]
      vs = Constant minimal:reverse (flattenSCCs (stronglyConnComp edges'))
      edges = [(x, x, [y | (x', y) <- less', x == x']) | x <- as, x /= Constant minimal]
      edges' = unGen (shuffle edges) (mkQCGen 12345) 0
      less' = less ++ [(Constant x, Constant y) | Constant x <- as, Constant y <- as, x << y]
      as = usort $ xs ++ map fst less ++ map snd less
      model = modelFromOrder vs
      true (t, u) = lessEqInModel model t u == Just Strict

class Ord f => Ordered f where
  -- | Return 'True' if the first term is less than or equal to the second,
  -- in the term ordering.
  lessEq :: Term f -> Term f -> Bool
  -- | Check if the first term is less than or equal to the second in the given model,
  -- and decide whether the inequality is strict or nonstrict.
  lessIn :: Model f -> Term f -> Term f -> Maybe Strictness
  lessEqSkolem :: Term f -> Term f -> Bool

-- | Describes whether an inequality is strict or nonstrict.
data Strictness =
    -- | The first term is strictly less than the second.
    Strict
    -- | The first term is less than or equal to the second.
  | Nonstrict deriving (Eq, Show)

-- | Return 'True' if the first argument is strictly less than the second,
-- in the term ordering.
lessThan :: Ordered f => Term f -> Term f -> Bool
lessThan t u = lessEq t u && isNothing (unify t u)

-- | Return the direction in which the terms are oriented according to the term
-- ordering, or 'Nothing' if they cannot be oriented. A result of @'Just' 'LT'@
-- means that the first term is less than /or equal to/ the second.
orientTerms :: Ordered f => Term f -> Term f -> Maybe Ordering
orientTerms t u
  | t == u = Just EQ
  | lessEq t u = Just LT
  | lessEq u t = Just GT
  | otherwise = Nothing
