{-# LANGUAGE TypeFamilies, CPP, FlexibleContexts, UndecidableInstances, StandaloneDeriving, RecordWildCards, GADTs, ScopedTypeVariables #-}
module KBC.Constraints where

#include "errors.h"
import KBC.Base
import qualified Solver.FourierMotzkin as FM
import qualified Solver.FourierMotzkin.Internal as FM
import KBC.Term
import Control.Monad
import Data.Ord
import Data.Function
import Data.Set(Set)
import Data.Map.Strict(Map)
import qualified Data.Set as Set
import qualified Data.Map.Strict as Map
import KBC.Utils
import Data.Maybe
import Control.Monad.Trans.Writer
import Data.List
import Data.Graph

-- Constrained things.
data Constrained a =
  Constrained {
    constraint  :: Constraint (ConstantOf a) (VariableOf a),
    constrained :: a }

instance (PrettyTerm (ConstantOf a), Pretty (VariableOf a), Pretty a) => Pretty (Constrained a) where
  pPrint (Constrained Constraint{formula = And []} x) = pPrint x
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

data Constraint f v =
  Constraint {
    formula       :: Formula Simple f v,
    branches      :: Formula Fancy f v,
    instances     :: Set (Instance f v) }

instance (Eq f, Eq v) => Eq (Constraint f v) where
  (==) = (==) `on` formula
  
instance (Ord f, Ord v) => Ord (Constraint f v) where
  compare = comparing formula

deriving instance (Show f, Show v) => Show (Constraint f v)

instance (PrettyTerm f, Pretty v) => Pretty (Constraint f v) where
  pPrintPrec l p = pPrintPrec l p . formula

instance (Minimal f, Sized f, Ord f, Ord v) => Symbolic (Constraint f v) where
  type ConstantOf (Constraint f v) = f
  type VariableOf (Constraint f v) = v

  termsDL = termsDL . formula

  substf sub Constraint{..} =
    toConstraint (substf sub formula)

data Instance f v = Subst (Subst f v) | HeadEqual v f deriving (Eq, Ord, Show)

instance (PrettyTerm f, Pretty v) => Pretty (Instance f v) where
  pPrint (Subst sub) = pPrint sub
  pPrint (HeadEqual x f) = text "hd(" <> pPrint x <> text ") = " <> pPrint f

data Formula k f v where
  Less        :: Tm f v -> Tm f v -> Formula k f v
  LessEq      :: Tm f v -> Tm f v -> Formula Simple f v
  And         :: [Formula k f v] -> Formula k f v
  Or          :: [Formula k f v] -> Formula k f v
  SizeIs      :: FM.Constraint v -> Formula Fancy f v
  HeadLess    :: v -> f -> Formula Fancy f v
  HeadGreater :: v -> f -> Formula Fancy f v

deriving instance (Eq f,   Eq v)   => Eq   (Formula k f v)
deriving instance (Ord f,  Ord v)  => Ord  (Formula k f v)
deriving instance (Show f, Show v) => Show (Formula k f v)

data Simple
data Fancy

instance (PrettyTerm f, Pretty v) => Pretty (Formula k f v) where
  pPrintPrec _ _ (Less t u) = hang (pPrint t <+> text "<") 2 (pPrint u)
  pPrintPrec _ _ (LessEq t u) = hang (pPrint t <+> text "<=") 2 (pPrint u)
  pPrintPrec _ _ (And []) = text "true"
  pPrintPrec _ _ (Or []) = text "false"
  pPrintPrec l p (And xs) =
    pPrintParen (p > 10)
      (fsep (punctuate (text " &") (nest' (map (pPrintPrec l 11) xs))))
    where
      nest' (x:xs) = x:map (nest 2) xs
  pPrintPrec l p (Or xs) =
    pPrintParen (p > 10)
      (fsep (punctuate (text " |") (nest' (map (pPrintPrec l 11) xs))))
    where
      nest' (x:xs) = x:map (nest 2) xs
  pPrintPrec l p (SizeIs t) = pPrintPrec l p t
  pPrintPrec l _ (HeadLess t x) = text "hd(" <> pPrintPrec l 0 t <> text ") <" <+> pPrintPrec l 0 x
  pPrintPrec l _ (HeadGreater t x) = text "hd(" <> pPrintPrec l 0 t <> text ") >" <+> pPrintPrec l 0 x

instance (Minimal f, Sized f, Ord f, Ord v) => Symbolic (Formula k f v) where
  type ConstantOf (Formula k f v) = f
  type VariableOf (Formula k f v) = v

  termsDL (Less t u) = termsDL (t, u)
  termsDL (LessEq t u) = termsDL (t, u)
  termsDL (And ts) = msum (map termsDL ts)
  termsDL (Or ts) = msum (map termsDL ts)
  termsDL (SizeIs t) = termsDL (SizeConstraint t)
  termsDL (HeadGreater x _) = return (Var x)
  termsDL (HeadLess x _) = return (Var x)

  substf sub (Less t u) = less' (substf sub t) (substf sub u)
  substf sub (LessEq t u) = less Nonstrict (substf sub t) (substf sub u)
  substf sub (And ts) = conj (map (substf sub) ts)
  substf sub (Or ts) = disj (map (substf sub) ts)
  substf sub (SizeIs t) = sizeIs t'
    where
      SizeConstraint t' = substf sub (SizeConstraint t)
  substf sub (HeadGreater x f) = headGreater (substf sub (Var x)) f
  substf sub (HeadLess x f) = headLess (substf sub (Var x)) f

newtype SizeConstraint f v = SizeConstraint (FM.Constraint v)

instance (Sized f, Ord v) => Symbolic (SizeConstraint f v) where
  type ConstantOf (SizeConstraint f v) = f
  type VariableOf (SizeConstraint f v) = v
  termsDL (SizeConstraint t) =
    msum . map (return . Var) . Map.keys . FM.vars . FM.bound $ t
  substf sub (SizeConstraint t) =
    SizeConstraint t { FM.bound = substFM sub (FM.bound t) }
    where
      substFM f t =
        FM.scalar (FM.constant t) +
        sum [k FM.^* termSize (f v) | (v, k) <- Map.toList (FM.vars t)]

termSize :: (Sized f, Ord v) => Tm f v -> FM.Term v
termSize = foldTerm FM.var fun
  where
    fun f ss = FM.scalar (funSize f) + sum ss

problem :: (Symbolic a, Ord (VariableOf a)) => a -> FM.Problem (VariableOf a)
problem t =
  FM.problem [ FM.var x FM.>== 1 | x <- usort (vars t) ]

negateFormula :: Formula Simple f v -> Formula Simple f v
negateFormula (Less t u) = LessEq u t
negateFormula (LessEq t u) = Less u t
negateFormula (And ts) = Or (map negateFormula ts)
negateFormula (Or ts) = And (map negateFormula ts)

less :: (Sized f, Minimal f, Ord f, Ord v) => Strictness -> Tm f v -> Tm f v -> Formula Simple f v
less str t u
  | str == Nonstrict && isNothing (unify t u) = less Strict t u
  | lessThan str t u = true
  | lessThan (negateStrictness str) u t = false
  | otherwise =
    case str of
      Strict    -> uncurry Less   (focus str t u)
      Nonstrict -> uncurry LessEq (focus str t u)

less' :: (Sized f, Minimal f, Ord f, Ord v) => Tm f v -> Tm f v -> Formula k f v
less' t u =
  case less Strict t u of
    And []   -> And []
    Or  []   -> Or []
    Less t u -> Less t u
    _        -> ERROR("less returned bad constructor")

focus :: (Sized f, Minimal f, Ord f, Ord v) => Strictness -> Tm f v -> Tm f v -> (Tm f v, Tm f v)
focus str t@(Fun f ts) u@(Fun g us) | f == g = loop ts us
  where
    prob = problem (t, u)
    diff = termSize t - termSize u

    loop [] [] = (t, u)
    loop (x:xs) (y:ys)
      | x == y = loop xs ys
      | canFocus x y = focus str x y
      | otherwise = (t, u)
    loop _ _ = ERROR("incorrect function arity")

    canFocus x y =
      [diff' FM.</= 0] ==> diff FM.<== 0 &&
      [diff' FM.>/= 0] ==> diff FM.>== 0 &&
      [diff' FM.>== 0, diff' FM.<== 0] ==> diff FM.>== 0 &&
      [diff' FM.>== 0, diff' FM.<== 0] ==> diff FM.<== 0 &&
      case unify x y of
        Nothing -> True
        Just sub ->
          let t' = subst sub t
              u' = subst sub u in
          case str of
            Strict    -> lessThan Nonstrict u' t'
            Nonstrict -> lessThan Nonstrict t' u'
      where
        diff' = termSize x - termSize y

    infix 4 ==>
    ps ==> q = isNothing (FM.solve (FM.addConstraints (FM.negateConstraint q:ps) prob))
focus _ t u = (t, u)

sizeIs :: forall f v. (Sized f, Ord v) => FM.Constraint v -> Formula Fancy f v
sizeIs p
  | isNothing (FM.solve (FM.addConstraints [p] prob)) = false
  | isNothing (FM.solve (FM.addConstraints [FM.negateConstraint p] prob)) = true
  | otherwise = SizeIs p
  where
    prob = problem (SizeConstraint p :: SizeConstraint f v)

headLess :: (Minimal f, Ord f, Ord v) => Tm f v -> f -> Formula Fancy f v
headLess _ f | f == minimal = false
headLess (Fun f _) g =
  case compare f g of
    LT -> true
    _  -> false
headLess (Var x) f = HeadLess x f

headGreater :: (Sized f, Minimal f, Ord f, Ord v) => Tm f v -> f -> Formula Fancy f v
headGreater _ f | funSize f == 0 && funArity f == 1 = false
headGreater (Fun f _) g =
  case compare f g of
    GT -> true
    _  -> false
headGreater (Var x) f = HeadGreater x f

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

toConstraint :: (Minimal f, Sized f, Ord f, Ord v) => Formula Simple f v -> Constraint f v
toConstraint form = Constraint form branch instances
  where
    (branch, instances) = runWriter (reduce form)

reduce :: (Minimal f, Sized f, Ord f, Ord v) => Formula Simple f v -> Writer (Set (Instance f v)) (Formula Fancy f v)
reduce (LessEq t u) = liftM2 (|||) (reduce (less' t u)) (equalsAnd t u (return true))
reduce (Less t u) = reduceLess t u
reduce (And xs) = fmap conj (mapM reduce xs)
reduce (Or xs) = fmap disj (mapM reduce xs)

reduceLess :: (Minimal f, Sized f, Ord f, Ord v) => Tm f v -> Tm f v -> Writer (Set (Instance f v)) (Formula Fancy f v)
reduceLess (Var x) (Var y) = return (Less (Var x) (Var y))
reduceLess (Var x) t@(Fun f _) = do
  headEqual x f
  let sz = termSize t - FM.var x
      hl = headLess (Var x) f
  if hl == false
  then return (sizeIs (sz FM.>/= 0))
  else if hl == true
  then return (sizeIs (sz FM.>== 0))
  else
    return $
      sizeIs (sz FM.>/= 0) |||
        (sizeIs (sz FM.>== 0) &&& hl)
    -- No need to elaborate headEqual case, it turns into an instance
reduceLess t@(Fun f _) (Var x) = do
  headEqual x f
  let sz = FM.var x - termSize t
      hg = headGreater (Var x) f
  if hg == false
  then return (sizeIs (sz FM.>/= 0))
  else if hg == true
  then return (sizeIs (sz FM.>== 0))
  else
    return $
      sizeIs (sz FM.>/= 0) |||
        (sizeIs (sz FM.>== 0) &&& hg)
reduceLess t@(Fun f ts) u@(Fun g us) = do
  let sz = termSize u - termSize t
  case compare f g of
    LT -> return (sizeIs (sz FM.>== 0))
    GT -> return (sizeIs (sz FM.>/= 0))
    EQ -> do
      form <- loop ts us
      return $
        sizeIs (sz FM.>/= 0) |||
        (sizeIs (sz FM.>== 0) &&& form)
  where
    loop [] [] = return false
    loop (t:ts) (u:us) = do
      form <- reduce (less Strict t u)
      fmap (form |||) (equalsAnd t u (loop ts us))      
    loop _ _ = ERROR("incorrect function arity")

equalsAnd :: (Ord f, Ord v) =>
  Tm f v -> Tm f v ->
  Writer (Set (Instance f v)) (Formula Fancy f v) ->
  Writer (Set (Instance f v)) (Formula Fancy f v)
equalsAnd t u form
  | t == u = form
  | otherwise =
    case unify t u of
      Nothing -> return false
      Just sub -> do
        tell (Set.singleton (Subst sub))
        return false

headEqual :: (Ord f, Ord v) => v -> f -> Writer (Set (Instance f v)) (Formula Fancy f v)
headEqual x f = do
  tell (Set.singleton (HeadEqual x f))
  return false

-- Solving formulas.
data Solution f v =
  -- We complete the set of constraints as follows:
  --  * Less is transitively closed.
  --  * If Less x y, then size x <= size y.
  --  * If HeadGreater x f and Less x y and HeadLess y g with g <= f,
  --    then size x < size y (size x = size y implies f < g).
  -- Once completed, the constraints are satisfiable iff:
  --  1. The size constraints are satisfiable.
  --  2. There is no literal Less x x.
  --  3. There is no pair of literals HeadLess x f and HeadGreater x g
  --     with f <= g.
  Tautological |
  Solution {
    -- Size constraints.
    sol_prob        :: FM.Problem v,
    sol_solution    :: Map v Rational,
    -- HeadLess and HeadGreater constraints for variables.
    sol_headLess    :: Map v f,
    sol_headGreater :: Map v f,
    -- Less x y constraints. Transitively closed.
    sol_less        :: Map v (Set v) }
  deriving (Eq, Ord, Show)

instance (PrettyTerm f, Pretty v) => Pretty (Solution f v) where
  pPrint Tautological = text "true"
  pPrint Solution{..} =
    pPrint [
      pPrint sol_prob,
      pPrint sol_solution,
      pPrint sol_headLess,
      pPrint sol_headGreater,
      pPrint sol_less ]

solve :: (Minimal f, Sized f, Ord f, Ord v) => Formula Fancy f v -> [Solution f v]
solve form = go [] form >>= solve1
  where
    go ls (And xs) = foldM go ls xs
    go ls (Or xs)  = msum [ go ls x | x <- xs ]
    go ls l = return (l:ls)

solve1 :: forall f v. (Minimal f, Sized f, Ord f, Ord v) => [Formula Fancy f v] -> [Solution f v]
solve1 [] = return Tautological
solve1 ls
  | or [ Set.member x s | (x, s) <- Map.toList less' ] = mzero
  | or [ f >= g | (x, (f, g)) <- Map.toList (Map.intersectionWith (,) headLess' headGreater') ] = mzero
  | otherwise =
      case FM.solve prob of
        Nothing -> mzero
        Just sol -> return (Solution prob sol headLess' headGreater' less')
  where
    size = [s | SizeIs s <- ls]
    headLess = [(x, f) | HeadLess x f <- ls]
    headGreater = [(x, f) | HeadGreater x f <- ls]
    headLess' = Map.fromListWith min headLess
    headGreater' = Map.fromListWith max headGreater
    less = [(t, u) | Less (Var t) (Var u) <- ls]
    less' = close less
    prob = FM.addConstraints ps (problem (map SizeConstraint ps :: [SizeConstraint f v]))
      where
        ps = size ++ lessProb ++ headProb
    lessProb = [FM.var x FM.<== FM.var y | (x, y) <- less]
    headProb = [FM.var x FM.</= FM.var y | (x, ys) <- Map.toList less', y <- Set.toList ys, Just f <- [Map.lookup x headGreater'], Just g <- [Map.lookup y headLess'], f >= g ]

close :: Ord a => [(a, a)] -> Map a (Set a)
close bs = Map.fromList [(x, close1 bs x) | x <- usort (map fst bs)]

close1 :: Ord a => [(a, a)] -> a -> Set a
close1 bs x = aux (successors x) Set.empty
  where
    aux [] s = s
    aux (x:xs) s
      | x `Set.member` s = aux xs s
      | otherwise = aux (successors x ++ xs) (Set.insert x s)
      where
    successors x = [y | (x', y) <- bs, x == x']

data Extended f v =
    Original f
    -- ConstrainedVar x n k (Just f):
    -- x is at position n among all ConstrainedVars,
    -- has size k and its head is smaller than f
  | ConstrainedVar v Int Rational (Maybe f)
    -- Unconstrained variables.
    -- These go above the minimal constant but less than
    -- anything else.
  | UnconstrainedVar v
  deriving (Eq, Show)

toExtended :: Ord v => Map v (Extended f v) -> Tm f v -> Tm (Extended f v) v
toExtended m (Var x) =
  case Map.lookup x m of
    Nothing -> Fun (UnconstrainedVar x) []
    Just f -> Fun f []
toExtended m (Fun f ts) =
  Fun (Original f) (map (toExtended m) ts)

fromExtended :: Tm (Extended f v) v -> Tm f v
fromExtended (Fun (Original f) ts) = Fun f (map fromExtended ts)
fromExtended (Fun (ConstrainedVar x _ _ _) []) = Var x
fromExtended (Fun (UnconstrainedVar x) []) = Var x
fromExtended (Fun _ _) = ERROR("extended var applied to arguments")
fromExtended (Var x) = Var x

instance Sized f => Sized (Extended f v) where
  funSize (Original f) = funSize f
  funSize (ConstrainedVar _ _ k _) = k
  funSize UnconstrainedVar{} = 1
  funArity (Original f) = funArity f
  funArity _ = 0

instance Numbered f => Numbered (Extended f v) where
  number (Original f) = number f
  number _ = ERROR("extended vars don't have numbers")
  withNumber n (Original f) = Original (withNumber n f)
  withNumber _ _ = ERROR("extended vars don't have numbers")

instance Minimal f => Minimal (Extended f v) where
  minimal = Original minimal

instance (Minimal f, Sized f, Ord f, Ord v) => Ord (Extended f v) where
  compare (Original f) (Original g) = compare f g

  compare (ConstrainedVar _ m _ _) (ConstrainedVar _ n _ _) = compare m n
  compare (ConstrainedVar _ _ _ Nothing) (Original f)
    | funSize f == 0 && funArity f == 1 = LT
    | otherwise = GT
  compare (ConstrainedVar _ _ _ (Just f)) (Original g)
    | f <= g = LT
    | otherwise = GT

  compare (UnconstrainedVar x) (UnconstrainedVar y) = compare x y
  compare UnconstrainedVar{} (Original f) | f == minimal = GT
  compare UnconstrainedVar{} _ = LT

  compare x y =
    case compare y x of
      LT -> GT
      EQ -> EQ
      GT -> LT

instance (PrettyTerm f, Pretty v) => Pretty (Extended f v) where
  pPrint (Original f) = pPrint f
  pPrint (ConstrainedVar x n k l) =
    text "c" <> pPrint n <> pPrint x <> brackets (pPrint k <> bound l)
    where
      bound Nothing = text ""
      bound (Just f) = text ", <" <+> pPrint f
  pPrint (UnconstrainedVar x) = pPrint x

instance (PrettyTerm f, Pretty v) => PrettyTerm (Extended f v) where
  termStyle (Original f) = termStyle f
  termStyle _ = curried

toModel :: (Ord f, Ord v) => Solution f v -> Map v (Extended f v)
toModel Tautological = Map.empty
toModel Solution{..} =
  Map.fromList [(x, var x i) | (x, i) <- zip vs' [0..]]
  where
    vs = usort (Set.toList (FM.pvars sol_prob) ++
                Map.keys sol_headLess ++
                Map.keys sol_headGreater ++
                concat [(x:Set.toList s) | (x, s) <- Map.toList sol_less])
    vs' = reverse (flattenSCCs (stronglyConnComp [(x, x, Set.toList (Map.findWithDefault Set.empty x sol_less)) | x <- vs]))
    var x i =
      ConstrainedVar x i
        (varSize x)
        (try minimum
         (catMaybes
          [ Map.lookup y sol_headLess
          | y <- x:filter (sameSize x) (Set.toList (Map.findWithDefault Set.empty x sol_less)) ]))
    varSize x = Map.findWithDefault 1 x sol_solution
    sameSize x y = varSize x == varSize y
    try _ [] = Nothing
    try f xs = Just (f xs)

trueIn :: (Sized f, Minimal f, Ord f, Ord v) => Map v (Extended f v) -> Formula Simple f v -> Bool
trueIn model (Less t u) =
  lessThan Strict (toExtended model t) (toExtended model u)
trueIn model (LessEq t u) =
  lessThan Nonstrict (toExtended model t) (toExtended model u)
trueIn model (And xs) = all (trueIn model) xs
trueIn model (Or xs)  = any (trueIn model) xs

instantiate :: (Symbolic a, Sized (ConstantOf a), Minimal (ConstantOf a), Numbered (VariableOf a), Ord (ConstantOf a), Ord (VariableOf a)) => Constrained a -> [Constrained a]
instantiate x@(Constrained Constraint{..} _) = map inst (Set.toList instances)
  where
    inst (Subst sub) = substf (evalSubst sub) x
    inst (HeadEqual v f) = substf sub x
      where
        sub y
          | v == y    = Fun f (map var [n..funArity f+n-1])
          | otherwise = Var y
        var n = Var (withNumber n v)
        n = maximum (0:map (succ . number) (vars x))
