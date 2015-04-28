{-# LANGUAGE TypeOperators, TypeFamilies, CPP, FlexibleContexts, UndecidableInstances, StandaloneDeriving, ConstraintKinds #-}
module KBC.Constraints where

#include "errors.h"
import KBC.Base
import qualified Solver.FourierMotzkin as FM
import qualified Solver.FourierMotzkin.Internal as FM
import Solver.FourierMotzkin hiding (trace, solve)
import KBC.Term
import KBC.Utils
import Control.Monad
import Control.Monad.Trans.State.Strict
import qualified Data.Map.Strict as Map
import Data.Map.Strict(Map)
import Data.Maybe
import Data.Ord
import qualified Data.Set as Set
import Data.Set(Set)
import Data.List

-- Constrained things.
data Constrained a =
  Constrained {
    context     :: ContextOf a,
    constrained :: a }

instance (PrettyTerm (ConstantOf a), Pretty (VariableOf a), Pretty a) => Pretty (Constrained a) where
  pPrint (Constrained (Context { formula = FTrue }) x) = pPrint x
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
    termsDL (context x)

  substf sub (Constrained ctx x) =
    Constrained (substf sub ctx) (substf sub x)

reduce :: (Symbolic a, Minimal (ConstantOf a), Sized (ConstantOf a), Ord (ConstantOf a), Ord (VariableOf a), Numbered (VariableOf a)) => Constrained a -> Constrained a
reduce x =
  case split x of
    [y] | simple (formula (context y)) -> y
    [] -> Constrained (toContext FFalse) (constrained x)
    _ -> x
  where
    simple (p :&: q) = simple p && simple q
    simple (p :|: q) = simple p || simple q
    simple FTrue = True
    simple FFalse = True
    simple Less{} = True
    simple _ = False

split :: (Symbolic a, Minimal (ConstantOf a), Sized (ConstantOf a), Ord (ConstantOf a), Ord (VariableOf a), Numbered (VariableOf a)) => Constrained a -> [Constrained a]
split (Constrained ctx x) =
  case runM simplify (formula ctx) of
    Equal t u p q ->
      let Just sub = unify t u in
      split (make q) ++ split (substf (evalSubst sub) (make (prune p)))
    p :|: q ->
      split (make p) ++ split (make q)
    p -> [make p | satisfiable (solved (toContext p))]
  where
    make ctx = Constrained (toContext ctx) x
    prune (Equal t u p q) = Equal t u (prune p) (prune q)
    prune (p :|: q) = prune p ||| prune q
    prune p
      | satisfiable (solved (toContext p)) = p
      | otherwise = FFalse

mainSplit :: (Minimal f, Sized f, Numbered v, Ord f, Ord v) => Formula f v -> Formula f v
mainSplit p =
  case filter (satisfiable . solve) (mainSplits p) of
    [] -> FFalse
    (q:_) -> q

mainSplits :: (Minimal f, Sized f, Numbered v, Ord f, Ord v) => Formula f v -> [Formula f v]
mainSplits p =
  case runM simplify p of
    Equal _ _ _ q -> mainSplits q
    p :|: q -> mainSplits p ++ mainSplits q
    p -> [p]

neg :: (Symbolic a, Minimal (ConstantOf a), Sized (ConstantOf a), Numbered (VariableOf a), Ord (ConstantOf a), Ord (VariableOf a)) => Constrained a -> Constrained a
neg = runM $ \x -> do
  f <- negFormula (formula (context x))
  return x { context = toContext f }

-- Contexts (sets of constraints).
type ContextOf a = Context (ConstantOf a) (VariableOf a)
data Context f v =
  Context {
    formula :: Formula f v,
    solved  :: Solved f v,
    model   :: Map v (Extended f v) }
  deriving Show

toContext :: (Minimal f, Sized f, Ord f, Ord v) => Formula f v -> Context f v
toContext x = Context x s (toModel s)
  where
    s = solve x

instance (Eq f, Eq v) => Eq (Context f v) where
  x == y = formula x == formula y
instance (Ord f, Ord v) => Ord (Context f v) where
  compare = comparing formula
instance (PrettyTerm f, Pretty v) => Pretty (Context f v) where
  pPrint = pPrint . formula
instance (Minimal f, Sized f, Ord f, Ord v) => Symbolic (Context f v) where
  type ConstantOf (Context f v) = f
  type VariableOf (Context f v) = v
  termsDL ctx = termsDL (formula ctx)
  substf sub ctx = toContext (substf sub (formula ctx))

-- Formulas.
type FormulaOf a = Formula (ConstantOf a) (VariableOf a)
data Formula f v =
  -- After calling split, formulas are in the following form:
  --  * No occurrences of Equal.
  --  * HeadIs and Less can only be applied to variables.
  --  * No tautological or impossible literals.
    FTrue
  | FFalse
  | Formula f v :&: Formula f v
  | Formula f v :|: Formula f v
  | Size (Constraint v)
  | HeadIs Sense (Tm f v) f
  | Less (Tm f v) (Tm f v)
    -- Equal t u p q represents (t = u & p) | q.
    -- The smart constructors (|||) and (&&&) lift
    -- Equal to the top level.
  | Equal (Tm f v) (Tm f v) (Formula f v) (Formula f v)
  deriving (Eq, Ord, Show)

data Sense = Lesser | Greater deriving (Eq, Ord, Show)
instance Pretty Sense where
  pPrint Lesser = text "<"
  pPrint Greater = text ">"

instance (PrettyTerm f, Pretty v) => Pretty (Formula f v) where
  pPrintPrec _ _ FTrue = text "true"
  pPrintPrec _ _ FFalse = text "false"
  pPrintPrec l p (x :&: y) =
    pPrintParen (p > 10)
      (hang (pPrintPrec l 11 x <+> text "&") 0 (pPrintPrec l 11 y))
  pPrintPrec l p (x :|: y) =
    pPrintParen (p > 10)
      (hang (pPrintPrec l 11 x <+> text "|") 0 (pPrintPrec l 11 y))
  pPrintPrec l p (Size t) = pPrintPrec l p t
  pPrintPrec l _ (HeadIs sense t x) = text "hd(" <> pPrintPrec l 0 t <> text ")" <+> pPrintPrec l 0 sense <+> pPrintPrec l 0 x
  pPrintPrec l _ (Less t u) = pPrintPrec l 0 t <+> text "<" <+> pPrintPrec l 0 u
  pPrintPrec l _ (Equal t u FTrue FFalse) =
    pPrintPrec l 0 t <+> text "=" <+> pPrintPrec l 0 u
  pPrintPrec l _ (Equal t u p FFalse) =
    text "{" <> pPrintPrec l 0 t <+> text "=" <+> pPrintPrec l 0 u <> text "}" <+>
    pPrintPrec l 11 p
  pPrintPrec l p (Equal t u x y) =
    pPrintPrec l p ((Equal t u x FFalse) :|: y)

instance (Minimal f, Sized f, Ord v) => Symbolic (Formula f v) where
  type ConstantOf (Formula f v) = f
  type VariableOf (Formula f v) = v
  termsDL FTrue = mzero
  termsDL FFalse = mzero
  termsDL (p :&: q) = termsDL p `mplus` termsDL q
  termsDL (p :|: q) = termsDL p `mplus` termsDL q
  termsDL (Size t) = msum (map (return . Var) (Map.keys (FM.vars (FM.bound t))))
  termsDL (HeadIs _ t _) = return t
  termsDL (Less t u) = return t `mplus` return u
  termsDL (Equal t u p q) = return t `mplus` return u `mplus` termsDL p `mplus` termsDL q

  substf _ FTrue = FTrue
  substf _ FFalse = FFalse
  substf sub (p :&: q) = substf sub p &&& substf sub q
  substf sub (p :|: q) = substf sub p ||| substf sub q
  substf sub (Size t) = Size t { FM.bound = substFM sub (FM.bound t) }
    where
      substFM f t =
        scalar (FM.constant t) +
        sum [k ^* termSize (f v) | (v, k) <- Map.toList (FM.vars t)]
  substf sub (HeadIs sense t f) = HeadIs sense (substf sub t) f
  substf sub (Less t u) = Less (substf sub t) (substf sub u)
  substf sub (Equal t u p q) = Equal (substf sub t) (substf sub u) (substf sub p) (substf sub q)

termSize :: (Minimal f, Sized f, Ord v) => Tm f v -> FM.Term v
termSize = foldTerm FM.var fun
  where
    fun f ss = scalar (funSize f) + sum ss

sizeAxioms :: Ord v => FM.Term v -> [Constraint v]
sizeAxioms s = [ var x >== 1 | x <- Map.keys (FM.vars s) ]

termAxioms :: (Symbolic a, Ord (VariableOf a)) => a -> [Constraint (VariableOf a)]
termAxioms t = [ var x >== 1 | x <- usort (vars t) ]

(|||), (&&&) :: Formula f v -> Formula f v -> Formula f v
FTrue ||| _ = FTrue
_ ||| FTrue = FTrue
FFalse ||| p = p
p ||| FFalse = p
Equal t u p q ||| r = Equal t u p (q ||| r)
r ||| Equal t u p q = Equal t u p (q ||| r)
p ||| q = p :|: q

FTrue &&& p = p
p &&& FTrue = p
FFalse &&& _ = FFalse
_ &&& FFalse = FFalse
Equal t u p q &&& r = Equal t u (p &&& r) (q &&& r)
r &&& Equal t u p q = Equal t u (p &&& r) (q &&& r)
p &&& (q :|: r) = (p &&& q) ||| (p &&& r)
(p :|: q) &&& r = (p &&& r) ||| (q &&& r)
p &&& q = p :&: q

true :: (Minimal f, Sized f, Ord f, Ord v) => Formula f v -> Bool
true FTrue = True
true FFalse = False
true (p :&: q) = true p && true q
true (p :|: q) = true p || true q
true (Less t u) = t `simplerThan` u
true (HeadIs Lesser (Fun f _) g) | f < g = True
true (HeadIs Greater (Fun f _) g) | f > g = True
true (Size (FM.Closed s)) | minSize s >= Just 0 = True
true (Size (FM.Open s))   | minSize s >  Just 0 = True
true _ = False

minSize :: Ord v => FM.Term v -> Maybe Rational
minSize s
  | any (< 0) (Map.elems (FM.vars s)) = Nothing
  | otherwise = Just (sum (Map.elems (FM.vars s)) + FM.constant s)

type M = State Int

runM :: (Symbolic a, Numbered (VariableOf a)) => (a -> M b) -> a -> b
runM f x = evalState (f x) n
  where
    n = maximum (0:map (succ . number) (vars x))

newName :: Numbered a => a -> M a
newName x = do
  n <- get
  put $! n+1
  return (withNumber n x)

simplify :: (Minimal f, Sized f, Ord f, Ord v, Numbered v) => Formula f v -> M (Formula f v)
simplify FTrue = return FTrue
simplify FFalse = return FFalse
simplify (p :&: q) = liftM2 (&&&) (simplify p) (simplify q) >>= go
  where
    go p@Equal{} = simplify p
    go p = return p
simplify (p :|: q) = liftM2 (|||) (simplify p) (simplify q) >>= go
  where
    go p@Equal{} = simplify p
    go p = return p
simplify (Equal t u p q) | t == u = simplify (p ||| q)
simplify (Equal t u p q) =
  case unify t u of
    Nothing -> simplify q
    Just sub -> liftM2 (equal t u) (simplify (substf (sanitise (evalSubst sub)) p)) (simplify q)
  where
    equal _ _ FFalse q = q
    equal _ _ _ FTrue = FTrue
    equal t u p q = Equal t u p q
    sanitise f x
      | isVar t || isGround t = t
      | otherwise = Var x
      where
        t = f x
simplify (Size s)
  | isNothing (solve s) = return FFalse
  | isNothing (solve (FM.negateBound s)) = return FTrue
  where
    solve s = FM.solve (addConstraints [s] p)
    p = problem (sizeAxioms (FM.bound s))
simplify (HeadIs sense (Fun f _) g)
  | test sense f g = return FTrue
  | otherwise = return FFalse
  where
    test Lesser = (<)
    test Greater = (>)
simplify (HeadIs Lesser _ x) | x == minimal = return FFalse
simplify (HeadIs Greater _ f) | funSize f == 0 && funArity f == 1 =
  return FFalse
simplify (Less t u) | t == u = return FFalse
simplify (Less _ (Fun x [])) | x == minimal = return FFalse
simplify (Less t (Var x)) | x `elem` vars t = return FFalse
simplify (Less (Var x) t) | x `elem` vars t = return FTrue
simplify (Less t u) | isFun t || isFun u = do
  rest <- structLess t u
  simplify (Size (sz </= 0) ||| (Size (sz >== 0) &&& Size (sz <== 0) &&& rest))
  where
    sz = termSize t - termSize u
simplify p = return p

structLess :: (Minimal f, Sized f, Ord f, Ord v, Numbered v) => Tm f v -> Tm f v -> M (Formula f v)
structLess (Fun f ts) (Fun g us) =
  return $
  case compare f g of
    LT -> FTrue
    GT -> FFalse
    EQ -> loop ts us
  where
    loop [] [] = FFalse
    loop (t:ts) (u:us) = Equal t u (loop ts us) (Less t u)
    loop _ _ = ERROR("inconsistent arities")
structLess (Var x) (Fun f ts) = do
  u <- specialise x f
  rest <- structLess u (Fun f ts)
  return $
    Equal (Var x) u rest $
      HeadIs Lesser (Var x) f
structLess (Fun f ts) (Var x) = do
  u <- specialise x f
  rest <- structLess (Fun f ts) u
  return $
    Equal (Var x) u rest $
      HeadIs Greater (Var x) f
structLess (Var _) (Var _) =
  ERROR("impossible case in structLess")

specialise :: (Minimal f, Sized f, Ord f, Ord v, Numbered v) => v -> f -> M (Tm f v)
specialise x f = do
  ns <- replicateM (funArity f) (newName x)
  return (Fun f (map Var ns))

negFormula :: (Minimal f, Sized f, Numbered v, Ord f, Ord v) => Formula f v -> M (Formula f v)
negFormula FTrue = return FFalse
negFormula FFalse = return FTrue
negFormula (p :&: q) = liftM2 (|||) (negFormula p) (negFormula q)
negFormula (p :|: q) = liftM2 (&&&) (negFormula p) (negFormula q)
negFormula (Size s) = return (Size (FM.negateBound s))
negFormula (Less t u) = return (Equal t u FTrue (Less u t))
negFormula (HeadIs sense (Var x) f) = do
  t <- specialise x f
  return (Equal (Var x) t FTrue (HeadIs (negateSense sense) (Var x) f))
  where
    negateSense Lesser = Greater
    negateSense Greater = Lesser
negFormula _ = ERROR "must call split before using a context"

-- Solved formulas.
type SolvedOf a = Solved (ConstantOf a) (VariableOf a)
data Solved f v =
  -- We complete the set of constraints as follows:
  --  * Less is transitively closed.
  --  * If Less x y, then size x <= size y.
  --  * If HeadGreater x f and Less x y and HeadLess y g with g <= f,
  --    then size x < size y (size x = size y implies f < g).
  --    When x = y this becomes: if HeadGreater x f and HeadLess x f,
  --    then size x < size x, i.e. false.
  -- Once completed, the constraints are satisfiable iff:
  --  1. The size constraints are satisfiable.
  --  2. There is no literal Less x x.
  Unsolvable |
  Tautological |
  Solved {
    -- Size constraints.
    prob        :: Problem v,
    solution    :: Map v Rational,
    -- HeadLess and HeadGreater constraints for variables.
    headLess    :: Map v f,
    headGreater :: Map v f,
    -- Less x y constraints. Transitively closed.
    less        :: Map v (Set v) }
  deriving (Eq, Ord, Show)

instance (PrettyTerm f, Pretty v) => Pretty (Solved f v) where
  pPrint Unsolvable = text "false"
  pPrint Tautological = text "true"
  pPrint x =
    pPrint [
      pPrint (prob x),
      pPrint (solution x),
      pPrint (headLess x),
      pPrint (headGreater x),
      pPrint (less x) ]

solve :: (Minimal f, Sized f, Ord f, Ord v) => Formula f v -> Solved f v
solve = solve1 . filter (/= FTrue) . literals
  where
    literals (p :&: q) = literals p ++ literals q
    literals (_ :|: _) = ERROR "must call split before using a context"
    literals (Equal _ _ _ _) = ERROR "must call split before using a context"
    literals p = [p]

solve1 :: (Minimal f, Sized f, Ord f, Ord v) => [Formula f v] -> Solved f v
solve1 [] = Tautological
solve1 ls
  | not (null equal) = ERROR "must call split before using a context"
  | FFalse `elem` ls = Unsolvable
  | or [ Set.member x s | (x, s) <- Map.toList less' ] = Unsolvable
  | otherwise =
      case FM.solve prob of
        Nothing -> Unsolvable
        Just sol -> Solved prob sol headLess' headGreater' less'
  where
    size = [s | Size s <- ls]
    headLess = [(unVar x, f) | HeadIs Lesser x f <- ls]
    headGreater = [(unVar x, f) | HeadIs Greater x f <- ls]
    headLess' = Map.fromListWith min headLess
    headGreater' = Map.fromListWith max headGreater
    less = [(unVar t, unVar u) | Less t u <- ls]
    less' = close less
    equal = [() | Equal{} <- ls]
    unVar (Var x) = x
    unVar _ = ERROR "must call split before using a context"
    prob = FM.problem (size ++ termAxioms ls ++ lessProb ++ headProb)
    lessProb = [var x <== var y | (x, y) <- less]
    headProb = [var x </= var y | (x, f) <- Map.toList headGreater', (y, g) <- Map.toList headLess', f >= g]

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

satisfiable :: (Ord f, Ord v) => Solved f v -> Bool
satisfiable Unsolvable = False
satisfiable _ = True

implies :: (Minimal f, Sized f, Numbered v, Ord f, Ord v) => Solved f v -> Formula f v -> Bool
implies Unsolvable _ = __
implies _ FTrue = True
implies Tautological _ = False
implies _ FFalse = False
implies form (p :&: q) = implies form p && implies form q
implies form (p :|: q) = implies form p || implies form q
implies form (Equal _ _ _ p) = implies form p
implies form (Size s) =
  isNothing (FM.solve (addConstraints ts (prob form)))
  where
    ts = FM.negateBound s:sizeAxioms (FM.bound s)
implies form (Less (Var x) (Var y)) =
  y `Set.member` Map.findWithDefault Set.empty x (less form)
implies form (HeadIs Lesser (Var x) f) =
  case Map.lookup x (headLess form) of
    Just g | g <= f -> True
    _ -> False
implies form (HeadIs Greater (Var x) f) =
  case Map.lookup x (headGreater form) of
    Just g | g >= f -> True
    _ -> False
implies _ _ = ERROR("non-split formula")

modelSize :: (Pretty v, Minimal f, Sized f, Ord f, Ord v) => Tm f v -> Solved f v -> Integer
modelSize _ Unsolvable = __
modelSize t Tautological = fromIntegral (size t)
modelSize t s = ceiling (FM.eval val (termSize t))
  where
    val x = Map.findWithDefault 1 x (solution s)

minimiseContext :: (Minimal f, Sized f, Pretty v, Ord f, Ord v) => Tm f v -> Context f v -> Context f v
minimiseContext t ctx =
  ctx { solved = s, model = toModel s }
  where
    s = minimiseSolved t (solved ctx)

minimiseSolved :: (Pretty v, Minimal f, Sized f, Ord f, Ord v) => Tm f v -> Solved f v -> Solved f v
minimiseSolved _ Unsolvable = Unsolvable
minimiseSolved _ Tautological = Tautological
minimiseSolved t s =
  s { solution = loop (solution s) }
  where
    sz = termSize t
    p = addConstraints (sizeAxioms sz) (prob s)
    loop m
      | x < 0 = __
      | otherwise =
          case FM.solve (addConstraints [sz <== fromIntegral (n-1)] p) of
            Nothing -> m
            Just m -> loop m
      where
        x = FM.eval val sz
        val v = Map.findWithDefault 1 v m
        n :: Integer
        n = ceiling x

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

instance (Minimal f, Sized f) => Sized (Extended f v) where
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
      bound (Just f) = text ", >" <+> pPrint f
  pPrint (UnconstrainedVar x) = pPrint x

instance (PrettyTerm f, Pretty v) => PrettyTerm (Extended f v) where
  termStyle (Original f) = termStyle f
  termStyle _ = curried

toModel :: (Ord f, Ord v) => Solved f v -> Map v (Extended f v)
toModel Unsolvable = __
toModel Tautological = Map.empty
toModel s =
  Map.fromList [(x, var x i) | (x, i) <- zip (sortBy cmp vs) [0..]]
  where
    vs = usort (Set.toList (FM.pvars (prob s)) ++
                Map.keys (headLess s) ++
                Map.keys (headGreater s) ++
                concat [(x:Set.toList s) | (x, s) <- Map.toList (less s)])
    cmp x y
      | y `Set.member` Map.findWithDefault Set.empty x (less s) = LT
      | x `Set.member` Map.findWithDefault Set.empty y (less s) = GT
      | otherwise = compare x y
    var x i =
      ConstrainedVar x i
        (varSize x)
        (try minimum
         (catMaybes
          [ Map.lookup y (headLess s)
          | y <- x:filter (sameSize x) (Set.toList (Map.findWithDefault Set.empty x (less s))) ]))
    varSize x = Map.findWithDefault 1 x (solution s)
    sameSize x y = varSize x == varSize y
    try _ [] = Nothing
    try f xs = Just (f xs)

trueIn :: (Sized f, Minimal f, Ord f, Ord v) => Map v (Extended f v) -> Formula f v -> Bool
trueIn _ FTrue = True
trueIn _ FFalse = False
trueIn model (p :&: q) = trueIn model p && trueIn model q
trueIn model (p :|: q) = trueIn model p || trueIn model q
trueIn model (Size p) =
  FM.boundTrue (fmap (eval val) p)
  where
    val x =
      case Map.lookup x model of
        Just (ConstrainedVar _ _ k _) -> k
        _ -> 1
trueIn _ (HeadIs Lesser (Fun f _) g) = f < g
trueIn _ (HeadIs Greater (Fun f _) g) = f > g
trueIn model (HeadIs Lesser (Var x) f) =
  case Map.lookup x model of
    Nothing -> UnconstrainedVar x < Original f
    Just t  -> t < Original f
trueIn model (HeadIs Greater (Var x) f) =
  case Map.lookup x model of
    Nothing -> UnconstrainedVar x > Original f
    Just t  -> t > Original f
trueIn model (Less t u) =
  toExtended model t `simplerThan` toExtended model u
trueIn model (Equal t u p q) =
  (t == u && trueIn model p) || trueIn model q
