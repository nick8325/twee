{-# LANGUAGE TemplateHaskell, FlexibleInstances, FlexibleContexts, UndecidableInstances, StandaloneDeriving, ScopedTypeVariables, TupleSections, DeriveGeneric, DerivingVia, DeriveAnyClass #-}
module Main where

import Twee.Constraints
import Twee.Term hiding (subst, canonicalise, F)
import Twee.Term.Core hiding (F)
import Test.QuickCheck hiding (Function, Fun)
import Test.QuickCheck.All
import Twee.Pretty
import Twee.CP
import Twee.Proof
import qualified Twee.KBO as Ord
import Text.PrettyPrint
import Twee.Base hiding (F)
import Twee.Rule
import Twee.Equation
import Control.Monad
import qualified Data.Map as Map
import Data.Maybe
import Data.Ord
import Data.List hiding (singleton)
import Data.Typeable
import qualified Twee.Index as Index
import Data.Int
import GHC.Generics
import Twee.Utils
import qualified Data.IntMap as M
import qualified Twee.Index as Index

data Func = F Int Integer deriving (Eq, Ord, Show, Labelled)

instance Pretty Func where
  pPrint (F 3 _) = text "a"
  pPrint (F 4 _) = text "b"
  pPrint (F 5 _) = text "zero"
  pPrint (F 6 _) = text "plus"
  pPrint (F 7 _) = text "times"
  pPrint (F f _) = text "f" <#> int f
instance PrettyTerm Func
instance Arbitrary (Subst Func) where
  arbitrary = fmap fromJust (fmap listToSubst (liftM2 zip (fmap nub arbitrary) (infiniteListOf arbitrary)))
instance Arbitrary Func where
  arbitrary = F <$> choose (0, 2) <*> choose (1, 3)
instance Minimal Func where
  minimal = fun (F 0 1)
instance Ord.Sized Func where size (F _ n) = n
instance Ord.Weighted Func where argWeight _ = 1
class Arity f where
  arity :: f -> Int
instance Arity Func where
  arity (F 0 _) = 0
  arity (F 1 _) = 1
  arity (F 2 _) = 2
  arity (F 3 _) = 0 -- a
  arity (F 4 _) = 0 -- b
  arity (F 5 _) = 0 -- zero
  arity (F 6 _) = 2 -- plus
  arity (F 7 _) = 2 -- times
instance EqualsBonus Func

instance Arbitrary Var where arbitrary = fmap V (choose (0, 3))
instance (Labelled f, Ord f, Typeable f, Arbitrary f, Arity f) => Arbitrary (Fun f) where
  arbitrary = fmap fun arbitrary

instance (Labelled f, Ord f, Typeable f, Arbitrary f, Arity f) => Arbitrary (Term f) where
  arbitrary =
    sized $ \n ->
      oneof $
        [ build <$> var <$> arbitrary ] ++
        [ do { f <- arbitrary; build <$> app (fun f) <$> vectorOf (arity f) (resize ((n-1) `div` arity f) arbitrary :: Gen (Term f)) } | n > 0 ]
  shrink (App f ts0) =
    ts ++ (build <$> app f <$> shrinkOne ts)
    where
      ts = unpack ts0
      shrinkOne [] = []
      shrinkOne (x:xs) =
        [ y:xs | y <- shrink x ] ++
        [ x:ys | ys <- shrinkOne xs ]
  shrink _ = []

instance (Labelled f, Ord f, Typeable f, Arbitrary f, Arity f) => Arbitrary (TermList f) where
  arbitrary = buildList <$> listOf (arbitrary :: Gen (Term f))
  shrink = map buildList . shrink . unpack

data Pair f = Pair (Term f) (Term f) deriving Show

instance (Labelled f, Ord f, Typeable f, Arbitrary f, Arity f) => Arbitrary (Pair f) where
  arbitrary = liftM2 Pair arbitrary arbitrary
  shrink (Pair x y) =
    [ Pair x' y  | x' <- shrink x ] ++
    [ Pair x y'  | y' <- shrink y ] ++
    [ Pair x' y' | x' <- shrink x, y' <- shrink y ]

instance (Labelled f, Ord f, Typeable f, Arbitrary f, Arity f) => Arbitrary (Equation f) where
  arbitrary = do
    Pair t u <- arbitrary
    return (t :=: u)
  shrink (t :=: u) = [t' :=: u' | Pair t' u' <- shrink (Pair t u)]

instance Ordered Func where
  lessIn = Ord.lessIn
  lessEq = Ord.lessEq
  lessEqSkolem = Ord.lessEqSkolem

instance Function f => Arbitrary (Model f) where
  arbitrary = fmap (modelFromOrder . map Variable . nub) arbitrary
  shrink = weakenModel

{-
prop_1 :: Model Func -> Pair Func -> Subst Func -> Property
prop_1 model (Pair t u) sub =
  counterexample ("Model: " ++ prettyShow model) $
  counterexample ("Subst: " ++ prettyShow sub) $
  conjoin $ do
    let cp = CriticalPair (t :=: u) 0 Nothing (axiom (Axiom 0 "dummy" (t :=: u)))
    r@(Rule _ t' u') <- map orient (map cp_eqn (split cp))
    return $
      counterexample ("LHS:   " ++ prettyShow t') $
      counterexample ("RHS:   " ++ prettyShow u') $
      counterexample ("Rule:  " ++ prettyShow r) $
      counterexample ("Inst:  " ++ prettyShow (Rule Oriented (subst sub t') (subst sub u'))) $
      counterexample ("Res:   " ++ show (lessIn model (subst sub u') (subst sub t'))) $
      not (reducesInModel model r sub) || isJust (lessIn model (subst sub u') (subst sub t'))
-}

prop_2 :: Model Func -> Pair Func -> Bool
prop_2 model (Pair t u) =
  not (lessIn model t u == Just Strict && isJust (lessIn model u t))

prop_3 :: Pair Func -> Bool
prop_3 (Pair t u) =
  not (lessThan t u && lessEq u t)

prop_4 :: Pair Func -> Property
prop_4 (Pair t u) =
  t /= u ==> 
  not (lessEq t u && lessEq u t)

prop_5 :: Term Func -> Property
prop_5 t =
  lessEq t t .&&. not (lessThan t t)

prop_paths :: Term Func -> Property
prop_paths t =
  forAllShrink (choose (0, len t-1)) shrink $ \n ->
    counterexample (show (positionToPath t n)) $
    pathToPosition t (positionToPath t n) === n

prop_index :: [Term Func] -> Term Func -> Property
prop_index ts u =
  counterexample (show ts') $
  counterexample (show idx) $
  sort (catMaybes [fmap (,t) (match t u) | t <- ts']) ===
  sort (Index.matches u idx)
  where
    idx = foldr (\t -> Index.insert t t) Index.empty ts
    ts' = map canonicalise ts

newtype Terms f = Terms [Term f] deriving Show
instance (Labelled f, Ord f, Typeable f, Arbitrary f, Arity f) => Arbitrary (Terms f) where
  arbitrary = Terms <$> arbitrary
  shrink (Terms ts) =
    map Terms $
      filter (/= ts) $
      shrink ts ++ [canonicalise ts] ++ shrinkList (return . canonicalise) ts

newtype IndexOps f = IndexOps [IndexOp f] deriving Show
data IndexOp f = Add (Term f) | Delete (Term f) deriving Show

instance (Labelled f, Ord f, Typeable f, Arbitrary f, Arity f) => Arbitrary (IndexOps f) where
  arbitrary =
    sized $ \n -> IndexOps <$> take n <$> arbOps []
    where
      arbOps ts =
        frequency $
          [(2, do { t <- arbitrary; ops <- arbOps (t:ts); return (Add t:ops) })] ++
          [(1, do { t <- elements ts; ops <- arbOps (delete t ts); return (Delete t:ops) }) | not (null ts)]
  shrink (IndexOps ops) =
    IndexOps <$> shrinkList shr ops
    where
      shr (Add t) = Add <$> shrink t
      shr (Delete t) = Delete <$> shrink t


prop_index_invariant :: IndexOps Func -> Property
prop_index_invariant (IndexOps ops) =
  flip (foldr (counterexample . show)) idxs $
  property $ Index.invariant (last idxs)
  where
    idxs = scanl (\idx op -> applyIndex op idx) Index.empty ops
    applyIndex (Add t) = Index.insert t t
    applyIndex (Delete t) = Index.delete t t

deriving instance Eq Symbol
deriving instance Generic Symbol

instance Arbitrary Symbol where
  arbitrary =
    Symbol <$>
      arbitrary <*>
      fmap getLarge arbitrary <*>
      (fmap (fromIntegral . getLarge) (arbitrary :: Gen (Large Int32)) `suchThat` (> 0) `suchThat` (< 2^31))
  shrink s =
    filter ok (genericShrink s)
    where
      ok s = Twee.Term.Core.size s > 0

prop_symbol_1 :: Symbol -> Property
prop_symbol_1 s =
  withMaxSuccess 100000 $
  counterexample ("fun/index/size = " ++ show (isFun s, index s, Twee.Term.Core.size s)) $
  counterexample ("n = " ++ show (fromSymbol s)) $
  toSymbol (fromSymbol s) === twiddle s
  where
    twiddle s =
      s { index = fromIntegral (fromIntegral (index s) :: Int32) }

prop_symbol_2 :: Int64 -> Property
prop_symbol_2 n =
  withMaxSuccess 100000 $
  fromSymbol (toSymbol n) === n

prop_canonorder :: Equation Func -> Property
prop_canonorder eqn@(t :=: u) =
  let vs = usort (vars eqn) in
  forAll (shuffle vs) $ \ws swap (NonNegative n) ->
    let
      Just sub = listToSubst (zip vs [build (var (V (w + n))) | V w <- ws])
      eqn' = subst sub (if swap then u :=: t else t :=: u)
    in
      canonicalise (order eqn) === canonicalise (order eqn')

prop_canonorder2 :: Equation Func -> Equation Func -> Bool
prop_canonorder2 eqn1 eqn2 =
  eqn1 `simplerThan` eqn2 || eqn2 `simplerThan` eqn1 || order eqn1 == order eqn2

prop_canonorder3 :: Equation Func -> Property
prop_canonorder3 eq =
  let eq' = order eq in
  counterexample (show eq) $
  Ord.size (eqn_lhs eq') >= Ord.size (eqn_rhs eq')

--t :: Term Func
--t = build (app (fun (F 0)) [app (fun (F 1)) [var (V 0), var (V 1)], var (V 2)])

-- Define 'nest' from Fuchs "The application of goal-oriented heuristics...",
-- then refine it to a more efficient version
nestf :: Func -> Term Func -> Int
nestf f _ | arity f == 0 = 0
nestf f t = hnest (fun f) t 0 0
  where
    hnest _ (Var _) c a = max c a
    hnest _ (App _ Empty) c a = max c a
    hnest f (App g ts) c a
      | f == g = maximum [hnest f t (c+1) a | t <- unpack ts]
      | otherwise = maximum [hnest f t 0 (max c a) | t <- unpack ts]

-- a simpler version, to illustrate the meaning
nestf1 :: Func -> Term Func -> Int
nestf1 f t = hnest (fun f) t 0
  where
    hnest _ (Var _) c = c
    hnest _ (App _ Empty) c = c
    hnest f (App g ts) c
      | f == g = maximum [hnest f t (c+1) | t <- unpack ts]
      | otherwise = max c (maximum [hnest f t 0 | t <- unpack ts])

-- a more efficient version
nestf2 :: Func -> Term Func -> Int
nestf2 f t = hnest (fun f) (singleton t) 0 0
  where
    hnest _ Empty c a = max c a
    hnest f (Cons (Var _) ts) c a = hnest f ts c a
    hnest f (Cons (App _ Empty) ts) c a = hnest f ts c a
    hnest f (Cons (App g ts) us) c a
      | f == g = 
        let a' = hnest f ts (c+1) a
        in hnest f us c a'
      | otherwise =
        let a' = hnest f ts 0 a
        in hnest f us c a'

-- a version that does all function symbols at once
nestf3 :: Term Func -> M.IntMap Int
nestf3 t = hnest 0 0 M.empty (singleton t)
  where
    hnest f c as Empty = M.insertWith max f c as
    hnest f c as (Cons (Var _) ts) = hnest f c as ts
    hnest f c as (Cons (App _ Empty) ts) = hnest f c as ts
    hnest f c as (Cons (App g ts) us) =
      let as' = hnest (fun_id g) (if f == fun_id g then c+1 else 1) as ts
      in hnest f c as' us

prop_nest_1 :: Func -> Term Func -> Property
prop_nest_1 f t = withMaxSuccess 1000000 $ nestf f t === nestf1 f t

prop_nest_2 :: Func -> Term Func -> Property
prop_nest_2 f t = withMaxSuccess 1000000 $ nestf f t === nestf2 f t

prop_nest_3 :: Func -> Term Func -> Property
prop_nest_3 f t =
  withMaxSuccess 1000000 $
    nestf f t === M.findWithDefault 0 (fun_id (fun f)) (nestf3 t)

prop_nests :: Func -> TermList Func -> Property
prop_nests f ts =
  withMaxSuccess 1000000 $
    maximum (0:map (nestf f) (unpack ts)) ===
    M.findWithDefault 0 (fun_id (fun f)) (nests ts)

return []
main = $forAllProperties (quickCheckWithResult stdArgs { maxSuccess = 1000000 })

a = con (fun (F 3 1))
b = con (fun (F 4 2))
zero = con (fun (F 5 1))
plus t u = app (fun (F 6 1)) [t, u]
times t u = app (fun (F 7 1)) [t, u]
x = var (V 0)
y = var (V 1)

axioms = [
  build (plus x y) ==== plus y x,
  times zero x ==== zero,
  plus x zero ==== x ]
  where
    t ==== u = build t :=: build u

rules = [orient eq (certify (axiom (Axiom 0 "axiom" eq))) | eq <- axioms]

theIndex = Index.fromList [(lhs r, r) | r <- rules]

term = build (plus (times zero a) b)
strat = anywhere1 (basic (rewrite reduces theIndex))
