-- Tests for KBO and LPO.

{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
module TermOrder(tests) where

import Common
import Twee.Base
import Twee.Constraints hiding (funs)
import Twee.Utils
import qualified Twee.KBO as KBO
import qualified Twee.LPO as LPO
import Data.Function
import Data.List
import Data.Maybe
import Test.Tasty
import Test.Tasty.QuickCheck hiding (Function, subterms)

data TermOrder f =
  TermOrder {
    to_lessEq :: Term f -> Term f -> Bool,
    to_lessIn :: Model f -> Term f -> Term f -> Maybe Strictness,
    to_lessEqSkolem :: Term f -> Term f -> Bool }

kbo :: (Function f, KBO.Sized f, KBO.ArgWeighted f) => TermOrder f
kbo =
   TermOrder {
     to_lessEq = KBO.lessEq,
     to_lessIn = KBO.lessIn,
     to_lessEqSkolem = KBO.lessEqSkolem }

lpo :: Function f => TermOrder f
lpo =
   TermOrder {
     to_lessEq = LPO.lessEq,
     to_lessIn = LPO.lessIn,
     to_lessEqSkolem = LPO.lessEqSkolem }

type OrderGen = forall prop. Testable prop => ((Term Func -> Term Func -> Bool) -> prop) -> Property

prop_subterm_reduces :: OrderGen -> Term Func -> Property
prop_subterm_reduces withLessEq t =
  withLessEq $ \lessEq ->
    conjoin [lessEq u t | u <- subterms t]

prop_erase_reduces :: OrderGen -> Term Func -> [Var] -> Property
prop_erase_reduces withLessEq t xs =
  withLessEq $ \lessEq ->
    erase xs t `lessEq` t

prop_antisymmetric :: OrderGen -> Pair Func -> Property
prop_antisymmetric withLessEq (Pair t u) =
  t /= u ==>
  withLessEq $ \lessEq ->
    not (lessEq t u && lessEq u t)

prop_reflexive :: OrderGen -> Term Func -> Property
prop_reflexive withLessEq t =
  withLessEq $ \lessEq ->
    lessEq t t

prop_total :: OrderGen -> Pair Func -> Property
prop_total withLessEq (Pair t u) =
  withLessEq $ \lessEq ->
    lessEq (ground t) (ground u) || lessEq (ground u) (ground t)

prop_skolem_correct :: TermOrder Func -> Pair Func -> Property
prop_skolem_correct TermOrder{..} (Pair t u) =
  skolemFree t && skolemFree u ==>
  to_lessEqSkolem t u === to_lessEq (skolemise t) (skolemise u)
  where
    skolemFree t = all (not . isSkolem) (funs t)
    isSkolem (Sym (Skolem _)) = True
    isSkolem _ = False

prop_lessIn_trivial :: TermOrder Func -> Pair Func -> Property
prop_lessIn_trivial TermOrder{..} (Pair t u) =
  to_lessIn (modelFromOrder []) t u === lessEq' t u
  where
    lessEq' t u
      | to_lessEq t u = Just (if isJust (unify t u) then Nonstrict else Strict)
      | otherwise = Nothing

prop_lessIn_antisymmetric :: TermOrder Func -> Model Func -> Pair Func -> Bool
prop_lessIn_antisymmetric TermOrder{..} model (Pair t u) =
  not (to_lessIn model t u == Just Strict && isJust (to_lessIn model u t))

prop_lessIn_nonstrict :: TermOrder Func -> Model Func -> Pair Func -> Property
prop_lessIn_nonstrict TermOrder{..} model (Pair t u) =
  to_lessIn model t u == Just Nonstrict ==>
  isJust (unify t u)

prop_lessIn_permutation :: TermOrder Func -> Term Func -> Property
prop_lessIn_permutation TermOrder{..} t =
  let vs = nub (vars t) in
  forAll (shuffle vs) $ \ws ->
    let Just sub = listToSubst [(v, build (var w)) | (v, w) <- zip vs ws]
        u = subst sub t
        model = modelFromOrder (map Variable vs)
        weaken m = [m' | m' <- weakenModel m, and [varInModel m' v | v <- vs]]
        allModels = fixpoint (usort . concatMap weaken) [model] in
    conjoin [counterexample (prettyShow m) (isJust (to_lessIn m t u)) | m <- allModels]

prop_lessIn_instance :: TermOrder Func -> Pair Func -> Property
prop_lessIn_instance TermOrder{..} (Pair t u) =
  not (to_lessEq t u) && not (to_lessEq u t) ==>
  let vs = usort (vars t ++ vars u) in
  forAll (ground <$> genSubst vs) $ \sub ->
    case (to_lessEq (subst sub t) (subst sub u), to_lessEq (subst sub u) (subst sub t)) of
      (False, False) ->
        error "partial on ground terms"
      (True, True) ->
        counterexample "Equal terms" $
        subst sub t === subst sub u
      (True, False) ->
        counterexample "t < u" $
        property $ isNothing (to_lessIn (modelFromSubst sub) u t)
      (False, True) ->
        counterexample "t > u" $
        property $ isNothing (to_lessIn (modelFromSubst sub) t u)
  where
    modelFromSubst =
      modelFromOrder' . map (map (Variable . fst)) . groupBy ((==) `on` snd) . sortBy ord . substToList
    ord (_, t) (_, u) =
      case (to_lessEq t u, to_lessEq u t) of
        (False, False) -> error "partial on ground terms"
        (False, True)  -> GT
        (True,  False) -> LT
        (True,  True)  -> if t == u then EQ else error "not antisymmetric"

prop_lpo_basic :: Pair Func -> Property
prop_lpo_basic (Pair t u) =
  minimal `notElem` funs t ==>
  LPO.lessEq t u === LPO.lessEqBasic t u

lessEqTests :: OrderGen -> [TestTree]
lessEqTests withLessEq = [
  testProperty "Order respects subterms" (prop_subterm_reduces withLessEq),
  testProperty "Order respects erasure" (prop_erase_reduces withLessEq),
  testProperty "Order is antisymmetric" (prop_antisymmetric withLessEq),
  testProperty "Order is reflexive" (prop_reflexive withLessEq),
  testProperty "Order is total on ground terms" (prop_total withLessEq)]

orderTests :: TermOrder Func -> [TestTree]
orderTests order@TermOrder{..} = [
  testGroup "Basic order" (lessEqTests (\p -> property (p to_lessEq))),
  testGroup "Skolemised order" $
    lessEqTests (\p -> property (p to_lessEqSkolem)) ++
    [testProperty "Order agrees with basic order" (prop_skolem_correct order)],
  testGroup "Model-based order" $
    lessEqTests (\p ->
      property $ \model -> p (\t u -> isJust (to_lessIn model t u))) ++
    [testProperty "Order is correct with empty model" (prop_lessIn_trivial order),
     testProperty "Order is correct with permutations" (prop_lessIn_permutation order),
     testProperty "Order only gives non-strict when necessary" (prop_lessIn_nonstrict order),
     testProperty "Order is strongly antisymmetric" (prop_lessIn_antisymmetric order),
     testProperty "Order is sound" (prop_lessIn_instance order)]]

tests :: TestTree
tests =
  localOption (QuickCheckTests 1000000) $
  testGroup "Term ordering"
    [testGroup "KBO" (orderTests kbo),
     testGroup "LPO" $
       [testProperty "Basic order agrees with simple implementation" prop_lpo_basic] ++
       orderTests lpo]
