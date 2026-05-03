-- Tests for equation and rule ordering.

module Ordering(tests) where

import Common
import Test.QuickCheck hiding (Function, Fun)
import Twee.Base
import Twee.Constraints
import Twee.Equation
import Twee.Utils
import Twee.Rule
import Twee.CP
import Twee.Proof
import qualified Twee.KBO as KBO
import Data.Maybe
import Test.Tasty
import Test.Tasty.QuickCheck

-- TODO: this only checks for the default order (KBO)
-- But very similar things are covered in TermOrder.hs.
prop_reducesWith_correct :: Model Func -> Pair Func -> Subst Func -> Property
prop_reducesWith_correct model (Pair t u) sub =
  counterexample ("Model: " ++ prettyShow model) $
  counterexample ("Subst: " ++ prettyShow sub) $
  conjoin $ do
    let cp = CriticalPair (t :=: u) Nothing (axiom (Axiom 0 "dummy" (t :=: u)))
    r@Rule{lhs = t', rhs = u'} <- map (flip orient (certify (cp_proof cp))) (map cp_eqn (split cp))
    return $
      counterexample ("LHS:   " ++ prettyShow t') $
      counterexample ("RHS:   " ++ prettyShow u') $
      counterexample ("Rule:  " ++ prettyShow r) $
      counterexample ("Inst:  " ++ prettyShow (subst sub r)) $
      counterexample ("Res:   " ++ show (lessIn model (subst sub u') (subst sub t'))) $
      not (reducesInModel model r sub) || isJust (lessIn model (subst sub u') (subst sub t'))

prop_simplerThan_irreflexive :: Equation Func -> Bool
prop_simplerThan_irreflexive eq =
  not (eq `simplerThan` eq)

prop_simplerThan_antisymmetric :: Equation Func -> Equation Func -> Property
prop_simplerThan_antisymmetric eq1 eq2 =
  eq1 `simplerThan` eq2 ==> not (eq2 `simplerThan` eq1)

prop_order_simplerThan :: Equation Func -> Equation Func -> Bool
prop_order_simplerThan eq1 eq2 =
  eq1 `simplerThan` eq2 || eq2 `simplerThan` eq1 || order eq1 == order eq2

prop_order_rearrange :: Equation Func -> Property
prop_order_rearrange eq@(t :=: u) =
  let vs = usort (vars eq) in
  forAll (shuffle vs) $ \ws swap (NonNegative n) ->
    let
      Just sub = listToSubst (zip vs [build (var (V (w + n))) | V w <- ws])
      eq' = subst sub (if swap then u :=: t else t :=: u)
    in
      canonicalise (order eq) === canonicalise (order eq')

prop_order_size :: Equation Func -> Property
prop_order_size eq =
  let eq' = order eq in
  counterexample (show eq) $
  KBO.size (eqn_lhs eq') >= KBO.size (eqn_rhs eq')

prop_order_erase :: Equation Func -> Property
prop_order_erase eq =
  let eq' = order eq in
  counterexample (show eq) $
  eqn_rhs (ground eq') `lessEqSkolem` eqn_lhs (ground eq')

tests :: TestTree
tests =
  localOption (QuickCheckTests 1000000) $
  testGroup "Equation ordering" [
    testProperty "reducesWith respects KBO" prop_reducesWith_correct,
    testProperty "simplerThan irreflexive" prop_simplerThan_irreflexive,
    testProperty "simplerThan antisymmetric" prop_simplerThan_antisymmetric,
    testProperty "order/simplerThan trichotomogy" prop_order_simplerThan,
    testProperty "order invariant under rearrangement" prop_order_rearrange,
    testProperty "order respects size" prop_order_size,
    testProperty "order respects term order of erase terms" prop_order_erase ]
