-- Tests for the 'nests' function.

module Nest(tests) where

import Common
import Data.Intern
import Twee.Base
import Test.Tasty
import Test.Tasty.QuickCheck
import qualified Data.IntMap as M

-- Define 'nest' from Fuchs "The application of goal-oriented heuristics...",
-- then refine it to a more efficient version
nestf :: Func -> Term Func -> Int
nestf f _ | arity f == 0 = 0
nestf f t = hnest (Sym f) t 0 0
  where
    hnest _ (Var _) c a = max c a
    hnest _ (App _ Nil) c a = max c a
    hnest f (App g ts) c a
      | f == g = maximum [hnest f t (c+1) a | t <- unpack ts]
      | otherwise = maximum [hnest f t 0 (max c a) | t <- unpack ts]

-- a simpler version, to illustrate the meaning
nestf1 :: Func -> Term Func -> Int
nestf1 f t = hnest (Sym f) t 0
  where
    hnest _ (Var _) c = c
    hnest _ (App _ Nil) c = c
    hnest f (App g ts) c
      | f == g = maximum [hnest f t (c+1) | t <- unpack ts]
      | otherwise = max c (maximum [hnest f t 0 | t <- unpack ts])

-- a more efficient version
nestf2 :: Func -> Term Func -> Int
nestf2 f t = hnest (Sym f) (singleton t) 0 0
  where
    hnest _ Nil c a = max c a
    hnest f (Cons (Var _) ts) c a = hnest f ts c a
    hnest f (Cons (App _ Nil) ts) c a = hnest f ts c a
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
    hnest f c as Nil = M.insertWith max f c as
    hnest f c as (Cons (Var _) ts) = hnest f c as ts
    hnest f c as (Cons (App _ Nil) ts) = hnest f c as ts
    hnest f c as (Cons (App g ts) us) =
      let as' = hnest (symId g) (if f == symId g then c+1 else 1) as ts
      in hnest f c as' us

prop_nest_1 :: Func -> Term Func -> Property
prop_nest_1 f t = nestf f t === nestf1 f t

prop_nest_2 :: Func -> Term Func -> Property
prop_nest_2 f t = nestf f t === nestf2 f t

prop_nest_3 :: Func -> Term Func -> Property
prop_nest_3 f t =
  nestf f t === M.findWithDefault 0 (symId (Sym f)) (nestf3 t)

prop_nests :: Func -> TermList Func -> Property
prop_nests f ts =
  maximum (0:map (nestf f) (unpack ts)) ===
  M.findWithDefault 0 (symId (Sym f)) (nests ts)

tests :: TestTree
tests =
  localOption (QuickCheckTests 100000) $
  testGroup "Nest function" [
    testProperty "nestf1 is correct" prop_nest_1,
    testProperty "nestf2 is correct" prop_nest_2,
    testProperty "nestf3 is correct" prop_nest_3,
    testProperty "nests is correct" prop_nests]
