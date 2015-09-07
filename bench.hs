{-# LANGUAGE PatternGuards #-}
import Criterion.Main
import KBC.Term hiding (var, fun, isFun)
import qualified KBC.Term
import Test.QuickCheck
import Data.Int
import Data.Maybe
import KBC.Term.Core hiding (subst)
import KBC.Term.Nested

t0, t1, u0, u1, t2, t, u :: KBC.Term.Term Int
t0 = flatten $ fun 0 [var 0, fun 0 [var 0, fun 0 [fun 0 [var 0, var 1], var 2]]]
u0 = flatten $ fun 0 [fun 0 [fun 2 [fun 2 [var 2, var 2], var 1], fun 0 [fun 2 [var 2, var 2], var 3]], fun 0 [fun 0 [fun 2 [fun 2 [var 2, var 2], var 1], fun 0 [fun 2 [var 2, var 2], var 3]], fun 0 [fun 0 [fun 0 [fun 2 [fun 2 [var 2, var 2], var 1], fun 0 [fun 2 [var 2, var 2], var 3]], fun 2 [fun 2 [var 2, var 2], var 1]], fun 2 [var 2, var 2]]]]

t1 = flatten $ fun 0 [fun 1 [var 0], fun 1 [var 1]]
u1 = flatten $ fun 0 [fun 1 [fun 0 [fun 2 [], fun 3 []]], fun 1 [fun 0 [fun 4 [], fun 5 []]]]

t2 = flatten $ fun 0 [var 0, fun 1 [var 1, fun 1 [var 1, var 1]]]
u2 = flatten $ fun 0 [fun 0 [var 2, var 2], var 2]

fun f ts = KBC.Term.Nested.Fun (MkFun f) ts
var = KBC.Term.Nested.Var . MkVar

t = t0
u = u0

Just sub = match t u

mgu1 t u = let Just sub = unifyTri t u in iterSubst sub t
mgu2 t u = let Just sub = unify t u in subst sub t

Just sub' = unifyTri t2 u2
Just csub' = unify t2 u2

main = do
  print t
  print u
  print (match t u)
  print (subst sub t)
  print (unifyTri t2 u2)
  print (close sub')
  print (iterSubst sub' t2)
  print (iterSubst sub' u2)
  print (mgu1 t2 u2)
  print (mgu2 t2 u2)
  print (t == t)
  print (subst sub t == u)
  print (iterSubst sub' t2 == iterSubst sub' u2)
  print (subst csub' t1 == iterSubst sub' t1)
  print (mgu1 t2 u2 == mgu2 t2 u2)
  print (subst csub' t2 == iterSubst sub' t2)
  defaultMain [
    bench "eq-t" (whnf (uncurry (==)) (t, t)),
    bench "eq-u" (whnf (uncurry (==)) (u, u)),
    bench "match" (whnf (fromJust . uncurry match) (t, u)),
    bench "subst" (whnf (uncurry subst) (sub, t)),
    bench "unifyTri" (whnf (fromJust . uncurry unifyTri) (t2, u2)),
    bench "unify-close" (whnf (uncurry unify) (t2, u2)),
    bench "unify-subst-iter1" (whnf (uncurry iterSubst) (sub', t2)),
    bench "unify-subst-iter2" (whnf (uncurry iterSubst) (sub', u2)),
    bench "unify-subst-closed1" (whnf (uncurry subst) (csub', t2)),
    bench "unify-subst-closed2" (whnf (uncurry subst) (csub', u2)),
    bench "mgu-tri" (whnf (uncurry mgu1) (t2, u2)),
    bench "mgu-close" (whnf (uncurry mgu2) (t2, u2)),
    bench "make-constant" (whnf (uncurry KBC.Term.fun) (MkFun 0, [])),
    bench "make-constant-cfun" (whnf (uncurry KBC.Term.Nested.Fun) (MkFun 0, [])),
    bench "baseline" (whnf (uncurry (+)) (0 :: Int, 0))]

prop :: Bool -> NonNegative (Small Int) -> NonNegative (Small Int) -> Property
prop fun_ (NonNegative (Small index_)) (NonNegative (Small size_)) =
  (isFun x, index x, size x) === (fun_, index_, size_)
  where
    x = toSymbol (fromSymbol (Symbol fun_ index_ size_))

prop2 :: Int64 -> Property
prop2 x = fromSymbol (toSymbol x) === x
