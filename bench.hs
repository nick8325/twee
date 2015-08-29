{-# LANGUAGE PatternGuards #-}
import Criterion.Main
import KBC.Term
import Test.QuickCheck
import Data.Int
import Data.Maybe
import KBC.Term.Core hiding (subst)

t0, t1, u0, u1, t2, t, u :: Term Int
t0 = flattenTerm $ fun 0 [var 0, fun 0 [var 0, fun 0 [fun 0 [var 0, var 1], var 2]]]
u0 = flattenTerm $ fun 0 [fun 0 [fun 2 [fun 2 [var 2, var 2], var 1], fun 0 [fun 2 [var 2, var 2], var 3]], fun 0 [fun 0 [fun 2 [fun 2 [var 2, var 2], var 1], fun 0 [fun 2 [var 2, var 2], var 3]], fun 0 [fun 0 [fun 0 [fun 2 [fun 2 [var 2, var 2], var 1], fun 0 [fun 2 [var 2, var 2], var 3]], fun 2 [fun 2 [var 2, var 2], var 1]], fun 2 [var 2, var 2]]]]

t1 = flattenTerm $ fun 0 [fun 1 [var 0], fun 1 [var 1]]
u1 = flattenTerm $ fun 0 [fun 1 [fun 0 [fun 2 [], fun 3 []]], fun 1 [fun 0 [fun 4 [], fun 5 []]]]

t2 = flattenTerm $ fun 0 [fun 1 [fun 2 [var 5, var 1]], fun 1 [fun 3 [var 4]]]

fun f ts = CFun (MkFun f) (fromList ts)
var = CVar . MkVar

t = t0
u = u0

(st1, st2) = share2 t1 t2

Just sub = match t u

mgu1 t u = let Just sub = unifyTri t u in iterSubst sub t
mgu2 t u = let Just sub = unify t u in subst sub t

us = CFun (MkFun 0) (fromList (replicate 10 (CSubstTerm sub (singleton t))))

Just sub' = unifyTri t1 t2
Just csub' = unify t1 t2

main = do
  print t
  print u
  print (match t u)
  print (subst sub t)
  print (unifyTri t1 t2)
  print (close sub')
  print (iterSubst sub' t1)
  print (iterSubst sub' t2)
  print (mgu1 t1 t2)
  print (mgu2 t1 t2)
  print (t == t)
  print (subst sub t == u)
  print (iterSubst sub' t1 == iterSubst sub' t2)
  print (subst csub' t1 == iterSubst sub' t1)
  print (mgu1 t1 t2 == mgu2 t1 t2)
  print (subst csub' t2 == iterSubst sub' t2)
  defaultMain [
    bench "eq-t" (whnf (uncurry (==)) (t, t)),
    bench "eq-u" (whnf (uncurry (==)) (u, u)),
    bench "match" (whnf (fromJust . uncurry match) (t, u)),
    bench "subst" (whnf (uncurry subst) (sub, t)),
    bench "subst10" (whnf flattenTerm us),
    bench "unifyTri" (whnf (fromJust . uncurry unifyTri) (t1, t2)),
    bench "unifyTri-shared" (whnf (fromJust . uncurry unifyTri) (st1, st2)),
    bench "unify-close" (whnf (uncurry unify) (t1, t2)),
    bench "unify-close-shared" (whnf (uncurry unify) (st1, st2)),
    bench "unify-subst-iter1" (whnf (uncurry iterSubst) (sub', t1)),
    bench "unify-subst-iter2" (whnf (uncurry iterSubst) (sub', t2)),
    bench "unify-subst-closed1" (whnf (uncurry subst) (csub', t1)),
    bench "unify-subst-closed2" (whnf (uncurry subst) (csub', t2)),
    bench "mgu-tri" (whnf (uncurry mgu1) (t1, t2)),
    bench "mgu-close" (whnf (uncurry mgu2) (t1, t2))]

prop :: Bool -> NonNegative (Small Int) -> NonNegative (Small Int) -> Property
prop fun_ (NonNegative (Small index_)) (NonNegative (Small size_)) =
  (isFun x, index x, size x) === (fun_, index_, size_)
  where
    x = toSymbol (fromSymbol (Symbol fun_ index_ size_))

prop2 :: Int64 -> Property
prop2 x = fromSymbol (toSymbol x) === x
