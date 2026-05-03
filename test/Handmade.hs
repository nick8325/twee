-- A few handmade test cases for interactive use.

module Handmade where

import Common
import Twee.Base
import Twee.Equation
import Twee.Proof
import Twee.Rule
import qualified Twee.Index as Index

a = con (Sym (F 3 1))
b = con (Sym (F 4 2))
zero = con (Sym (F 5 1))
plus t u = app (Sym (F 6 1)) [t, u]
times t u = app (Sym (F 7 1)) [t, u]
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
