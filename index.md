---
title: Twee, an equational theorem prover
menutitle: Home
order: 1
---

# Twee, an equational theorem prover

Twee is a theorem prover for equational logic. It takes as input two sets of
equations, the _axioms_ and the _conjectures_, and tries to prove the
conjectures from the axioms. See the [installation](installation) page for how
to get a copy; you may also want to look at the short [manual](manual).

The input problems should be written in [TPTP](http://tptp.org) format.
Here is an example problem from group theory. We state that there is an
associative binary function `f` with a right identity and right inverse:

```prolog
fof(right_identity, axiom,
    ![X]: f(X, e) = X).
fof(right_inverse, axiom,
    ![X]: f(X, i(X)) = e).
fof(associativity, axiom,
    ![X, Y, Z]: f(X, f(Y, Z)) = f(f(X, Y), Z)).
```

Then we state the conjecture that the right inverse is also a left inverse:

```
fof(left_inverse, conjecture,
    ![X]: f(i(X),X) = e).
```

We can put this problem into a file, say `group.p`, and run `twee group.p`. Twee
spits out the following proof; at the bottom it says `Theorem` which tells us
the conjecture is true.

```
Goal 1 (left_inverse): f(i(X), X) = e.
Proof:
  f(i(X), X)
= { by axiom 1 (right_identity) }
  f(i(X), f(X, e))
= { by axiom 2 (right_inverse) }
  f(i(X), f(X, f(i(X), i(i(X)))))
= { by axiom 3 (associativity) }
  f(i(X), f(f(X, i(X)), i(i(X))))
= { by axiom 2 (right_inverse) }
  f(i(X), f(e, i(i(X))))
= { by axiom 3 (associativity) }
  f(f(i(X), e), i(i(X)))
= { by axiom 1 (right_identity) }
  f(i(X), i(i(X)))
= { by axiom 2 (right_inverse) }
  e

RESULT: Theorem (the conjecture is true).
```
