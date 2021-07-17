---
title: Twee manual
menutitle: Manual
order: 2
---

# Manual

The basic way to run twee is as follows:

    twee name_of_problem.p

The problem must be in [TPTP](http://tptp.org) FOF or CNF or TFF format; you can
find a worked example on the [main page](.) and lots of test problems
[here](https://github.com/nick8325/twee/tree/master/tests). Twee accepts any
problem which after clausification consists only of unit equalities and Horn clauses.
In practice this means that the input problem can freely use
quantification, both universal and existential, in any combination.

The input file can have any number of conjectures. Twee will then solve each of
them one at a time and report the final result. If the conjecture has an
existential quantifier, twee will give you a witness, if possible.

The input file can use multiple types, although this slightly reduces the
efficiency of the prover, and twee does not understand any built-in theories
such as arithmetic. Currently, using types also litters the proof with terms of
the form `$to_foo(t)`, which are used internally to keep track of types. When
reading the proof you should read `$to_foo(t)` as simply `t`.

## Verbosity

The `--quiet` flag disables all progress output.

The `--no-proof` flag suppresses printing the final proof.

## Different strategies

If twee fails to prove your conjecture, you might have more luck with
a different strategy. Here are a couple to try:

* `--no-flatten-goal` - disable twee's support for goal-directed search
* `--lhs-weight 1` - adjust the scoring of critical pairs

## Infix operators

As an extension to TPTP syntax, twee supports infix operators.
For example, you can write

```
cnf(commutativity, axiom, X+Y = Y+X).
```

which is equivalent to

```
cnf(commutativity, axiom, '+'(X,Y) = '+'(Y, X)).
```

You can find a longer example [https://github.com/nick8325/twee/blob/master/tests/deriv.p](here).

Operators may not include characters such as `&` and `|` that are used
in TPTP connectives. This rules out quite a lot of useful characters.
However, twee supports Unicode input, so you can often find a suitable
Unicode character to use (see [here](https://en.wikipedia.org/wiki/List_of_mathematical_symbols_by_subject)
for the more common ones).

## TPTP support

Twee respects the `TPTP` environment variable for finding problems and axioms.
For example, `twee BOO067-1.p` will find `$TPTP/Problems/BOO/BOO067-1.p`.
You can add extra search directories using the `--root` option, which takes a
comma-separated list of directories and can be passed multiple times.

The `--tstp` flag causes twee to print `SZS status` lines in the official
syntax. The flags `--tstp --formal-proof` cause it to print a
`CNFRefutation` in the formal TSTP format when it proves the conjecture.

## Resource limits

Twee has several options for stopping the proof search after a certain resource
bound is reached.

`--max-term-size n` discards any rewrite rule whose left-hand side is longer
than `n` symbols.

`--max-cps n` stops twee after it has considered `n` critical pairs.

`--max-cp-depth n` discards any critical pair whose "distance" to the axioms is
more than `n`. For example, `--max-cp-depth 1` only generates critical pairs
directly from the axioms, `--max-cp-depth 2` generates critical pairs from
_those_ critical pairs, and so on.

If any of these modes are specified, twee will print `GaveUp` rather than
`Satisfiable` when it runs out of critical pairs to try.

## Expert options

There are also several options for tweaking heuristics and so on. You can get a
brief description of them with `twee --expert-help`. Apart from that, they
remain undocumented for now :)
