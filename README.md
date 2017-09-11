This is twee, an equational theorem prover.

The version in this git repository is likely to be unstable!
To install the latest stable version, run:

    cabal install twee

If you have LLVM installed, you can get a slightly faster version by
running:

    cabal install twee -fllvm

If you really want the latest unstable version, run `cabal install` in
this repository. You will most likely need the latest git version of
Jukebox, from https://github.com/nick8325/jukebox, too - and things
may break from time to time.

Afterwards, run `twee nameofproblem.p`. The problem should be in TPTP
format (http://www.tptp.org). You can find a few examples in the
`tests` directory. All axioms and conjectures must be equations, but
you can freely use quantifiers. If it succeeds in proving your
problem, twee will print a human-readable proof.

For the official manual, see http://nick8325.github.io/twee.
