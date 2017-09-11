---
title: Installing twee
menutitle: Installation
order: 3
---

# Installing twee

Twee is written in Haskell - so you will need to have GHC, the Glasgow
Haskell Compiler, installed. Get it from
[here](https://www.haskell.org/downloads); the "minimal installer"
will be fine.

The easiest way to install twee is then to run

    cabal update
    cabal install twee

which should put a copy of twee in your `~/.cabal/bin` directory.
You can either add `~/.cabal/bin` to your `PATH` or copy the `twee`
binary somewhere more convenient.

If you have a suitable version of LLVM installed, you can pass the
option `-fllvm` to `cabal install` to get a somewhat faster binary.

If you want a tarball of the latest version, you can get it
[here](https://github.com/nick8325/twee/archive/twee-2.0.tar.gz).
However, you will still need to use `cabal` to install it; just type
`cabal install` instead of `cabal install twee`.

## Installing from binary

If you use Linux on amd64 you can download a
<a href="https://github.com/nick8325/twee/releases/download/twee-2.0/twee-2.0-linux-amd64">binary</a> release.

## System on TPTP

Twee is also available on
[System on TPTP](http://www.cs.miami.edu/~tptp/cgi-bin/SystemOnTPTP)
(thanks Geoff!)
