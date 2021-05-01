---
title: Installing twee
menutitle: Installation
order: 3
---

# Installing twee

Twee is written in Haskell - so you will need to have GHC, the Glasgow
Haskell Compiler, installed. The easiest way is to install Stack, a
Haskell package manager, from [here](https://www.haskell.org/downloads/#stack).
Then run

    stack install twee twee-lib jukebox minisat

which should put a copy of twee in your `~/.local/bin` directory.
You can either add `~/.local/bin` to your `PATH` or copy the `twee`
binary somewhere more convenient.

If you have a suitable version of LLVM installed, you can pass the
option `--flag twee-lib:llvm` to `stack install` to get a somewhat
faster binary.

If you want a tarball of the latest version, you can get it
[here](https://github.com/nick8325/twee/archive/twee-2.3.tar.gz).
To install it, just type `stack install`.

## Installing from binary

If you use Linux on amd64 you can download a
<a href="https://github.com/nick8325/twee/releases/download/twee-2.3/twee-2.3-linux-amd64">binary</a> release.

## System on TPTP

Twee is also available on
[System on TPTP](http://www.cs.miami.edu/~tptp/cgi-bin/SystemOnTPTP)
(thanks Geoff!)
