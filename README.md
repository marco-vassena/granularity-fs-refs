# From Fine- to Coarse-Grained Dynamic Information Flow Control and Back - Mechanized Proofs

This repository contains Agda mechanized proofs of the paper [From Fine- to Coarse-Grained Dynamic Information Flow Control and Back](https://doi.org/10.1145/3290389) by Vassena, Russo,
Vineet, Deepak, Stefan.

## Checking the proofs

The script `compile.sh` compiles the source files contained in `src` and
generates highlighted, hyperlinked web pages of the source scripts in directory
`html`.

You can typecheck the proofs with:

  - Agda version 2.5.3 
  - The Agda standard library v0.15
  - `--rewriting` flag

A docker containining all the required software is available on [Docker
Hub](https://hub.docker.com/r/marcovassena/granularity/).

## Overview
- Module `Toc`: Table of Contents with direct pointers to all the definitions and theorems of the paper.
- Module `Lattice`: security lattice, properties and proofs.
- Module `FG`: syntax, semantics, non-interference of the fine-grained calculus.
- Module `CG`: syntax, semantics, non-interference of the coarse-grained calculus.
- Module `FG2CG`: fine- to coarse-grained translation, semantics preservation and recovery of non-interference.
- Module `CG2FG`: coarse- to fine-grained translation, semantics preservation and recovery of non-interference.
- Module `Generic`: generic reusable interfaces for IFC calculi, contexts, stores, and heaps.

We recommend to start to navigate the proof scripts from the top-level module
`Toc`.

The most challenging proofs are the recovery of non-interference (in both
directions, i.e., `FG2CG.Recovery` and `CG2FG.Recovery`), wherein proving
injectivity of the translation requires to use the _graph of the function_, an
inductive relation that represents the translation function and enables
from-target-to-source inductive reasoning.

## Differences from the Paper
The translation from the paper and its mechanization differ in the following:
1. _Syntactic sugar_. In the paper, `x <- e1 ; e2` desugars to `bind(e1, x.e2)`
   in the proof scripts and `let x = e1 in e2` to `(\x.e2) e1`.
2. Term `wken` is omitted in the paper and explicit used in the proof scripts
   where needed.
3. Variables are _named_ in the paper and _unnamed_ De Bruijn in the proof
   scripts.
4. The type `Id` is omitted in the paper and used in the proof scripts to
   ensure injectivity.

## Additional Axiom
The proof of semantics preservation of the fine to coarse transformation requires
the (often used) axiom of function extensionality, which is assumed as a
postulate in `Generic.Store.Base` and used in `FG2CG.Correct`.
