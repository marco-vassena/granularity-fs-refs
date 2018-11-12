# From Fine- to Coarse-Grained Dynamic Information Flow Control and Back - Mechanized Proofs

This repository contains Agda mechanized proofs of the paper [https://doi.org/10.1145/3290389]("From Fine- to
Coarse-Grained Dynamic Information Flow Control and Back") by Vassena, Russo,
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
- Module `Generic`: generic reusable interfaces for IFC calculi, contexts and stores.

We recommend to start to navigate the proof scripts from the top-level module
`Toc`.

The most challenging proofs are the recovery of non-interference (in both
directions, i.e., `FG2CG.Recovery` and `CG2FG.Recovery`), wherein proving
injectivity of the translation requires to use the _graph of the function_, an
inductive relation that represents the translation function and enables
from-target-to-source inductive reasoning.

## Additional Axiom
The fine to coarse semantics-preservation proof of the transformation requires
the (often used) axiom of function extensionality, which is assumed as a
postulate in `Generic/Store/Base.agda`.

## Difference from the paper
The translation from the paper and its mechanization differ in the following:
1. _Syntactic sugar_. In the paper, `x <- e1 ; e2` desugars to `bind(e1, x.e2)`
   in the proof scripts (footnote 12) and `let x = e1 in e2` to `(\x.e2) e1`
(footnote 19).
2. Term `wken` is omitted in the paper and explicit used in the proof scripts
   where needed (paragraph _Note on Environments_ on pag. 17).
3. Variables are _named_ in the paper and _unnamed_ De Bruijn in the proof
   scripts (footnote 7)
4. The `Id` type is omitted in the paper and used in the proof scripts to
   ensure injectivity (footnote 21).

