# From Fine- to Coarse-Grained Dynamic Information Flow Control and Back - Mechanized Proofs

This repository contains Agda mechanized proofs of the paper "From Fine- to
Coarse-Grained Dynamic Information Flow Control and Back" by Vassena, Russo,
Vineet, Deepak, Stefan.

The script `compile.sh` compiles the source files (`src`) and generates
highlighted, hyperlinked web pages from the source in directory `html`.

You can typecheck the proofs with:

  - Agda version 2.5.3 
  - The Agda standard library v0.16
  - `--rewriting` flag

The proof of non-interference requires the axiom of function extensionality,
which is assumed as a postulate in `Generic/Store/Base.agda`.
