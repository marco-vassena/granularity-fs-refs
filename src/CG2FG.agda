-- CG → FG translation and correctness

open import Lattice

module CG2FG {{𝑳 : Lattice}} where

-- Type translation.
open import CG2FG.Types

-- Translation for all other categories.
open import CG2FG.Syntax

-- Cross-language logical relation (semantics equivalence up to extra
-- label annotations).
open import CG2FG.CrossEq

-- Semantics preservation.
open import CG2FG.Correct

-- Recovery of TINI
open import CG2FG.Recovery
