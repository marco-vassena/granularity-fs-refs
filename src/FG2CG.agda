import Lattice as L

module FG2CG (𝑳 : L.Lattice) where

-- Translation for types and contexts
open import FG2CG.Types

-- Translation for all other categories
open import FG2CG.Syntax

-- The translation is semantics preserving
open import FG2CG.Correct

-- Recovery of TINI
open import FG2CG.Recovery
