import Lattice as L

module CG2FG.Graph {{𝑳 : L.Lattice}} where

-- The following modules define inductive relations that capture the
-- translation from fine to coarse grained for types and expressions.
-- These relations are suitable to prove properties and lemmas that
-- require back-translating terms, e.g., unlifting and injectivity.

open import CG2FG.Graph.Types public

open import CG2FG.Graph.Expr public
