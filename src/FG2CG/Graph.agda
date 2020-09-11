import Lattice as L

module FG2CG.Graph (𝑳 : L.Lattice) where

-- The following modules define several inductive relations that
-- capture the translation for most of the categories of the calculus.
-- These relations are suitable to prove properties and lemmas that
-- require back-translating terms, e.g., unlifting and injectivity.

open import FG2CG.Graph.Types public

open import FG2CG.Graph.Value public

open import FG2CG.Graph.Expr public

open import FG2CG.Graph.Memory public

-- open import FG2CG.Graph.Heap public
