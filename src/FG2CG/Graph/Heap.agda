open import Lattice

module FG2CG.Graph.Heap {{𝑳 : Lattice}} where

open import FG2CG.Graph.Types
open import FG2CG.Graph.Value

open import Generic.Heap.Graph Graph-⟪·⟫ᵗ′ Graph-⟪·⟫ᴸ
  renaming (Graphᴴ to Fg2Cgᴴ
           ; ⌜_⌝ᴴ to mkFg2Cgᴴ
           ; ⌞_⌟ᴴ to ≡-Fg2Cgᴴ ) public
