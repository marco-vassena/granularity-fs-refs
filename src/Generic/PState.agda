open import Lattice
open import Generic.Bijection

module Generic.PState
  {{𝑳 : Lattice}}
  (Ty₁ : Set) (Ty₂ : Set)
  (Value₁ : Ty₁ → Set) (Value₂ : Ty₂ → Set)
  where

open import Generic.PState.Base Value₁ Value₂ public
