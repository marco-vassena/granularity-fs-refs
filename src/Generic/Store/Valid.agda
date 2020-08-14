open import Data.Nat
open import Lattice

module Generic.Store.Valid
  (Ty : Set)
  (Value : Ty → Set)
  {{𝑳 : Lattice}}
  (∥_∥ⱽ : ∀ {τ} → Value τ → ℕ) where

open import Generic.Store Ty Value
open import Generic.Memory.Valid Ty Value ∥_∥ⱽ public

Validˢ : ℕ → Store → Set
Validˢ n Σ = ∀ ℓ → Validᴹ n (Σ ℓ)
