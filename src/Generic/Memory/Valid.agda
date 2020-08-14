open import Lattice
open import Data.Nat

module Generic.Memory.Valid
   {{𝑳 : Lattice}} (Ty : Set) (Value : Ty → Set) (∥_∥ⱽ : ∀ {τ} → Value τ → ℕ)
  where

open import Generic.Memory.Base Ty Value
open import Data.Unit hiding (_≤_)
open import Data.Product

Validᴹ : ∀ {ℓ} → ℕ → Memory ℓ → Set
Validᴹ n [] = ⊤
Validᴹ n (v ∷ M) = ∥ v ∥ⱽ ≤ n × Validᴹ n M
