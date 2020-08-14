open import Data.Nat
open import Lattice

module Generic.Heap.Valid
  (Ty : Set)
  (Value : Ty → Set)
  {{𝑳 : Lattice}}
  (∥_∥ⱽ : ∀ {τ} → Value τ → ℕ) where

open import Generic.Heap.Base Ty Value as S
open import Data.Unit hiding (_≤_)
open import Data.Product

Validᴴ : Heap → Set
Validᴴ Σ = ∀ {n τ} {v : Value τ } → n ↦ v ∈ᴴ Σ → ∥ v ∥ⱽ ≤ ∥ Σ ∥ᴴ
