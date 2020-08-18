open import Data.Nat
open import Lattice

module Generic.Heap.Valid
  (Ty : Set)
  (Value : Ty → Set)
  {{𝑳 : Lattice}}
  (Validⱽ : ∀ {τ} → ℕ → Value τ  → Set)
-- (∥_∥ⱽ : ∀ {τ} → Value τ → ℕ)
  where

open import Generic.Heap.Base Ty Value as S
open import Data.Unit hiding (_≤_)
open import Data.Product

open import Generic.Container.Valid ⊤ Ty Value Validⱽ -- (λ n v → ∥ v ∥ⱽ ≤ n)
  renaming ( read-valid to read-validⱽ
           ; snoc-valid to snoc-validᴴ
           ; write-valid to write-validᴴ
           ; tail-valid to tail-validᴴ
           ; valid-⊆ to valid-⊆ᴴ ) public

Validᴴ : Heap → Set
Validᴴ μ = Valid ∥ μ ∥ᴴ μ

postulate snoc-validᴴ′ : ∀ {τ μ} {v : Value τ} → Validᴴ μ →  Validⱽ (suc ∥ μ ∥ᴴ) v → Validᴴ (snocᴴ μ v)

-- postulate write-validᴴ : ∀ {τ μ μ' n} {v : Value τ} → Validᴴ μ → μ' ≔ μ [ n ↦ v ]ᴴ → Validⱽ ∥ μ ∥ᴴ v → Validᴴ μ'
