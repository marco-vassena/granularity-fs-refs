open import Data.Nat hiding (_≟_)
open import Lattice

module Generic.Store.Valid
  (Ty : Set)
  (Value : Ty → Set)
  {{𝑳 : Lattice}}
  (Validⱽ : ∀ {τ} → ℕ → Value τ  → Set) where
--  (∥_∥ⱽ : ∀ {τ} → Value τ → ℕ) where

open import Generic.Store Ty Value
open import Generic.Memory.Valid Ty Value Validⱽ public

Validˢ : ℕ → Store → Set
Validˢ n Σ = ∀ ℓ → Validᴹ n (Σ ℓ)

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

update-validˢ : ∀ {Σ ℓ} {M : Memory ℓ} n → Validˢ n Σ → Validᴹ n M → Validˢ n (Σ [ ℓ ↦ M ]ˢ)
update-validˢ {Σ} {ℓ} _ isV isVᴹ ℓ' with ℓ ≟ ℓ'
update-validˢ {Σ} {ℓ} _ isV isVᴹ ℓ' | yes refl = isVᴹ
update-validˢ {Σ} {ℓ} _ isV isVᴹ ℓ' | no ¬p = isV ℓ'

postulate validˢ-⊆ᴴ : ∀ {Σ n n'} → n ≤ n' → Validˢ n Σ → Validˢ n' Σ -- Unused
