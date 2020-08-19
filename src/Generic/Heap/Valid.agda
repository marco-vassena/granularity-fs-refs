open import Data.Nat
open import Lattice

module Generic.Heap.Valid
  (Ty : Set)
  (Value : Ty → Set)
  {{𝑳 : Lattice}}
  (Validⱽ : ∀ {τ} → ℕ → Value τ  → Set)
-- (∥_∥ⱽ : ∀ {τ} → Value τ → ℕ)
  where

open import Data.Unit hiding (_≤_)
import Generic.Container.Base ⊤ Ty Value as B
open import Generic.Heap.Base Ty Value as S
open import Generic.Heap.Lemmas Ty Value
open import Data.Product
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality

open import Generic.Container.Valid ⊤ Ty Value Validⱽ -- (λ n v → ∥ v ∥ⱽ ≤ n)
  renaming ( read-valid to read-validⱽ
--           ; snoc-valid to snoc-validᴴ
           ; write-valid to write-validᴴ
           ; tail-valid to tail-validᴴ
--           ; valid-⊆ to valid-⊆ᴴ
           )
  public

-- postulate write-validᴴ : ∀ {τ μ μ' n} {v : Value τ} → Validᴴ μ → μ' ≔ μ [ n ↦ v ]ᴴ → Validⱽ ∥ μ ∥ᴴ v → Validᴴ μ'

Validᴴ : Heap → Set
Validᴴ μ = Valid ∥ μ ∥ᴴ μ

open import Data.Sum

postulate wken-valid : ∀ {τ n n'} (v : Value τ) → n ≤ n' → Validⱽ n v → Validⱽ n' v

snoc-validᴴ′ : ∀ {τ} {μ : Heap} {v : Value τ} → Validᴴ μ →  Validⱽ (suc ∥ μ ∥ᴴ) v → Validᴴ (snocᴴ μ v)
snoc-validᴴ′ {μ = μ} {v} isV isVⱽ {n} ∈₁ with split-lookup μ v ∈₁
snoc-validᴴ′ {μ = μ} isV isVⱽ {n} ∈₁ | inj₁ ∈' = wken-valid _ snoc-≤ (isV ∈')
snoc-validᴴ′ {μ = μ} {v} isV isVⱽ {n} ∈₁ | inj₂ (refl , refl) rewrite ∥snoc∥ μ v = isVⱽ
