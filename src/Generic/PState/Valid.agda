open import Lattice
open import Data.Nat

module Generic.PState.Valid
  {{𝑳 : Lattice}}
  {Ty₁ : Set} {Ty₂ : Set}
  {Value₁ : Ty₁ → Set} {Value₂ : Ty₂ → Set}
  (Valid₁ : ∀ {τ} → ℕ → Value₁ τ  → Set)
  (Valid₂ : ∀ {τ} → ℕ → Value₂ τ  → Set) where
  -- (∥_∥₁ : ∀ {τ} → Value₁ τ → ℕ)
  -- (∥_∥₂ : ∀ {τ} → Value₂ τ → ℕ)
--  where

open import Generic.PState.Base Ty₁ Ty₂ Value₁ Value₂
open import Data.Product
open import Generic.Store.Valid Ty₁ Value₁ Valid₁ public
open import Generic.Heap.Base Ty₂ Value₂
open import Generic.Heap.Valid Ty₂ Value₂ Valid₂ public

open PState

record Validᴾ (p : PState) : Set where
  constructor ⟨_,_⟩
  field
    validˢ : Validˢ ∥ heap p ∥ᴴ (store p)
    validᴴ : Validᴴ (heap p)

-- data Validᴾ : PState → Set where
--   ⟨_,_⟩ : ∀ {Σ μ} → Validˢ ∥ μ  ∥ᴴ Σ → Validᴴ μ → Validᴾ ⟨ Σ , μ ⟩
