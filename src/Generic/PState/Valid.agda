open import Lattice
open import Data.Nat
open import Generic.Valid

module Generic.PState.Valid
  {{𝑳 : Lattice}}
  {Ty₁ : Set} {Ty₂ : Set}
  {Value₁ : Ty₁ → Set} {Value₂ : Ty₂ → Set}
  -- (Valid₁ : ∀ {τ} → ℕ → Value₁ τ  → Set)
  -- (Valid₂ : ∀ {τ} → ℕ → Value₂ τ  → Set) where
  {∥_∥₁ : ∀ {τ} → Value₁ τ → ℕ}
  {∥_∥₂ : ∀ {τ} → Value₂ τ → ℕ}
  (𝑽₁ : IsValid Ty₁ Value₁ ∥_∥₁)
  (𝑽₂ : IsValid Ty₂ Value₂ ∥_∥₂) where
--  where

open import Generic.Valid

open import Generic.PState.Base Value₁ Value₂
open import Data.Product
open import Generic.Store.Valid 𝑽₁ public
open import Generic.Heap.Valid 𝑽₂ public

open PState

record Validᴾ (p : PState) : Set where
  constructor ⟨_,_⟩
  field
    validˢ : Validˢ ∥ heap p ∥ᴴ (store p)
    validᴴ : Validᴴ (heap p)
