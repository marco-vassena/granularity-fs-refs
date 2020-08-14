open import Lattice
open import Generic.Bijection

module Generic.PState.LowEq
  {{𝑳 : Lattice}}
  {Ty₁ : Set} {Ty₂ : Set}
  {Value₁ : Ty₁ → Set} {Value₂ : Ty₂ → Set}
  (_≈⟨_⟩₁_ :  IProps.Relᴮ Ty₁ Value₁)
  (_≈⟨_⟩₂_ :  IProps.Relᴮ Ty₂ Value₂)
  (A : Label)
  where

open import Data.Product
open import Generic.Store Ty₁ Value₁
open import Generic.Heap Ty₂ Value₂
open import Generic.Store.LowEq {Ty₁} {Value₁} _≈⟨_⟩₁_ A public
open import Generic.Heap.LowEq {Ty₂} {Value₂} _≈⟨_⟩₂_ A public

open import Generic.PState.Base Ty₁ Ty₂ Value₁ Value₂ public

open PState

-- Helper L-equivalence relation for program state, which combines both store and heap
record _≈⟨_⟩ᴾ_ (p₁ : PState) (β : Bij) (p₂ : PState) : Set where
  constructor ⟨_,_⟩
  field
    store-≈ˢ : store p₁ ≈⟨ β ⟩ˢ store p₂
    heap-≈ᴴ : heap p₁ ≈⟨ β ⟩ᴴ heap p₂

private module V₁ = IProps Ty₁ Value₁
private module V₂ = IProps Ty₂ Value₂

module ≈ᴾ-Props (𝑽₁ : V₁.IsEquivalenceᴮ _≈⟨_⟩₁_) (𝑽₂ : V₂.IsEquivalenceᴮ _≈⟨_⟩₂_) where

  open ≈ˢ-Props 𝑽₁ public
  open ≈ᴴ-Props 𝑽₂ public
  open import Generic.PState.Valid {Ty₁} {Ty₂} {Value₁} {Value₂} (V₁.Dom 𝑽₁) (V₂.Dom 𝑽₂)

  refl-≈ᴾ : ∀ {p} {{validᴾ : Validᴾ p}} → p ≈⟨ ι ∥ heap p ∥ᴴ ⟩ᴾ p
  refl-≈ᴾ {{⟨ validˢ , validᴴ ⟩}} = ⟨ (refl-≈ˢ {{validˢ}}) , (refl-≈ᴴ {{validᴴ}} ) ⟩

  open SProps PState

  sym-≈ᴾ : Symmetricᴮ _≈⟨_⟩ᴾ_
  sym-≈ᴾ ⟨ ≈ˢ , ≈ᴴ ⟩ = ⟨ sym-≈ˢ ≈ˢ , sym-≈ᴴ ≈ᴴ ⟩

  trans-≈ᴾ : Transitiveᴮ _≈⟨_⟩ᴾ_
  trans-≈ᴾ ⟨ ≈ˢ₁ , ≈₁ᴴ ⟩ ⟨ ≈ˢ₂ , ≈₂ᴴ ⟩ = ⟨ (trans-≈ˢ ≈ˢ₁ ≈ˢ₂) , trans-≈ᴴ ≈₁ᴴ ≈₂ᴴ ⟩

  postulate square-≈ᴾ-ι : ∀ {p₁ p₁' p₂ p₂' β} →
                p₁ ≈⟨ β ⟩ᴾ p₂ →
                p₁ ≈⟨ ι ∥ heap p₁ ∥ᴴ ⟩ᴾ p₁' →
                p₂ ≈⟨ ι ∥ heap p₂ ∥ᴴ ⟩ᴾ p₂' →
                p₁' ≈⟨ β ⟩ᴾ p₂'

  postulate trans-≈ᴾ-ι : ∀ {p₁ p₂ p₃} → p₁ ≈⟨ ι ∥ heap p₁ ∥ᴴ ⟩ᴾ p₂ → p₂ ≈⟨ ι ∥ heap p₂ ∥ᴴ ⟩ᴾ p₃ → p₁ ≈⟨ ι ∥ heap p₁ ∥ᴴ ⟩ᴾ p₃
