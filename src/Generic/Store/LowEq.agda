-- Generic pointwise L-equivalence for stores and memories and their
-- properties.
{-# OPTIONS --allow-unsolved-metas #-}

open import Lattice
open import Relation.Binary

module Generic.Store.LowEq
  {Ty : Set}
  {Value : Ty → Set}
  {{𝑳 : Lattice}}
  (_≈ⱽ_ :  ∀ {τ} → Value τ → Value τ → Set)
  (A : Label) where

open import Generic.Store.Base Ty Value
open import Generic.Memory.LowEq {Ty} {Value} _≈ⱽ_ A as M using (_≈⟨_⟩ᴹ_ ; _≈⟨_,_⟩ᴹ_ ; ⌞_⌟ᴹ) public

open import Data.Empty
open import Data.Unit hiding (_≟_)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Generic.Bijection

--------------------------------------------------------------------------------

module Store-≈ˢ where

  -- Stores are related pointwise
  _≈⟨_⟩ˢ_ : Store → Bij → Store → Set
  Σ₁ ≈⟨ β ⟩ˢ Σ₂ = ∀ ℓ → Σ₁ ℓ ≈⟨ β , ℓ ⊑? A ⟩ᴹ Σ₂ ℓ

  -- Retrieves two observable memories
  getᴸ : ∀ {ℓ Σ₁ Σ₂ β} → Σ₁ ≈⟨ β ⟩ˢ Σ₂ → ℓ ⊑ A → Σ₁ ℓ ≈⟨ β ⟩ᴹ Σ₂ ℓ
  getᴸ {ℓ} Σ₁≈Σ₂ ℓ⊑A with ℓ ⊑? A | Σ₁≈Σ₂ ℓ
  ... | yes _ | M₁≈M₂ = M₁≈M₂
  ... | no ℓ⋤A | _  = ⊥-elim (ℓ⋤A ℓ⊑A)

open Store-≈ˢ public

module Props (𝑽 : ∀ {τ} → IsEquivalence (_≈ⱽ_ {τ})) where

  module ≈ˢ-Equivalence where

    open M.Props 𝑽 public

    -- What size should I use here for the identity bijection?
    -- Maybe it's not the right thing to compute it.

    -- Reflexive
    refl-≈ˢ : ∀ {Σ} → Σ ≈ˢ Σ
    refl-≈ˢ {Σ} ℓ = refl-≈⟨ _ ⟩ᴹ

    -- Symmetric
    sym-≈ˢ : ∀ {Σ₁ Σ₂} → Σ₁ ≈ˢ Σ₂ → Σ₂ ≈ˢ Σ₁
    sym-≈ˢ Σ₁≈Σ₂ ℓ = sym-≈⟨ _ ⟩ᴹ (Σ₁≈Σ₂ ℓ)

    -- Transitive
    trans-≈ˢ : ∀ {Σ₁ Σ₂ Σ₃} → Σ₁ ≈ˢ Σ₂ → Σ₂ ≈ˢ Σ₃ → Σ₁ ≈ˢ Σ₃
    trans-≈ˢ Σ₁≈Σ₂ Σ₂≈Σ₃ = λ ℓ → trans-≈⟨ _  ⟩ᴹ (Σ₁≈Σ₂ ℓ) (Σ₂≈Σ₃ ℓ)

    ≈ˢ-isEquivalence : IsEquivalence _≈ˢ_
    ≈ˢ-isEquivalence = record { refl = refl-≈ˢ ; sym = sym-≈ˢ ; trans = trans-≈ˢ }

    Store-≈ˢ : Setoid _ _
    Store-≈ˢ = record { Carrier = Store ; _≈_ = _≈ˢ_ ; isEquivalence = ≈ˢ-isEquivalence }

  open ≈ˢ-Equivalence public

  --------------------------------------------------------------------------------
  -- Store properties

  -- Updating the store with low-equivalent memories preserves low-equivalence
  updateᴸ-≈ˢ : ∀ {ℓ Σ₁ Σ₂} {M₁ M₂ : Memory ℓ} → Σ₁ ≈ˢ Σ₂ → M₁ ≈ᴹ M₂ → (Σ₁ [ ℓ ↦ M₁ ]ˢ) ≈ˢ (Σ₂ [ ℓ ↦ M₂ ]ˢ)
  updateᴸ-≈ˢ {ℓ} Σ₁≈Σ₂ M₁≈M₂ ℓ' with ℓ ≟ ℓ'
  ... | yes refl = ⌞ M₁≈M₂ ⌟ᴹ
  ... | no ℓ≠ℓ' = Σ₁≈Σ₂ ℓ'

  -- Modifying a high memory preserves low-equivalence of the store
  updateᴴ-≈ˢ : ∀ {ℓ} Σ (M : Memory ℓ) → ℓ ⋤ A → Σ ≈ˢ (Σ [ ℓ ↦ M ]ˢ)
  updateᴴ-≈ˢ {ℓ} Σ M ℓ⋤A ℓ' with ℓ' ⊑? A
  updateᴴ-≈ˢ {ℓ} Σ M ℓ⋤A ℓ' | yes ℓ'⊑A with ℓ ≟ ℓ'
  updateᴴ-≈ˢ {.ℓ} Σ M ℓ⋤A ℓ | yes ℓ⊑A | yes refl = ⊥-elim (ℓ⋤A ℓ⊑A)
  updateᴴ-≈ˢ {ℓ} Σ M ℓ⋤A ℓ' | yes ℓ'⊑A | no ℓ≠ℓ' = refl-≈ᴹ
  updateᴴ-≈ˢ {ℓ} Σ M ℓ⋤A ℓ' | no ℓ'⋤A = tt

  square-≈ˢ : ∀ {Σ₁ Σ₁' Σ₂ Σ₂'} → Σ₁ ≈ˢ Σ₂ → Σ₁ ≈ˢ Σ₁' → Σ₂ ≈ˢ Σ₂' → Σ₁' ≈ˢ Σ₂'
  square-≈ˢ Σ₁≈Σ₂ Σ₁≈Σ₁' Σ₂≈Σ₂' = trans-≈ˢ (trans-≈ˢ (sym-≈ˢ Σ₁≈Σ₁') Σ₁≈Σ₂) Σ₂≈Σ₂'
