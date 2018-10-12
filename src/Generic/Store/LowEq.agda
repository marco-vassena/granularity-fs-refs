-- Generic pointwise L-equivalence for stores and memories and their
-- properties.

open import Lattice
open import Relation.Binary

module Generic.Store.LowEq
  {Ty : Set}
  {Value : Ty → Set}
  {{𝑳 : Lattice}}
  (_≈ⱽ_ :  ∀ {τ} → Value τ → Value τ → Set)
  (A : Label) where

open import Generic.Store.Base Ty Value

open import Data.Empty
open import Data.Unit hiding (_≟_)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

--------------------------------------------------------------------------------

module Memory-≈ᴹ where

  -- Pointwise low-equivalence (for observable memories)
  data _≈ᴹ_ {ℓ} : Memory ℓ → Memory ℓ → Set where
    [] : [] ≈ᴹ []
    _∷_ : ∀ {τ M₁ M₂} {v₁ v₂ : Value τ} → (v₁≈v₂ : v₁ ≈ⱽ v₂) (M₁≈M₂ : M₁ ≈ᴹ M₂) → (v₁ ∷ M₁) ≈ᴹ (v₂ ∷ M₂)

  -- Any pair of non-observable memories are related, otherwise they are related pointwise
  _≈⟨_⟩ᴹ_ : ∀ {ℓ} → Memory ℓ → Dec (ℓ ⊑ A) → Memory ℓ → Set
  M₁ ≈⟨ yes p ⟩ᴹ M₂ = M₁ ≈ᴹ M₂
  M₁ ≈⟨ no ¬p ⟩ᴹ M₂ = ⊤

  ⌞_⌟ᴹ : ∀ {ℓ} {M₁ M₂ : Memory ℓ} → M₁ ≈ᴹ M₂ → M₁ ≈⟨ ℓ ⊑? A ⟩ᴹ M₂
  ⌞_⌟ᴹ {ℓ} M₁≈M₂ with ℓ ⊑? A
  ... | yes ℓ⊑A = M₁≈M₂
  ... | no ℓ⋤A = tt

open Memory-≈ᴹ public

module Store-≈ˢ where

  -- Stores are related pointwise
  _≈ˢ_ : Store → Store → Set
  Σ₁ ≈ˢ Σ₂ = ∀ ℓ → Σ₁ ℓ ≈⟨ ℓ ⊑? A ⟩ᴹ Σ₂ ℓ

  -- Retrieves two observable memories
  getᴸ : ∀ {ℓ Σ₁ Σ₂} → Σ₁ ≈ˢ Σ₂ → ℓ ⊑ A → Σ₁ ℓ ≈ᴹ Σ₂ ℓ
  getᴸ {ℓ} Σ₁≈Σ₂ ℓ⊑A with ℓ ⊑? A | Σ₁≈Σ₂ ℓ
  ... | yes _ | M₁≈M₂ = M₁≈M₂
  ... | no ℓ⋤A | _  = ⊥-elim (ℓ⋤A ℓ⊑A)

open Store-≈ˢ public

module Props (𝑽 : ∀ {τ} → IsEquivalence (_≈ⱽ_ {τ})) where

  module Shorthand where

    open import Relation.Binary renaming (IsEquivalence to R)

    refl-≈ⱽ : ∀ {τ} → {v : Value τ} → v ≈ⱽ v
    refl-≈ⱽ = R.refl 𝑽

    sym-≈ⱽ : ∀ {τ} {v₁ v₂ : Value τ} → v₁ ≈ⱽ v₂ → v₂ ≈ⱽ v₁
    sym-≈ⱽ = R.sym 𝑽

    trans-≈ⱽ : ∀ {τ} {v₁ v₂ v₃ : Value τ} → v₁ ≈ⱽ v₂ → v₂ ≈ⱽ v₃ → v₁ ≈ⱽ v₃
    trans-≈ⱽ = R.trans 𝑽

  open Shorthand

  --------------------------------------------------------------------------------

  module ≈ᴹ-Equivalence where

    -- Reflexive
    refl-≈ᴹ : ∀ {ℓ} {M : Memory ℓ} → M ≈ᴹ M
    refl-≈ᴹ {M = []} = []
    refl-≈ᴹ {M = _∷_ {τ = τ} v M} = refl-≈ⱽ ∷ refl-≈ᴹ

    -- Symmetric
    sym-≈ᴹ : ∀ {ℓ} {M₁ M₂ : Memory ℓ} → M₁ ≈ᴹ M₂ → M₂ ≈ᴹ M₁
    sym-≈ᴹ [] = []
    sym-≈ᴹ (v₁≈v₂ ∷ M₁≈M₂) = sym-≈ⱽ v₁≈v₂ ∷ sym-≈ᴹ M₁≈M₂

    -- Transitive
    trans-≈ᴹ : ∀ {ℓ} → {M₁ M₂ M₃ : Memory ℓ} → M₁ ≈ᴹ M₂ → M₂ ≈ᴹ M₃ → M₁ ≈ᴹ M₃
    trans-≈ᴹ [] [] = []
    trans-≈ᴹ (v₁≈v₂ ∷ M₁≈M₂) (v₂≈v₃ ∷ M₂≈M₃) = trans-≈ⱽ v₁≈v₂ v₂≈v₃ ∷ trans-≈ᴹ M₁≈M₂ M₂≈M₃

    ≈ᴹ-isEquivalence : ∀ {ℓ} → IsEquivalence (_≈ᴹ_ {ℓ})
    ≈ᴹ-isEquivalence = record { refl = refl-≈ᴹ ; sym = sym-≈ᴹ ; trans = trans-≈ᴹ }

  open ≈ᴹ-Equivalence public

  --------------------------------------------------------------------------------

  module  ≈⟨_⟩ᴹ-Equivalence  where

    refl-≈⟨_⟩ᴹ : ∀ {ℓ} {M : Memory ℓ} (x : Dec (ℓ ⊑ A)) → M ≈⟨ x ⟩ᴹ M
    refl-≈⟨ yes p ⟩ᴹ = refl-≈ᴹ
    refl-≈⟨ no ¬p ⟩ᴹ = tt

    sym-≈⟨_⟩ᴹ : ∀ {ℓ} {M₁ M₂ : Memory ℓ} (x : Dec (ℓ ⊑ A)) → M₁ ≈⟨ x ⟩ᴹ M₂ → M₂ ≈⟨ x ⟩ᴹ M₁
    sym-≈⟨ yes p ⟩ᴹ M₁≈M₂ = sym-≈ᴹ M₁≈M₂
    sym-≈⟨ no ¬p ⟩ᴹ M₁≈M₂ = tt

    trans-≈⟨_⟩ᴹ : ∀ {ℓ} {M₁ M₂ M₃ : Memory ℓ} → (x : Dec (ℓ ⊑ A)) →  M₁ ≈⟨ x ⟩ᴹ M₂ → M₂ ≈⟨ x ⟩ᴹ M₃ → M₁ ≈⟨ x ⟩ᴹ M₃
    trans-≈⟨ yes p ⟩ᴹ M₁≈M₂ M₂≈M₃ = trans-≈ᴹ M₁≈M₂ M₂≈M₃
    trans-≈⟨ no ¬p ⟩ᴹ M₁≈M₂ M₂≈M₃ = tt

    ≈⟨_⟩ᴹ-isEquivalence : ∀ {ℓ} (x : Dec (ℓ ⊑ A)) → IsEquivalence (λ (M₁ M₂ : Memory ℓ) → M₁ ≈⟨ x ⟩ᴹ M₂)
    ≈⟨ x ⟩ᴹ-isEquivalence = record { refl = refl-≈⟨ x ⟩ᴹ ; sym = sym-≈⟨ x ⟩ᴹ ; trans = trans-≈⟨ x ⟩ᴹ }

  open ≈⟨_⟩ᴹ-Equivalence public

  --------------------------------------------------------------------------------

  module ≈ˢ-Equivalence where

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

  -- Low memories have the same length
  ∥_∥-≡ : ∀ {ℓ} {M₁ M₂ : Memory ℓ} → M₁ ≈ᴹ M₂ → ∥ M₁ ∥ ≡ ∥ M₂ ∥
  ∥ [] ∥-≡ = refl
  ∥ x ∷ M₁≈M₂ ∥-≡ rewrite ∥ M₁≈M₂ ∥-≡ = refl

  new-≈ᴹ : ∀ {τ ℓ} {M₁ M₂ : Memory ℓ} {v₁ v₂ : Value τ} → M₁ ≈ᴹ M₂ → v₁ ≈ⱽ v₂ → (M₁ ∷ᴿ v₁) ≈ᴹ (M₂ ∷ᴿ v₂)
  new-≈ᴹ [] v₁≈v₂ = v₁≈v₂ ∷ []
  new-≈ᴹ (v₁≈v₂' ∷ M₁≈M₂) v₁≈v₂ = v₁≈v₂' ∷ (new-≈ᴹ M₁≈M₂ v₁≈v₂)

  update-≈ᴹ : ∀ {ℓ τ n} {M₁ M₁' M₂ M₂' : Memory ℓ} {v₁ v₂ : Value τ} →
                M₁ ≈ᴹ M₂ →
                v₁ ≈ⱽ v₂ →
                M₁' ≔ M₁ [ n ↦ v₁ ]ᴹ →
                M₂' ≔ M₂ [ n ↦ v₂ ]ᴹ →
                M₁' ≈ᴹ M₂'
  update-≈ᴹ (_ ∷ M₁≈M₂) v₁≈v₂ Here Here = v₁≈v₂ ∷ M₁≈M₂
  update-≈ᴹ (v₁≈v₂' ∷ M₁≈M₂) v₁≈v₂ (There u₁) (There u₂) = v₁≈v₂' ∷ update-≈ᴹ M₁≈M₂ v₁≈v₂ u₁ u₂

  read-≈ᴹ : ∀ {ℓ τ n} {M₁ M₂ : Memory ℓ} {v₁ v₂ : Value τ} →
              M₁ ≈ᴹ M₂ →
              n ↦ v₁ ∈ᴹ M₁ →
              n ↦ v₂ ∈ᴹ M₂ →
              v₁ ≈ⱽ v₂
  read-≈ᴹ (v₁≈v₂ ∷ _) Here Here = v₁≈v₂
  read-≈ᴹ (_ ∷ M₁≈M₂) (There r₁) (There r₂) = read-≈ᴹ M₁≈M₂ r₁ r₂

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
