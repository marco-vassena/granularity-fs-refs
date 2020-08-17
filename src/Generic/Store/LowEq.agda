-- Generic pointwise L-equivalence for stores and memories and their
-- properties.
-- {-# OPTIONS --allow-unsolved-metas #-}

open import Lattice
open import Relation.Binary -- Can be removed
open import Generic.Bijection

module Generic.Store.LowEq
  {{𝑳 : Lattice}}
  {Ty : Set}
  {Value : Ty → Set}
  (_≈⟨_⟩ⱽ_ :  IProps.Relᴮ Ty Value)
  (A : Label) where

open import Generic.Store Ty Value
open import Generic.Memory.LowEq {Ty} {Value} _≈⟨_⟩ⱽ_ A  as M using (_≈⟨_⟩ᴹ_ ; _≈⟨_,_⟩ᴹ_ ; ⌞_⌟ᴹ) public

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

private module V = IProps Ty Value

module ≈ˢ-Props (𝑽 : V.IsEquivalenceᴮ _≈⟨_⟩ⱽ_) where

  open M.≈ᴹ-Props 𝑽 public
  open import Generic.Store.Valid Ty Value (V.Dom 𝑽)

  open SProps Store

  -- What size should I use here for the identity bijection?
  -- Maybe it's not the right thing to compute it.

  -- Reflexive
  refl-≈ˢ : ∀ {Σ n} {{validˢ : Validˢ n Σ}} → Σ ≈⟨ ι n ⟩ˢ Σ
  refl-≈ˢ {{validˢ}} ℓ = refl-≈ᴹ′ {{validˢ ℓ}}

  -- Symmetric
  sym-≈ˢ : Symmetricᴮ _≈⟨_⟩ˢ_
  sym-≈ˢ Σ₁≈Σ₂ ℓ = sym-≈⟨ _ ⟩ᴹ (Σ₁≈Σ₂ ℓ)

  -- Transitive
  trans-≈ˢ : Transitiveᴮ _≈⟨_⟩ˢ_ -- ∀ {Σ₁ Σ₂ Σ₃} → Σ₁ ≈ˢ Σ₂ → Σ₂ ≈ˢ Σ₃ → Σ₁ ≈ˢ Σ₃
  trans-≈ˢ Σ₁≈Σ₂ Σ₂≈Σ₃ = λ ℓ → trans-≈⟨ _  ⟩ᴹ (Σ₁≈Σ₂ ℓ) (Σ₂≈Σ₃ ℓ)


  postulate wken-≈ˢ : Wkenᴮ _≈⟨_⟩ˢ_
--   ≈ˢ-isEquivalence : IsEquivalence _≈ˢ_
--   ≈ˢ-isEquivalence = record { refl = refl-≈ˢ ; sym = sym-≈ˢ ; trans = trans-≈ˢ }

--   Store-≈ˢ : Setoid _ _
--   Store-≈ˢ = record { Carrier = Store ; _≈_ = _≈ˢ_ ; isEquivalence = ≈ˢ-isEquivalence }

-- open ≈ˢ-Equivalence public

  --------------------------------------------------------------------------------
  -- Store properties

  -- Updating the store with low-equivalent memories preserves low-equivalence
  updateᴸ-≈ˢ : ∀ {ℓ β Σ₁ Σ₂} {M₁ M₂ : Memory ℓ} →
                 Σ₁ ≈⟨ β ⟩ˢ Σ₂ →
                 M₁ ≈⟨ β ⟩ᴹ M₂ →
                 (Σ₁ [ ℓ ↦ M₁ ]ˢ) ≈⟨ β ⟩ˢ (Σ₂ [ ℓ ↦ M₂ ]ˢ)
  updateᴸ-≈ˢ {ℓ} Σ₁≈Σ₂ M₁≈M₂ ℓ' with ℓ ≟ ℓ'
  ... | yes refl = ⌞ M₁≈M₂ ⌟ᴹ
  ... | no ℓ≠ℓ' = Σ₁≈Σ₂ ℓ'

--  open import Generic.Memory.Valid Ty Value ∣_∣ⱽ

  -- Modifying a high memory preserves low-equivalence of the store
  updateᴴ-≈ˢ : ∀ {ℓ n} Σ (M : Memory ℓ) {{validˢ : Validˢ n Σ}} →
                  ℓ ⋤ A → Σ ≈⟨ ι n ⟩ˢ (Σ [ ℓ ↦ M ]ˢ)
  updateᴴ-≈ˢ {ℓ} Σ M ℓ⋤A ℓ' with ℓ' ⊑? A
  updateᴴ-≈ˢ {ℓ} Σ M ℓ⋤A ℓ' | yes ℓ'⊑A with ℓ ≟ ℓ'
  updateᴴ-≈ˢ {ℓ} Σ M ℓ⋤A ℓ' | yes ℓ⊑A | yes refl = ⊥-elim (ℓ⋤A ℓ⊑A)
  updateᴴ-≈ˢ {ℓ} Σ M {{validˢ}} ℓ⋤A ℓ' | yes ℓ'⊑A | no ℓ≠ℓ' = refl-≈ᴹ {{ validˢ ℓ' }}
  updateᴴ-≈ˢ {ℓ} Σ M ℓ⋤A ℓ' | no ℓ'⋤A = tt

  square-≈ˢ : ∀ {β β₁ β₂ Σ₁ Σ₁' Σ₂ Σ₂'} →
                Σ₁ ≈⟨ β ⟩ˢ Σ₂ →
                Σ₁ ≈⟨ β₁ ⟩ˢ Σ₁' →
                Σ₂ ≈⟨ β₂ ⟩ˢ Σ₂' →
                Σ₁' ≈⟨ β₂ ∘ β ∘ (β₁ ⁻¹) ⟩ˢ Σ₂'
  square-≈ˢ Σ₁≈Σ₂ Σ₁≈Σ₁' Σ₂≈Σ₂' = trans-≈ˢ (trans-≈ˢ (sym-≈ˢ Σ₁≈Σ₁') Σ₁≈Σ₂) Σ₂≈Σ₂'

  -- Here we should be able to derive n₁ ≤ n₂ from β
  postulate square-≈ˢ-ι : ∀ {Σ₁ Σ₁' Σ₂ Σ₂' β n₁ n₂} →
                            Σ₁ ≈⟨ β ⟩ˢ Σ₂ →
                            Σ₁ ≈⟨ ι n₁ ⟩ˢ Σ₁' →
                            Σ₂ ≈⟨ ι n₂ ⟩ˢ Σ₂' →
                            Σ₁' ≈⟨ β ⟩ˢ Σ₂'

  postulate trans-≈ˢ-ι : ∀ {Σ₁ Σ₂ Σ₃ n₁ n₂} → Σ₁ ≈⟨ ι n₁ ⟩ˢ Σ₂ → Σ₂ ≈⟨ ι n₂ ⟩ˢ Σ₃ → Σ₁ ≈⟨ ι n₁ ⟩ˢ Σ₃
