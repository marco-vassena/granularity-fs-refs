-- Generic conversion between stores and memory

open import Lattice

module Generic.Store.Convert
  {{𝑳 : Lattice}}
  {Ty₁ Ty₂ : Set}
  {Value₁ : Ty₁ → Set}
  {Value₂ : Ty₂ → Set}
  (⟪_⟫ᵗ : Ty₁ → Ty₂)
  (⟪_⟫ⱽ : ∀ {τ} → Value₁ τ → Label → Value₂ ⟪ τ ⟫ᵗ) where

open import Generic.Store.Base as B using ([] ; _∷_)

module S = B Ty₁ Value₁
module T = B Ty₂ Value₂

-- Generic pointwise memory transformation
⟪_⟫ᴹ : ∀ {ℓ} → S.Memory ℓ → T.Memory ℓ
⟪_⟫ᴹ [] = []
⟪_⟫ᴹ {ℓ} (v ∷ M) = ⟪ v ⟫ⱽ ℓ ∷ ⟪ M ⟫ᴹ

-- Generic pointwise store transformation
⟪_⟫ˢ : S.Store → T.Store
⟪ Σ ⟫ˢ ℓ = ⟪ Σ ℓ ⟫ᴹ

infix 2 ⟪_⟫ˢ

module Lemmas where

  open import Relation.Binary.PropositionalEquality
  open import Relation.Nullary

  ∥_∥-≡ᴹ : ∀ {ℓ} (M : S.Memory ℓ) → T.∥ ⟪ M ⟫ᴹ ∥ ≡ S.∥ M ∥
  ∥ [] ∥-≡ᴹ = refl
  ∥ v ∷ M ∥-≡ᴹ rewrite ∥ M ∥-≡ᴹ = refl

  ∥_∥-≡ : ∀ Σ ℓ → T.∥ ⟪ Σ ⟫ˢ ℓ ∥ ≡ S.∥ Σ ℓ ∥
  ∥_∥-≡ Σ ℓ = ∥ (Σ ℓ) ∥-≡ᴹ

  ∷ᴿ-≡ : ∀ {ℓ τ} (v : Value₁ τ) (M : S.Memory ℓ) → ⟪ M ⟫ᴹ T.∷ᴿ ⟪ v ⟫ⱽ ℓ ≡ ⟪ M S.∷ᴿ v ⟫ᴹ
  ∷ᴿ-≡ v [] = refl
  ∷ᴿ-≡ v (_ ∷ M) = cong₂ _∷_ refl (∷ᴿ-≡ v M)

  update-≡ˢ : ∀ {ℓ Σ M₁ M₂} → M₁ ≡ ⟪ M₂ ⟫ᴹ → (ℓ' : Label) →
              ((⟪ Σ ⟫ˢ T.[ ℓ ↦ M₁ ]ˢ) ℓ' ≡ ⟪ Σ S.[ ℓ ↦ M₂ ]ˢ ⟫ˢ ℓ')
  update-≡ˢ {ℓ} eq ℓ' with ℓ ≟ ℓ'
  ... | yes refl = eq
  ... | no ¬p = refl

  ⟪_⟫∈ᴹ : ∀ {ℓ τ n} {v : Value₁ τ} {M : S.Memory ℓ} → n S.↦ v ∈ᴹ M → n T.↦ (⟪ v ⟫ⱽ ℓ) ∈ᴹ ⟪ M ⟫ᴹ
  ⟪ S.Here ⟫∈ᴹ = T.Here
  ⟪ S.There x ⟫∈ᴹ = T.There ⟪ x ⟫∈ᴹ

  write-≡ᴹ : ∀ {ℓ n τ} {M M' : S.Memory ℓ} {v : Value₁ τ} → M' S.≔ M [ n ↦ v ]ᴹ → ⟪ M' ⟫ᴹ T.≔ ⟪ M ⟫ᴹ [ n ↦ (⟪ v ⟫ⱽ ℓ) ]ᴹ
  write-≡ᴹ S.Here = T.Here
  write-≡ᴹ (S.There x) = T.There (write-≡ᴹ x)

------------------------------------------------------------------------------------------
