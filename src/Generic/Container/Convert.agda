open import Lattice

module Generic.Container.Convert
  {{𝑳 : Lattice}}
  (Label : Set)
  {Ty₁ Ty₂ : Set}
  {Value₁ : Ty₁ → Set}
  {Value₂ : Ty₂ → Set}
  (⟪_⟫ᵗ : Ty₁ → Ty₂)
  (⟪_⟫ⱽ : ∀ {τ} → Value₁ τ → Label → Value₂ ⟪ τ ⟫ᵗ) where

open import Generic.Container.Base Label as B using ([] ; _∷_)

private module S = B Ty₁ Value₁
private module T = B Ty₂ Value₂

-- Generic pointwise memory transformation
⟪_⟫ᶜ : ∀ {ℓ} → S.Container ℓ → T.Container ℓ
⟪_⟫ᶜ [] = []
⟪_⟫ᶜ {ℓ} (v ∷ M) = ⟪ v ⟫ⱽ ℓ ∷ ⟪ M ⟫ᶜ

open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

∥_∥-≡ : ∀ {ℓ} (M : S.Container ℓ) → T.∥ ⟪ M ⟫ᶜ ∥ ≡ S.∥ M ∥
∥ [] ∥-≡ = refl
∥ v ∷ M ∥-≡ rewrite ∥ M ∥-≡ = refl

∷ᴿ-≡ : ∀ {ℓ τ} (v : Value₁ τ) (M : S.Container ℓ) → ⟪ M ⟫ᶜ T.∷ᴿ ⟪ v ⟫ⱽ ℓ ≡ ⟪ M S.∷ᴿ v ⟫ᶜ
∷ᴿ-≡ v [] = refl
∷ᴿ-≡ v (_ ∷ M) = cong₂ _∷_ refl (∷ᴿ-≡ v M)

⟪_⟫∈ : ∀ {ℓ τ n} {v : Value₁ τ} {M : S.Container ℓ} → n S.↦ v ∈ M → n T.↦ (⟪ v ⟫ⱽ ℓ) ∈ ⟪ M ⟫ᶜ
⟪ S.Here ⟫∈ = T.Here
⟪ S.There x ⟫∈ = T.There ⟪ x ⟫∈

write-≡ : ∀ {ℓ n τ} {M M' : S.Container ℓ} {v : Value₁ τ} →
          M' S.≔ M [ n ↦ v ] →
          ⟪ M' ⟫ᶜ T.≔ ⟪ M ⟫ᶜ [ n ↦ (⟪ v ⟫ⱽ ℓ) ]
write-≡ S.Here = T.Here
write-≡ (S.There x) = T.There (write-≡ x)

------------------------------------------------------------------------------------------
