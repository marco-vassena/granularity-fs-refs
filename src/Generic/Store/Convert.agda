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

private module S = B Ty₁ Value₁ renaming (∥_∥ᴹ to ∥_∥ ; snocᴹ to _∷ᴿ_)
private module T = B Ty₂ Value₂ renaming (∥_∥ᴹ to ∥_∥ ; snocᴹ to _∷ᴿ_)

open import Generic.Container.Convert Label {Ty₁} {Ty₂} {Value₁} {Value₂} ⟪_⟫ᵗ ⟪_⟫ⱽ as M
  renaming ( ⟪_⟫ᶜ to ⟪_⟫ᴹ
           ; ∥_∥-≡ to ∥_∥-≡ᴹ
           ; ⟪_⟫∈ to ⟪_⟫∈ᴹ
           ; write-≡ to write-≡ᴹ) public

-- Generic pointwise store transformation
⟪_⟫ˢ : S.Store → T.Store
⟪ Σ ⟫ˢ ℓ = ⟪ Σ ℓ ⟫ᴹ

infix 2 ⟪_⟫ˢ

open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

update-≡ˢ : ∀ {ℓ Σ M₁ M₂} → M₁ ≡ ⟪ M₂ ⟫ᴹ → (ℓ' : Label) →
            ((⟪ Σ ⟫ˢ T.[ ℓ ↦ M₁ ]ˢ) ℓ' ≡ ⟪ Σ S.[ ℓ ↦ M₂ ]ˢ ⟫ˢ ℓ')
update-≡ˢ {ℓ} eq ℓ' with ℓ ≟ ℓ'
... | yes refl = eq
... | no ¬p = refl

∥_∥-≡ : ∀ Σ ℓ → T.∥ ⟪ Σ ⟫ˢ ℓ ∥ ≡ S.∥ Σ ℓ ∥
∥_∥-≡ Σ ℓ = ∥ (Σ ℓ) ∥-≡ᴹ
