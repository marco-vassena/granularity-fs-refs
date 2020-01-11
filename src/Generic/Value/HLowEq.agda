open import Relation.Binary

module Generic.Value.HLowEq
  {Ty : Set} {Value : Ty → Set}
  (_≈ⱽ_ :  ∀ {τ} → Value τ → Value τ → Set) where

-- Heterogeneous version of low-equivlence (accepts values with different types).
data _≅ⱽ_ {τ} (v : Value τ) : ∀ {τ} → Value τ → Set where
  ⌞_⌟ : ∀ {v' : Value τ} → v ≈ⱽ v' → v ≅ⱽ v'

module Props (𝑽 : ∀ {τ} → IsEquivalence (_≈ⱽ_ {τ})) where
  open import Generic.Value.LowEq {Ty} {Value} _≈ⱽ_
  open Props 𝑽
  open import Relation.Binary renaming (IsEquivalence to R)

  refl-≅ⱽ : ∀ {τ} {v : Value τ} → v ≅ⱽ v
  refl-≅ⱽ = ⌞ R.refl 𝑽 ⌟

  sym-≅ⱽ : ∀ {τ₁ τ₂} {v₁ : Value τ₁} {v₂ : Value τ₂} → v₁ ≅ⱽ v₂ → v₂ ≅ⱽ v₁
  sym-≅ⱽ ⌞ x ⌟ = ⌞ R.sym 𝑽 x ⌟

  trans-≅ⱽ : ∀ {τ₁ τ₂ τ₃} {v₁ : Value τ₁} {v₂ : Value τ₂} {v₃ : Value τ₃} →
               v₁ ≅ⱽ v₂ → v₂ ≅ⱽ v₃ → v₁ ≅ⱽ v₃
  trans-≅ⱽ ⌞ x ⌟ ⌞ y ⌟ = ⌞  R.trans 𝑽 x y ⌟
