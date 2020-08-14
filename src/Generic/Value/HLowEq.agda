open import Relation.Binary
open import Generic.Bijection
open import Relation.Binary.PropositionalEquality

module Generic.Value.HLowEq
  {Ty : Set} {Value : Ty → Set}
  (_≈⟨_⟩ⱽ_ :  IProps.Relᴮ Ty Value) where

-- Heterogeneous version of low-equivlence (accepts values with different types).
data _≅⟨_⟩ⱽ_ {τ} (v : Value τ) (β : Bij) : ∀ {τ} → Value τ → Set where
  ⌞_⌟ : ∀ {v' : Value τ} → v ≈⟨ β ⟩ⱽ v' → v ≅⟨ β ⟩ⱽ v'

-- Heterogenous L-equivalence implies equality of the types of the values
≅ⱽ-type-≡ : ∀ {τ₁ τ₂ β} {v₁ : Value τ₁} {v₂ : Value τ₂} → v₁ ≅⟨ β ⟩ⱽ v₂ → τ₁ ≡ τ₂
≅ⱽ-type-≡ ⌞ x ⌟ = refl

private module V = IProps Ty Value

-- Why two modules?
module Props (𝑽 : V.IsEquivalenceᴮ  _≈⟨_⟩ⱽ_) where
  open V.IsEquivalenceᴮ 𝑽
  open import Data.Nat

  Domⱽ : ∀ {τ} → Value τ → ℕ
  Domⱽ = Dom

  refl-≅ⱽ : ∀ {τ} {v : Value τ} → v ≅⟨ ι (Domⱽ v) ⟩ⱽ v
  refl-≅ⱽ = ⌞ reflᴮ ⌟

  sym-≅ⱽ : ∀ {τ₁ τ₂ β} {v₁ : Value τ₁} {v₂ : Value τ₂} → v₁ ≅⟨ β ⟩ⱽ v₂ → v₂ ≅⟨ β ⁻¹ ⟩ⱽ v₁
  sym-≅ⱽ ⌞ x ⌟ = ⌞ symᴮ x ⌟

  trans-≅ⱽ : ∀ {τ₁ τ₂ τ₃ β₁ β₂} {v₁ : Value τ₁} {v₂ : Value τ₂} {v₃ : Value τ₃} →
               v₁ ≅⟨ β₁ ⟩ⱽ v₂ → v₂ ≅⟨ β₂ ⟩ⱽ v₃ → v₁ ≅⟨ β₂ ∘ β₁ ⟩ⱽ v₃
  trans-≅ⱽ ⌞ x ⌟ ⌞ y ⌟ = ⌞  transᴮ x y ⌟

  wken-≅ⱽ : ∀ {τ₁ τ₂ β β'} {v₁ : Value τ₁} {v₂ : Value τ₂} →
            β ⊆ β' → v₁ ≅⟨ β ⟩ⱽ v₂ → v₁ ≅⟨ β' ⟩ⱽ v₂
  wken-≅ⱽ β⊆β' ⌞ x ⌟ = ⌞ wkenᴮ β⊆β' x ⌟


--------------------------------------------------------------------------------
-- Cleaner but gives us problem in the heap LowEq properties

-- data _≅⟨_⟩ⱽ_ {τ₁} : ∀ {τ₂} → Value τ₁ → Bij → Value τ₂ → Set where
--   ⌞_⌟ : ∀ {β} {v₁ : Value τ₁} {v₂ : Value τ₁} → v₁ ≈⟨ β ⟩ⱽ v₂ → v₁ ≅⟨ β ⟩ⱽ v₂

-- module Props (𝑽 : IsEquivalenceᴮ {F = Value} _≈⟨_⟩ⱽ_) where

--   open IsEquivalenceᴮ 𝑽

--   refl-≅ⱽ : Reflexiveᴮ {Ty} {Value} _≅⟨_⟩ⱽ_ Dom
--   refl-≅ⱽ = ⌞ reflᴮ ⌟

--   wken-≅ⱽ : Wkenᴮ {Ty} {Value} _≅⟨_⟩ⱽ_
--   wken-≅ⱽ n<m ⌞ x ⌟ = ⌞ wkenᴮ n<m x ⌟

--   sym-≅ⱽ : Symmetricᴮ {Ty} {Value} _≅⟨_⟩ⱽ_
--   sym-≅ⱽ ⌞ x ⌟ = ⌞ symᴮ x ⌟

--   trans-≅ⱽ : Transitiveᴮ {Ty} {Value} _≅⟨_⟩ⱽ_
--   trans-≅ⱽ ⌞ x ⌟ ⌞ y ⌟ = ⌞  transᴮ x y ⌟

--   ≅ⱽ-isEquivᴮ : IsEquivalenceᴮ {F = Value} _≅⟨_⟩ⱽ_
--   ≅ⱽ-isEquivᴮ =
--     record { Dom = Dom
--            ; wkenᴮ = wken-≅ⱽ
--            ; reflᴮ = refl-≅ⱽ
--            ; symᴮ = sym-≅ⱽ
--            ; transᴮ = trans-≅ⱽ }
