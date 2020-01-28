open import Relation.Binary
open import Generic.Bijection

module Generic.Value.LowEq
  {Ty : Set} {Value : Ty → Set}
  (_≈⟨_⟩ⱽ_ : Relᴮ {Ty} Value) where

module Props (𝑽 : IsEquivalenceᴮ {Ty} {Value} _≈⟨_⟩ⱽ_) where

  open IsEquivalenceᴮ 𝑽

  refl-≈ⱽ : Reflexiveᴮ {F = Value} _≈⟨_⟩ⱽ_ Dom
  refl-≈ⱽ = reflᴮ

  sym-≈ⱽ : Symmetricᴮ {F = Value} _≈⟨_⟩ⱽ_
  sym-≈ⱽ = symᴮ

  trans-≈ⱽ : Transitiveᴮ {F = Value} _≈⟨_⟩ⱽ_
  trans-≈ⱽ = transᴮ
