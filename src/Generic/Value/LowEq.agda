-- TODO: remove this module

open import Relation.Binary
open import Generic.Bijection

module Generic.Value.LowEq
  {Ty : Set} {Value : Ty → Set}
  (_≈⟨_⟩ⱽ_ : IProps.Relᴮ Ty Value) where

-- TODO: is not this just a renaming?

-- open IProps Ty Value
open import Generic.ValidEquivalence Ty Value

-- TODO: why do we need the inner module?
module Props (𝑽 : IsValidEquivalence _≈⟨_⟩ⱽ_) where

  open IsValidEquivalence 𝑽 renaming
    ( ∥_∥ to ∣_∣ⱽ
    ; reflᴮ to refl-≈ⱽ
    ; symᴮ to sym-≈ⱽ
    ; transᴮ to trans-≈ⱽ
    ; wkenᴮ to wken-≈ⱽ) public

  -- refl-≈ⱽ : Reflexiveᴮ {F = Value} _≈⟨_⟩ⱽ_ {!!} -- Dom
  -- refl-≈ⱽ = reflᴮ

  -- sym-≈ⱽ : Symmetricᴮ {F = Value} _≈⟨_⟩ⱽ_
  -- sym-≈ⱽ = symᴮ

  -- trans-≈ⱽ : Transitiveᴮ {F = Value} _≈⟨_⟩ⱽ_
  -- trans-≈ⱽ = transᴮ
