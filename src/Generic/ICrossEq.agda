-- Indexed cross equivalence

open import Generic.CrossEq

module Generic.ICrossEq
  {Ty₁ : Set} {Ty₂ : Set}
  (Label : Set)
  (𝑻 : CEq Ty₁ Ty₂) where

open CEq 𝑻 renaming (_↓≈_ to _↓≈ᵗ_ ; ⟦_⟧ to ⟦_⟧ᵗ ; refl-↓≈ to refl-↓≈ᵗ)
open import Relation.Binary.PropositionalEquality

record ICEq (Value₁ : Ty₁ → Set) (Value₂ : Ty₂ → Set) : Set₁ where
  field
    ⟦_⟧ : ∀ {τ₁} → Value₁ τ₁ → Label → Value₂ ⟦ τ₁ ⟧ᵗ
    _↓≈⟨_,_⟩_ : ∀ {τ₂ τ₁} → Value₂ τ₂ → Label → τ₂ ↓≈ᵗ τ₁  → Value₁ τ₁ → Set
    -- ix-↓≈ : ∀ {τ₁ τ₂ ℓ} {v₁ : Value₁ τ₁} {v₂ : Value₂ τ₂} →
    --            v₂ ↓≈⟨ ℓ ⟩ v₁ → τ₂ ↓≈ᵗ τ₁
    refl-↓≈⟨_⟩ : ∀ {τ₁} pc (v : Value₁ τ₁) → (⟦ v ⟧ pc) ↓≈⟨ pc , refl-↓≈ᵗ _  ⟩ v

  _↓≈⟨_⟩_ :  ∀ {τ₂ τ₁} {{τ≈ : τ₂ ↓≈ᵗ τ₁}} → Value₂ τ₂ → Label → Value₁ τ₁ → Set
  _↓≈⟨_⟩_ {{τ≈}} v₂ ℓ v₁ = v₂ ↓≈⟨ ℓ , τ≈ ⟩ v₁


  -- where
    -- where
    --   instance _ = refl-↓≈ᵗ
