-- TODO: already in Generic.Graph
-- Generic cross equivalence relation

module Generic.CrossEq where

open import Relation.Binary.PropositionalEquality

record CEq (Ty₁ Ty₂ : Set) : Set₁ where
  field
    ⟦_⟧ : Ty₁ → Ty₂
    _↓≈_ : Ty₂ → Ty₁ → Set
    ⌞_⌟ : ∀ {τ₁ τ₂} → τ₂ ↓≈ τ₁ → τ₂ ≡ ⟦ τ₁ ⟧
    refl-↓≈ : ∀ τ → ⟦ τ ⟧ ↓≈ τ
    !-↓≈ : ∀ {τ₁ τ₂} → (x y : τ₂ ↓≈ τ₁) → x ≡ y
