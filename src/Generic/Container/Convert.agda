open import Lattice

module Generic.Container.Convert
  {{𝑳 : Lattice}}
  (Label : Set)
  {Ty₁ Ty₂ : Set}
  {Value₁ : Ty₁ → Set}
  {Value₂ : Ty₂ → Set}
  (⟪_⟫ᵗ : Ty₁ → Ty₂)
  (⟪_⟫ⱽ : ∀ {τ} → Value₁ τ → Label → Value₂ ⟪ τ ⟫ᵗ) where

open import Generic.Container.Convert.Base Label {Ty₁} {Ty₂} {Value₁} {Value₂} ⟪_⟫ᵗ ⟪_⟫ⱽ public
