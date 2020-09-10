open import Lattice

module Generic.Container.Convert.Graph
  {{𝑳 : Lattice}}
  (Label : Set)
  {Ty₁ Ty₂ : Set}
  {Value₁ : Ty₁ → Set}
  {Value₂ : Ty₂ → Set}
  (⟪_⟫ᵗ : Ty₁ → Ty₂)
  (⟪_⟫ⱽ : ∀ {τ} → Value₁ τ → Label → Value₂ ⟪ τ ⟫ᵗ) where

open import Generic.Container.Base Label as B using ([] ; _∷_)
