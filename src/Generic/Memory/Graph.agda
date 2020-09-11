open import Lattice
open import Generic.Graph
open import Generic.IGraph

module Generic.Memory.Graph
  {{𝑳 : Lattice}}
  {Ty₁ Ty₂ : Set}
  {Value₁ : Ty₁ → Set}
  {Value₂ : Ty₂ → Set}
  {⟪_⟫ᵗ : Ty₁ → Ty₂}
  {⟪_⟫ⱽ : ∀ {τ} → Value₁ τ → Value₂ ⟪ τ ⟫ᵗ}
  (𝑮ᵗ : Graph ⟪_⟫ᵗ)
  (𝑮ⱽ : IGraph 𝑮ᵗ {Value₁} {Value₂} ⟪_⟫ⱽ) where

open import Data.Unit
open import Generic.Container.Convert.Graph Label 𝑮ᵗ 𝑮ⱽ
  renaming ( Graphᶜ to Fg2Cgᴹ
           ; mkGraphᶜ to mkFg2Cgᴹ
           ; ≡-Graphᶜ to ≡-mkFg2Cgᴹ
           ; unlift-⟪_⟫∈ to unlift-⟪_⟫∈ᴹ ) public
