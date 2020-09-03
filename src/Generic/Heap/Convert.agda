open import Lattice

module Generic.Heap.Convert
  {{𝑳 : Lattice}}
  {Ty₁ Ty₂ : Set}
  {Value₁ : Ty₁ → Set}
  {Value₂ : Ty₂ → Set}
  (⟪_⟫ᵗ : Ty₁ → Ty₂)
  (⟪_⟫ⱽ : ∀ {τ} → Value₁ τ → Value₂ ⟪ τ ⟫ᵗ) where

open import Data.Unit
open import Generic.Container.Convert ⊤ {Ty₁} {Ty₂} {Value₁} {Value₂} ⟪_⟫ᵗ (λ v ℓ → ⟪ v ⟫ⱽ)
  renaming ( ⟪_⟫ᶜ to ⟪_⟫ᴴ
           ; ∥_∥-≡ to ∥_∥-≡ᴴ
           ; ⟪_⟫∈ to ⟪_⟫∈ᴴ
           ; write-≡ to write-≡ᴴ
           ; ∷ᴿ-≡ to snocᴴ-≡) public
