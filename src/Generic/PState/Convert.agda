open import Lattice
open import Data.Unit

module Generic.PState.Convert
  {{𝑳 : Lattice}}
  {Ty₁ : Set} {Ty₂ : Set}
  (⟪_⟫₁ᵗ : Ty₁ → Ty₂)
  (⟪_⟫₂ᵗ : Ty₁ → Ty₂)
  {Valueˢ₁ : Ty₁ → Set} {Valueˢ₂ : Ty₂ → Set}
  {Valueᴴ₁ : Ty₁ → Set} {Valueᴴ₂ : Ty₂ → Set}
  (⟪_⟫ˢⱽ : ∀ {τ} → Valueˢ₁ τ → Label → Valueˢ₂ ⟪ τ ⟫₁ᵗ)
  (⟪_⟫ᴴⱽ : ∀ {τ} → Valueᴴ₁ τ → ⊤ → Valueᴴ₂ ⟪ τ ⟫₂ᵗ)
  where

open import Generic.Store.Convert {Ty₁} {Ty₂} {Valueˢ₁} {Valueˢ₂} ⟪_⟫₁ᵗ ⟪_⟫ˢⱽ public
open import Generic.Heap.Convert {Ty₁} {Ty₂} {Valueᴴ₁} {Valueᴴ₂} ⟪_⟫₂ᵗ (λ v → ⟪ v ⟫ᴴⱽ tt) public
open import Generic.PState Ty₁ Ty₁ Valueˢ₁ Valueᴴ₁ as S
open import Generic.PState Ty₂ Ty₂ Valueˢ₂ Valueᴴ₂ as T

⟪_⟫ᴾ : S.PState → T.PState
⟪ S.⟨ Σ , μ ⟩ ⟫ᴾ = T.⟨ ⟪ Σ ⟫ˢ , ⟪ μ ⟫ᴴ ⟩
