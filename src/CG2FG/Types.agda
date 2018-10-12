module CG2FG.Types where

open import CG.Types as C
open import FG.Types as F

-- Type translation
⟦_⟧ᵗ : C.Ty → F.Ty
⟦ unit ⟧ᵗ = unit
⟦ τ × τ₁ ⟧ᵗ = ⟦ τ ⟧ᵗ × ⟦ τ₁ ⟧ᵗ
⟦ τ + τ₁ ⟧ᵗ = ⟦ τ ⟧ᵗ + ⟦ τ₁ ⟧ᵗ
⟦ τ ➔ τ₁ ⟧ᵗ = ⟦ τ ⟧ᵗ ➔ ⟦ τ₁ ⟧ᵗ
⟦ 𝓛 ⟧ᵗ = 𝓛
⟦ LIO τ ⟧ᵗ = Id unit ➔ ⟦ τ ⟧ᵗ
⟦ Labeled τ ⟧ᵗ = Id (𝓛 × ⟦ τ ⟧ᵗ)
⟦ Ref τ ⟧ᵗ = Ref ⟦ τ ⟧ᵗ

-- Derived context translation
open import Generic.Context.Convert {C.Ty} {F.Ty} ⟦_⟧ᵗ  renaming (
    ⟪_⟫ᶜ to ⟦_⟧ᶜ
  ; ⟪_⟫∈ to ⟦_⟧∈
  ; ⟪_⟫⊆ to ⟦_⟧⊆ ) public
