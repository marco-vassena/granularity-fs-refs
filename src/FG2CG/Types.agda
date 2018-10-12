-- This module contains the FG → CG converion for types.

module FG2CG.Types where

open import CG.Types as C
open import FG.Types as F

mutual

  -- Type translation
  ⟪_⟫ᵗ′ : F.Ty → C.Ty
  ⟪ F.unit ⟫ᵗ′ = unit
  ⟪ τ F.× τ₁ ⟫ᵗ′ = ⟪ τ ⟫ᵗ × ⟪ τ₁ ⟫ᵗ
  ⟪ τ F.+ τ₁ ⟫ᵗ′ = ⟪ τ ⟫ᵗ + ⟪ τ₁ ⟫ᵗ
  ⟪ τ F.➔ τ₁ ⟫ᵗ′ = ⟪ τ ⟫ᵗ ➔ LIO ⟪ τ₁ ⟫ᵗ
  ⟪ F.𝓛 ⟫ᵗ′ = 𝓛
  ⟪ F.Ref τ ⟫ᵗ′ = Ref ⟪ τ ⟫ᵗ′
  ⟪ Id τ ⟫ᵗ′ = ⟪ τ ⟫ᵗ

  ⟪_⟫ᵗ : F.Ty → C.Ty
  ⟪ τ ⟫ᵗ = Labeled ⟪ τ ⟫ᵗ′

-- Context translation is pointwise (derived generically).
open import Generic.Context.Convert {F.Ty} {C.Ty} ⟪_⟫ᵗ using (
    ⟪_⟫ᶜ
  ; ⟪_⟫∈
  ; ⟪_⟫⊆ ) public
