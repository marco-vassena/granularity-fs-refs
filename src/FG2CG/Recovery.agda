-- This module recovers a FG TINI proof from CG TINI and the FG → CG
-- translation.

open import Lattice

module FG2CG.Recovery {{𝑳 : Lattice}} (A : Label) where

open import FG as FG hiding (_×_ ; _⊆_)
open import CG as CG hiding (_×_ ; _⊆_)
open import CG.Security A
open import FG.LowEq A as F
open import FG2CG.Correct
open import FG2CG.Recovery.Lift A public
open import FG2CG.Recovery.Unlift A public
open import Generic.Partial.Bijection
open import Data.Product renaming (_,_ to _∧_)

-- Recovery of TINI
--
-- The proof is structured as follows:
-- 1) Apply the semantics preserving transformation.
-- 2) Lift L-equivalence of initial configurations and environments from FG to CG.
-- 3) Apply CG TINI to CG translated program and obtain CG L-equivalence.
-- 4) Back-translate L-equivalence of final configurations from CG to FG (unlifting).

tini-via-cg :  ∀ {τ Γ pc θ₁ θ₂ β} {c₁ c₂ : FG.IConf Γ τ} {c₁' c₂' : FG.FConf τ} →
                 {{valid₁ : FG.Valid-Inputs c₁ θ₁}} {{valid₂ : FG.Valid-Inputs c₂ θ₂}} →
                 c₁ ⇓⟨ θ₁ , pc ⟩ c₁' →
                 c₂ ⇓⟨ θ₂ , pc ⟩ c₂' →
                 c₁ F.≈⟨ β ⟩ᴵ c₂ →
                 θ₁ F.≈⟨ β ⟩ᴱ θ₂ →
                 ∃ (λ β' → β ⊆ β' × c₁' F.≈⟨ β' ⟩ᶜ c₂')
tini-via-cg {pc = pc} {c₁ = c₁} {c₂ = c₂} {{isV₁}} {{isV₂}} x₁ x₂ c₁≈c₂ θ₁≈θ₂
  with fg2cgᶠ x₁ | fg2cgᶠ x₂ | lift-≈ᴵ pc c₁≈c₂ | lift-≈ᴱ θ₁≈θ₂
... | x₁' | x₂' | ⟪c₁≈c₂⟫ | ⟪θ₁≈θ₂⟫
  with tiniᶠ {{ lift-Valid-Inputs pc c₁ _ isV₁ }} {{ lift-Valid-Inputs pc c₂ _ isV₂ }} x₁' x₂' ⟪c₁≈c₂⟫ ⟪θ₁≈θ₂⟫
... | β' ∧ β⊆β' ∧ ⟪c₁'≈c₂'⟫ = β' ∧ β⊆β' ∧ unlift-≈ᶜ (FG.step-⊑ x₁) (FG.step-⊑ x₂) ⟪c₁'≈c₂'⟫
