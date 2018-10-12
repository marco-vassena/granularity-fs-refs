-- This module recovers a FG TINI proof from CG TINI and the FG → CG
-- translation.

open import Lattice

module FG2CG.Recovery {{𝑳 : Lattice}} (A : Label) where

open import FG as FG
open import CG as CG
open import CG.Security A
open import FG.LowEq A as F
open import FG2CG.Correct
open import FG2CG.Recovery.Lift A public
open import FG2CG.Recovery.Unlift A public

-- Recovery of TINI
--
-- The proof is structured as follows:
-- 1) Apply the semantics preserving transformation.
-- 2) Lift L-equivalence of initial configurations and environments from FG to CG.
-- 3) Apply CG TINI to CG translated program and obtain CG L-equivalence.
-- 4) Back-translate L-equivalence of final configurations from CG to FG (unlifting).

tini-via-cg :  ∀ {τ Γ θ₁ θ₂ pc} {c₁ c₂ : FG.IConf Γ τ} {c₁' c₂' : FG.FConf τ} →
                 c₁ ⇓⟨ θ₁ , pc ⟩ c₁' →
                 c₂ ⇓⟨ θ₂ , pc ⟩ c₂' →
                 c₁ F.≈ᴵ c₂ →
                 θ₁ F.≈ᴱ θ₂ →
                 c₁' F.≈ᶜ c₂'
tini-via-cg {pc = pc} x₁ x₂ c₁≈c₂ θ₁≈θ₂ with fg2cgᶠ x₁ | fg2cgᶠ x₂ | lift-≈ᴵ pc c₁≈c₂ | lift-≈ᴱ θ₁≈θ₂
... | x₁' | x₂' | ⟪c₁≈c₂⟫ | ⟪θ₁≈θ₂⟫ with tiniᶠ x₁' x₂' ⟪c₁≈c₂⟫ ⟪θ₁≈θ₂⟫
... | ⟪c₁'≈c₂'⟫ = unlift-≈ᶜ (FG.step-⊑ x₁) (FG.step-⊑ x₂) ⟪c₁'≈c₂'⟫
