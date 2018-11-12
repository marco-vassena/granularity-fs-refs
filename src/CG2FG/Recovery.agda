-- This module recovers a CG TINI proof from FG TINI and the CG → FG
-- translation.

open import Lattice

module CG2FG.Recovery {{𝑳 : Lattice}} (A : Label) where

open import CG
open import CG2FG.Correct
open import FG.Security A
open import CG.LowEq A as C

open import Data.Product
open _≈ᴬ_

open import CG2FG.Recovery.Lift A public
open import CG2FG.Recovery.Unlift A public

-- Recovery of TINI
--
-- The proof is structured as follows:
-- 1) Apply the semantics preserving transformation.
-- 2) Lift L-equivalence of initial configurations and environments from CG to FG.
-- 3) Apply FG TINI to CG translated program and obtain FG L-equivalence.
-- 4) Back-translate L-equivalence of final configurations from FG to CG (unlifting).

tini-via-fg : ∀ {τ Γ θ₁ θ₂} {c₁ c₂ : EConf Γ (LIO τ)} {c₁' c₂' : FConf τ} →
                 c₁ ⇓ᶠ⟨ θ₁ ⟩ c₁' →
                 c₂ ⇓ᶠ⟨ θ₂ ⟩ c₂' →
                 c₁ C.≈ᴵ c₂ →
                 θ₁ C.≈ᴱ θ₂ →
                 c₁' C.≈ᶜ c₂'
tini-via-fg x₁ x₂ c₁≈c₂ θ₁≈θ₂ with ⟦·⟧-correct x₁ | ⟦·⟧-correct x₂
... | c₁' , c₁≈′ , x₁' | c₂' , c₂≈′ , x₂' rewrite pc-≡ c₁≈c₂ with tini x₁' x₂' (lift-≈ᴵ c₁≈c₂) (lift-≈ᴱ θ₁≈θ₂)
... | c₁'≈c₂' = unlift-≈ᶜ c₁'≈c₂' c₁≈′ c₂≈′
