-- This module recovers a CG TINI proof from FG TINI and the CG → FG
-- translation.

open import Lattice

module CG2FG.Recovery {{𝑳 : Lattice}} (A : Label) where

open import CG hiding (_⊆_ ; _×_)
open import CG2FG.Correct
open import FG.Security A
open import CG.LowEq A as C
open import Generic.Bijection

open import Data.Product
open _≈⟨_⟩ᴬ_

open import CG2FG.Recovery.Lift A public
open import CG2FG.Recovery.Unlift A public

-- Recovery of TINI
--
-- The proof is structured as follows:
-- 1) Apply the semantics preserving transformation.
-- 2) Lift L-equivalence of initial configurations and environments from CG to FG.
-- 3) Apply FG TINI to CG translated program and obtain FG L-equivalence.
-- 4) Back-translate L-equivalence of final configurations from FG to CG (unlifting).

-- TODO: use TINI shorthand?
tini-via-fg : ∀ {τ Γ θ₁ θ₂ β} {c₁ c₂ : EConf Γ (LIO τ)} {c₁' c₂' : FConf τ} →
                {{valid₁ : Valid-Inputs c₁ θ₁}} {{valid₂ : Valid-Inputs c₂ θ₂}} →
                 c₁ ⇓ᶠ⟨ θ₁ ⟩ c₁' →
                 c₂ ⇓ᶠ⟨ θ₂ ⟩ c₂' →
                 c₁ C.≈⟨ β ⟩ᴵ c₂ →
                 θ₁ C.≈⟨ β ⟩ᴱ θ₂ →
                 ∃ (λ β' → β ⊆ β' × c₁' C.≈⟨ β' ⟩ᶜ c₂')
tini-via-fg {c₁ = c₁} {c₂} {{isV₁}} {{isV₂}} x₁ x₂ c₁≈c₂ θ₁≈θ₂ with ⟦·⟧-correct x₁ | ⟦·⟧-correct x₂
... | c₁' , c₁≈′ , x₁' | c₂' , c₂≈′ , x₂' with lift-Valid-Inputs c₁ _ isV₁ |  lift-Valid-Inputs c₂ _ isV₂
... | isV₁′ | isV₂′ rewrite pc-≡ c₁≈c₂ with tini {{ isV₁′ }} {{ isV₂′ }} x₁' x₂' (lift-≈ᴵ c₁≈c₂) (lift-≈ᴱ θ₁≈θ₂)
... | β' , β⊆β' , c₁'≈c₂' = β' , β⊆β' , unlift-≈ᶜ c₁'≈c₂' c₁≈′ c₂≈′
