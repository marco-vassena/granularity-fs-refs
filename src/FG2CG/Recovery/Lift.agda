-- FG L-equivalence (≈) of source terms implies CG L-equivalence of
-- the target (translated) terms.

open import Lattice

module FG2CG.Recovery.Lift {{𝑳 : Lattice}} (A : Label) where

open import FG as FG
open import CG as CG
open import FG.LowEq A as F
open import CG.LowEq A as C
open import FG2CG.Syntax
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Unit

mutual

  -- Environments.
  lift-≈ᴱ : ∀ {Γ} {θ₁ θ₂ : FG.Env Γ} →
             θ₁ F.≈ᴱ θ₂  →
             ⟪ θ₁ ⟫ᵉ C.≈ᴱ ⟪ θ₂ ⟫ᵉ
  lift-≈ᴱ [] = []
  lift-≈ᴱ (v₁≈v₂ ∷ θ₁≈θ₂) = (lift-≈ⱽ v₁≈v₂) ∷ (lift-≈ᴱ θ₁≈θ₂)

  -- Values.
  lift-≈ⱽ : ∀ {τ} {v₁ v₂ : FG.Value τ} →
            v₁ F.≈ⱽ v₂  →
            ⟪ v₁ ⟫ⱽ C.≈ⱽ ⟪ v₂ ⟫ⱽ
  lift-≈ⱽ (Valueᴸ ℓ⊑A r₁≈r₂) = Labeledᴸ ℓ⊑A (lift-≈ᴿ r₁≈r₂)
  lift-≈ⱽ (Valueᴴ ℓ₁⋤A ℓ₂⋤A) = Labeledᴴ ℓ₁⋤A ℓ₂⋤A

  -- Raw values.
  lift-≈ᴿ : ∀ {τ} {r₁ r₂ : FG.Raw τ} →
            r₁ F.≈ᴿ r₂ →
            ⟪ r₁ ⟫ᴿ C.≈ⱽ ⟪ r₂ ⟫ᴿ
  lift-≈ᴿ Unit = Unit
  lift-≈ᴿ (Lbl ℓ) = Lbl ℓ
  lift-≈ᴿ (Inl v₁≈v₂) = Inl (lift-≈ⱽ v₁≈v₂)
  lift-≈ᴿ (Inr v₁≈v₂) = Inr (lift-≈ⱽ v₁≈v₂)
  lift-≈ᴿ (Pair v₁≈v₁' v₂≈v₂') = Pair (lift-≈ⱽ v₁≈v₁') (lift-≈ⱽ v₂≈v₂')
  lift-≈ᴿ (Fun θ₁≈θ₂) = Fun (lift-≈ᴱ θ₁≈θ₂)
  lift-≈ᴿ (Refᴸ ℓ⊑A n) = Refᴸ ℓ⊑A n
  lift-≈ᴿ (Refᴴ ℓ₁⋤A ℓ₂⋤A) = Refᴴ ℓ₁⋤A ℓ₂⋤A
  lift-≈ᴿ (Id v₁≈v₂) = lift-≈ⱽ v₁≈v₂

-- Public memories.
lift-≈ᴹ : ∀ {ℓ} {M₁ M₂ : FG.Memory ℓ} → M₁ F.≈ᴹ M₂ → ⟪ M₁ ⟫ᴹ C.≈ᴹ ⟪ M₂ ⟫ᴹ
lift-≈ᴹ F.[] = C.[]
lift-≈ᴹ (v₁≈v₂ F.∷ M₁≈M₂) = lift-≈ᴿ v₁≈v₂ C.∷ lift-≈ᴹ M₁≈M₂

-- Memories.
lift-≈⟨_⟩ᴹ : ∀ {ℓ} {M₁ M₂ : FG.Memory ℓ} → (x : Dec (ℓ ⊑ A)) →
               M₁ F.≈⟨ x ⟩ᴹ M₂ →
               ⟪ M₁ ⟫ᴹ C.≈⟨ x ⟩ᴹ ⟪ M₂ ⟫ᴹ
lift-≈⟨ yes p ⟩ᴹ M₁≈M₂ = lift-≈ᴹ M₁≈M₂
lift-≈⟨ no ¬p ⟩ᴹ M₁≈M₂ = tt

-- Stores.
lift-≈ˢ : ∀ {Σ₁ Σ₂} → Σ₁ F.≈ˢ Σ₂ → ⟪ Σ₁ ⟫ˢ C.≈ˢ ⟪ Σ₂ ⟫ˢ
lift-≈ˢ Σ₁≈Σ₂ = λ ℓ → lift-≈⟨ ℓ ⊑? A ⟩ᴹ (Σ₁≈Σ₂ ℓ)

-- Initial configurations.
lift-≈ᴵ : ∀ {τ Γ} {c₁ c₂ : FG.IConf Γ τ} → (pc : Label) →
         c₁ F.≈ᴵ c₂  → ⟪ c₁ ⟫ᴵ pc C.≈ᴵ ⟪ c₂ ⟫ᴵ pc
lift-≈ᴵ pc ⟨ Σ₁≈Σ₂ , refl ⟩ = ⟨ lift-≈ˢ Σ₁≈Σ₂ , refl , refl ⟩
