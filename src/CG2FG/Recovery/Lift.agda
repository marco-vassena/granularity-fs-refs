-- CG L-equivalence (≈) of source terms implies FG L-equivalence of
-- the target (translated) terms.

open import Lattice

module CG2FG.Recovery.Lift {{𝑳 : Lattice}} (A : Label) where

open import CG as CG
open import FG as FG
open import CG.LowEq A as C
open import FG.LowEq A as F
open import CG2FG.Syntax

open import Data.Unit
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

mutual

  -- Environments
  lift-≈ᴱ : ∀ {Γ pc} {θ₁ θ₂ : CG.Env Γ} → θ₁ C.≈ᴱ θ₂ → ⟦ θ₁ ⟧ᵉ pc F.≈ᴱ ⟦ θ₂ ⟧ᵉ pc
  lift-≈ᴱ [] = []
  lift-≈ᴱ (v₁≈v₂ ∷ θ₁≈θ₂) = lift-≈ⱽ v₁≈v₂ ∷ lift-≈ᴱ θ₁≈θ₂

  -- Values.
  lift-≈ⱽ : ∀ {τ pc} {v₁ v₂ : CG.Value τ} → v₁ C.≈ⱽ v₂ → ⟦ v₁ ⟧ⱽ pc F.≈ⱽ ⟦ v₂ ⟧ⱽ pc
  lift-≈ⱽ {pc = pc} v₁≈v₂ with pc ⊑? A
  ... | yes p = Valueᴸ p (lift-≈ᴿ p v₁≈v₂)
  ... | no ¬p = Valueᴴ ¬p ¬p

  -- Raw values.
  lift-≈ᴿ :  ∀ {τ pc} {v₁ v₂ : CG.Value τ} → pc ⊑ A → v₁ C.≈ⱽ v₂ → ⟦ v₁ ⟧ᴿ pc F.≈ᴿ ⟦ v₂ ⟧ᴿ pc
  lift-≈ᴿ pc⊑A Unit = Unit
  lift-≈ᴿ pc⊑A (Lbl ℓ) = Lbl ℓ
  lift-≈ᴿ pc⊑A (Inl v₁≈v₂) = Inl (lift-≈ⱽ v₁≈v₂)
  lift-≈ᴿ pc⊑A (Inr v₁≈v₂) = Inr (lift-≈ⱽ v₁≈v₂)
  lift-≈ᴿ pc⊑A (Pair v₁≈v₂ v₁≈v₃) = Pair (lift-≈ⱽ v₁≈v₂) (lift-≈ⱽ v₁≈v₃)
  lift-≈ᴿ pc⊑A (Fun x) = Fun (lift-≈ᴱ x)
  lift-≈ᴿ pc⊑A (Thunk′ x) = Fun (lift-≈ᴱ x)
  lift-≈ᴿ pc⊑A (Labeledᴸ {ℓ = ℓ} ℓ⊑A v₁≈v₂) = Id (Valueᴸ pc⊑A (Pair (Valueᴸ ℓ⊑A (Lbl ℓ)) (lift-≈ⱽ v₁≈v₂)))
  lift-≈ᴿ pc⊑A (Labeledᴴ x x₁) = Id (Valueᴸ pc⊑A (Pair (Valueᴴ x x₁) (Valueᴴ x x₁)))
  lift-≈ᴿ pc⊑A (Refᴸ ℓ⊑A n) = Refᴸ ℓ⊑A n
  lift-≈ᴿ pc⊑A (Refᴴ ℓ₁⋤A ℓ₂⋤A) = Refᴴ ℓ₁⋤A ℓ₂⋤A

-- Public memories.
lift-≈ᴹ : ∀ {ℓ} {M₁ M₂ : CG.Memory ℓ} → ℓ ⊑ A → M₁ C.≈ᴹ M₂ → ⟦ M₁ ⟧ᴹ F.≈ᴹ ⟦ M₂ ⟧ᴹ
lift-≈ᴹ ℓ⊑A C.[] = F.[]
lift-≈ᴹ ℓ⊑A (v₁≈v₂ C.∷ M₁≈M₂) = lift-≈ᴿ ℓ⊑A v₁≈v₂ F.∷ lift-≈ᴹ ℓ⊑A M₁≈M₂

-- Memories.
lift-≈⟨_⟩ᴹ : ∀ {ℓ} {M₁ M₂ : CG.Memory ℓ} → (x : Dec (ℓ ⊑ A)) → M₁ C.≈⟨ x ⟩ᴹ M₂ → ⟦ M₁ ⟧ᴹ F.≈⟨ x ⟩ᴹ ⟦ M₂ ⟧ᴹ
lift-≈⟨ yes p ⟩ᴹ M₁≈M₂ = lift-≈ᴹ p M₁≈M₂
lift-≈⟨ no ¬p ⟩ᴹ M₁≈M₂ = tt

-- Stores.
lift-≈ˢ : ∀ {Σ₁ Σ₂} → Σ₁ C.≈ˢ Σ₂ → ⟦ Σ₁ ⟧ˢ F.≈ˢ ⟦ Σ₂ ⟧ˢ
lift-≈ˢ Σ₁≈Σ₂ = λ ℓ → lift-≈⟨ ℓ ⊑? A ⟩ᴹ (Σ₁≈Σ₂ ℓ)

-- Initial configurations.
lift-≈ᴵ : ∀ {τ Γ} {c₁ c₂ : EConf Γ (LIO τ)} → c₁ C.≈ᴵ c₂ → ⟦ c₁ ⟧ᴵ F.≈ᴵ ⟦ c₂ ⟧ᴵ
lift-≈ᴵ ⟨ Σ₁≈Σ₂ , refl , refl ⟩ = ⟨ lift-≈ˢ Σ₁≈Σ₂  , refl ⟩
