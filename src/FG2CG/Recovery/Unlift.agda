-- CG L-equivalence of target (translated) terms implies
-- L-equivalence of the original source FG terms.

open import Lattice

module FG2CG.Recovery.Unlift {{𝑳 : Lattice}} (A : Label) where

open import FG as FG
open import CG as CG
open import FG.LowEq A as F
open import CG.LowEq A as C
open import FG2CG.Syntax
open import FG2CG.Graph as G
open import FG2CG.Recovery.Injective
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Unit

private

  -- This module performs unlifting using the graph of the translation function.
  module Aux where

    mutual

      unlift-≈ᴱ : ∀ {Γ Γ' c₁ c₂ β} {θ₁ θ₂ : FG.Env Γ} {θ₁' θ₂' : CG.Env Γ'} →
                    θ₁' C.≈⟨ β ⟩ᴱ θ₂' →
                    Fg2Cgᵉ c₁ θ₁ θ₁' →
                    Fg2Cgᵉ c₂ θ₂ θ₂' →
                    θ₁ F.≈⟨ β ⟩ᴱ θ₂
      unlift-≈ᴱ C.[] G.[] G.[] = []
      unlift-≈ᴱ (v₁≈v₂ C.∷ θ₁≈θ₂) (x₁ G.∷ x₂) (y₁ G.∷ y₂) = unlift-≈ⱽ v₁≈v₂ x₁ y₁ ∷ unlift-≈ᴱ θ₁≈θ₂ x₂ y₂

      unlift-≈ᴿ : ∀ {τ τ' p₁ p₂ β} {r₁ r₂ : FG.Raw τ} {r₁' r₂' : CG.Value τ'} →
                    r₁' C.≈⟨ β ⟩ⱽ r₂' →
                    Fg2Cgᴿ p₁ r₁ r₁' →
                    Fg2Cgᴿ p₂ r₂ r₂' →
                    r₁ F.≈⟨ β ⟩ᴿ r₂
      unlift-≈ᴿ C.Unit G.Unit G.Unit = Unit
      unlift-≈ᴿ (C.Lbl .ℓ₁) (G.Lbl .ℓ₁) (G.Lbl ℓ₁) = Lbl ℓ₁
      unlift-≈ᴿ (C.Inl a) (G.Inl b) (G.Inl c) = Inl (unlift-≈ⱽ a b c)
      unlift-≈ᴿ (C.Inr a) (G.Inr b) (G.Inr c) = Inr (unlift-≈ⱽ a b c)
      unlift-≈ᴿ (C.Pair l₁≈l₂ r₁≈r₂) (G.Pair l₁ r₁) (G.Pair l₂ r₂) = Pair (unlift-≈ⱽ l₁≈l₂ l₁ l₂ ) (unlift-≈ⱽ r₁≈r₂ r₁ r₂)
      unlift-≈ᴿ (C.Fun θ₁≈θ₂′) (G.Fun {c = a} x₁ x₂) (G.Fun {c = b} y₁ y₂) with ≡-MkCtx a | ≡-MkCtx b
      ... | eq₁ | eq₂  rewrite eq₁ | inj-⟪ eq₂ ⟫ᶜ | inj-⟪·⟫ᴱ x₂ y₂ = Fun (unlift-≈ᴱ θ₁≈θ₂′ x₁ y₁)
      unlift-≈ᴿ (C.Refᴸ ℓ⊑A n) G.Ref G.Ref = Refᴸ ℓ⊑A _
      unlift-≈ᴿ (C.Refᴴ ℓ₁⋤A ℓ₂⋤A) G.Ref G.Ref = Refᴴ ℓ₁⋤A ℓ₂⋤A
      unlift-≈ᴿ a (Id b) (Id c) = Id (unlift-≈ⱽ a b c)

      unlift-≈ⱽ : ∀ {τ τ' p₁ p₂ β} {v₁ v₂ : FG.Value τ} {v₁' v₂' : CG.Value (Labeled τ')} →
                    v₁' C.≈⟨ β ⟩ⱽ v₂' →
                    Fg2Cgⱽ p₁ v₁ v₁' →
                    Fg2Cgⱽ p₂ v₂ v₂' →
                    v₁ F.≈⟨ β ⟩ⱽ v₂
      unlift-≈ⱽ (C.Labeledᴸ ℓ⊑A a) (G.Labeled .ℓ b) (G.Labeled ℓ c) = Valueᴸ ℓ⊑A (unlift-≈ᴿ a b c)
      unlift-≈ⱽ (C.Labeledᴴ ℓ⋤A a) (G.Labeled ℓ b) (G.Labeled ℓ₁ c) = Valueᴴ ℓ⋤A a

      unlift-≈ᴹ : ∀ {ℓ β} {M₁ M₂ : FG.Memory ℓ} {M₁' M₂' : CG.Memory ℓ} →
                     M₁' C.≈⟨ β ⟩ᴹ M₂' →
                     Fg2Cgᴹ M₁ M₁' →
                     Fg2Cgᴹ M₂ M₂' →
                     M₁ F.≈⟨ β ⟩ᴹ M₂
      unlift-≈ᴹ C.[] [] []  = F.[]
      unlift-≈ᴹ (v₁≈v₂ C.∷ M₁≈M₂) (G._∷_ {p = p} x₁ x₂) (G._∷_ {p = q} y₁ y₂) with ≡-MkTy′ p | ≡-MkTy′ q | inj-MkTy′ p q
      ... | eq₁ | eq₂ | eq₃ rewrite eq₁ | eq₂ | eq₃ = unlift-≈ᴿ v₁≈v₂ x₁ y₁ F.∷ unlift-≈ᴹ  M₁≈M₂ x₂ y₂


-- Public memories.
unlift-≈ᴹ : ∀ {ℓ β} {M₁ M₂ : FG.Memory ℓ} → ⟪ M₁ ⟫ᴹ C.≈⟨ β ⟩ᴹ ⟪ M₂ ⟫ᴹ → M₁ F.≈⟨ β ⟩ᴹ M₂
unlift-≈ᴹ ⟪M₁≈M₂⟫ = Aux.unlift-≈ᴹ ⟪M₁≈M₂⟫ (mkFg2Cgᴹ _) (mkFg2Cgᴹ _)

-- Memories.
unlift-≈⟨_⟩ᴹ : ∀ {ℓ β} {M₁ M₂ : FG.Memory ℓ} (x : Dec (ℓ ⊑ A)) → ⟪ M₁ ⟫ᴹ C.≈⟨ x , β ⟩ᴹ ⟪ M₂ ⟫ᴹ → M₁ F.≈⟨ x , β ⟩ᴹ M₂
unlift-≈⟨ yes p ⟩ᴹ ⟪M₁≈M₂⟫ = unlift-≈ᴹ ⟪M₁≈M₂⟫
unlift-≈⟨ no ¬p ⟩ᴹ _ = tt

-- Stores.
unlift-≈ˢ : ∀ {Σ₁ Σ₂ β} → ⟪ Σ₁ ⟫ˢ C.≈⟨ β ⟩ˢ ⟪ Σ₂ ⟫ˢ → Σ₁ F.≈⟨ β ⟩ˢ Σ₂
unlift-≈ˢ ⟪Σ₁≈Σ₂⟫ ℓ = unlift-≈⟨ ℓ ⊑? A ⟩ᴹ (⟪Σ₁≈Σ₂⟫ ℓ)

-- Raw values.
unlift-≈ᴿ : ∀ {τ} {r₁ r₂ : FG.Raw τ} →
              ⟪ r₁ ⟫ᴿ C.≈⟨ β ⟩ⱽ ⟪ r₂ ⟫ᴿ →
              r₁ F.≈⟨ β ⟩ᴿ r₂
unlift-≈ᴿ ⟪r₁≈r₂⟫ = Aux.unlift-≈ᴿ ⟪r₁≈r₂⟫ (mkFg2Cgᴿ _) (mkFg2Cgᴿ _)

-- Values.
unlift-≈ⱽ : ∀ {τ} {v₁ v₂ : FG.Value τ} →
              ⟪ v₁ ⟫ⱽ C.≈ⱽ ⟪ v₂ ⟫ⱽ →
              v₁ F.≈ⱽ v₂
unlift-≈ⱽ ⟪v₁≈v₂⟫ = Aux.unlift-≈ⱽ ⟪v₁≈v₂⟫ (mkFg2Cgⱽ _) (mkFg2Cgⱽ _)

-- Environments.
unlift-≈ᴱ :  ∀ {Γ} {θ₁ θ₂ : FG.Env Γ} →
               ⟪ θ₁ ⟫ᵉ C.≈ᴱ ⟪ θ₂ ⟫ᵉ →
               θ₁ F.≈ᴱ θ₂
unlift-≈ᴱ ⟪θ₁≈θ₂⟫ = Aux.unlift-≈ᴱ ⟪θ₁≈θ₂⟫ (mkFg2Cgᵉ _) (mkFg2Cgᵉ _)

-- Initial configurations (not needed).
unlift-≈ᴵ : ∀ {τ Γ β} {c₁ c₂ : IConf Γ τ} → (pc : Label) → ⟪ c₁ ⟫ᴵ pc C.≈⟨ β ⟩ᴵ ⟪ c₂ ⟫ᴵ pc → c₁ F.≈⟨ β ⟩ᴵ c₂
unlift-≈ᴵ pc ⟨ ≈ˢ , refl , term-≡ ⟩ = ⟨ unlift-≈ˢ ≈ˢ , inj-⟪ term-≡ ⟫ᴱ ⟩

-- Final configurations.
unlift-≈ᶜ : ∀ {pc τ β} {c₁ c₂ : FG.FConf τ} →
            let ⟨ _ , _ ^ ℓ₁ ⟩ = c₁
                ⟨ _ , _ ^ ℓ₂ ⟩ = c₂ in
                pc ⊑ ℓ₁ →
                pc ⊑ ℓ₂ →
                ⟪ c₁ ⟫ pc C.≈⟨ β ⟩ᶜ ⟪ c₂ ⟫ pc →
                c₁ F.≈⟨ β ⟩ᶜ c₂
unlift-≈ᶜ pc⊑ℓ₁ pc⊑ℓ₂ (pcᴸ Σ≈ pc⊑A v≈) = ⟨ unlift-≈ˢ Σ≈ , unlift-≈ⱽ v≈ ⟩
unlift-≈ᶜ pc⊑ℓ₁ pc⊑ℓ₂ (pcᴴ Σ≈ pc⋤A _) = ⟨ unlift-≈ˢ Σ≈ , Valueᴴ (trans-⋤ pc⊑ℓ₁ pc⋤A) (trans-⋤ pc⊑ℓ₂ pc⋤A)  ⟩
