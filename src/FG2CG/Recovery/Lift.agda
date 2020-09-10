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
  lift-≈ᴱ : ∀ {Γ β} {θ₁ θ₂ : FG.Env Γ} →
             θ₁ F.≈⟨ β ⟩ᴱ θ₂  →
             ⟪ θ₁ ⟫ᵉ C.≈⟨ β ⟩ᴱ ⟪ θ₂ ⟫ᵉ
  lift-≈ᴱ [] = []
  lift-≈ᴱ (v₁≈v₂ ∷ θ₁≈θ₂) = (lift-≈ⱽ v₁≈v₂) ∷ (lift-≈ᴱ θ₁≈θ₂)

  -- Values.
  lift-≈ⱽ : ∀ {τ β} {v₁ v₂ : FG.Value τ} →
            v₁ F.≈⟨ β ⟩ⱽ v₂  →
            ⟪ v₁ ⟫ⱽ C.≈⟨ β ⟩ⱽ ⟪ v₂ ⟫ⱽ
  lift-≈ⱽ (Valueᴸ ℓ⊑A r₁≈r₂) = Labeledᴸ ℓ⊑A (lift-≈ᴿ r₁≈r₂)
  lift-≈ⱽ (Valueᴴ ℓ₁⋤A ℓ₂⋤A) = Labeledᴴ ℓ₁⋤A ℓ₂⋤A

  -- Raw values.
  lift-≈ᴿ : ∀ {τ β} {r₁ r₂ : FG.Raw τ} →
            r₁ F.≈⟨ β ⟩ᴿ r₂ →
            ⟪ r₁ ⟫ᴿ C.≈⟨ β ⟩ⱽ ⟪ r₂ ⟫ᴿ
  lift-≈ᴿ Unit = Unit
  lift-≈ᴿ (Lbl ℓ) = Lbl ℓ
  lift-≈ᴿ (Inl v₁≈v₂) = Inl (lift-≈ⱽ v₁≈v₂)
  lift-≈ᴿ (Inr v₁≈v₂) = Inr (lift-≈ⱽ v₁≈v₂)
  lift-≈ᴿ (Pair v₁≈v₁' v₂≈v₂') = Pair (lift-≈ⱽ v₁≈v₁') (lift-≈ⱽ v₂≈v₂')
  lift-≈ᴿ (Fun θ₁≈θ₂) = Fun (lift-≈ᴱ θ₁≈θ₂)
  lift-≈ᴿ (Ref-Iᴸ ℓ⊑A) = Ref-Iᴸ ℓ⊑A _
  lift-≈ᴿ (Ref-Iᴴ ℓ₁⋤A ℓ₂⋤A) = Ref-Iᴴ ℓ₁⋤A ℓ₂⋤A
  lift-≈ᴿ (Ref-S x) = Ref-S x
  lift-≈ᴿ (Id v₁≈v₂) = lift-≈ⱽ v₁≈v₂

import Generic.Memory.LowEq {FG.Ty} {FG.Value} F._≈⟨_⟩ⱽ_ A as FM
import Generic.Memory.LowEq {CG.Ty} {CG.Value} C._≈⟨_⟩ⱽ_ A as CM

-- open F._≈⟨_⟩ᴹ_
-- Public memories.
lift-≈ᴹ : ∀ {ℓ β} {M₁ M₂ : FG.Memory ℓ} → M₁ F.≈⟨ β ⟩ᴹ M₂ → ⟪ M₁ ⟫ᴹ C.≈⟨ β ⟩ᴹ ⟪ M₂ ⟫ᴹ
lift-≈ᴹ FM.[] = CM.[]
lift-≈ᴹ (v₁≈v₂ FM.∷ M₁≈M₂) = lift-≈ᴿ v₁≈v₂ CM.∷ lift-≈ᴹ M₁≈M₂

-- Memories.
lift-≈⟨_⟩ᴹ : ∀ {ℓ β} {M₁ M₂ : FG.Memory ℓ} → (x : Dec (ℓ ⊑ A)) →
               M₁ F.≈⟨ β , x ⟩ᴹ M₂ →
               ⟪ M₁ ⟫ᴹ C.≈⟨ β , x ⟩ᴹ ⟪ M₂ ⟫ᴹ
lift-≈⟨ yes p ⟩ᴹ M₁≈M₂ = lift-≈ᴹ M₁≈M₂
lift-≈⟨ no ¬p ⟩ᴹ M₁≈M₂ = tt

-- Stores.
lift-≈ˢ : ∀ {Σ₁ Σ₂ β} → Σ₁ F.≈⟨ β ⟩ˢ Σ₂ → ⟪ Σ₁ ⟫ˢ C.≈⟨ β ⟩ˢ ⟪ Σ₂ ⟫ˢ
lift-≈ˢ Σ₁≈Σ₂ = λ ℓ → lift-≈⟨ ℓ ⊑? A ⟩ᴹ (Σ₁≈Σ₂ ℓ)

-- Heaps
lift-≈ᴴ : ∀ {μ₁ μ₂ β} → μ₁ F.≈⟨ β ⟩ᴴ μ₂ → ⟪ μ₁ ⟫ᴴ C.≈⟨ β ⟩ᴴ ⟪ μ₂ ⟫ᴴ
lift-≈ᴴ {μ₁} {μ₂} {β} μ₁≈μ₂ = record { dom-⊆ = lift-dom-⊆ ; rng-⊆ = lift-rng-⊆ ; lift-≅ = lift-lift-≅ }
  where open import Generic.Heap.Lemmas CG.Ty CG.LValue as HC
        open import Generic.Heap.Lemmas FG.Ty FG.Value as HF
        open import Generic.Value.HLowEq {CG.Ty} {CG.LValue} C._≈⟨_⟩ᴸ_ as CH
        open import FG2CG.Graph.Types
        open import FG2CG.Graph.Value
        open import Generic.Heap.Graph Graph-⟪·⟫ᵗ′ Graph-⟪·⟫ᴸ
        open F._≈⟨_⟩ᴴ_ μ₁≈μ₂
        open import Data.Product

        lift-dom-⊆ : β C.⊆ᴰ ⟪ μ₁ ⟫ᴴ
        lift-dom-⊆ ∈ᴮ with HF.∈-< (dom-⊆ ∈ᴮ)
        ... | ≤₁ rewrite sym (∥ μ₁ ∥-≡ᴴ) = HC.<-∈ ≤₁

        lift-rng-⊆ : β C.⊆ᴿ ⟪ μ₂ ⟫ᴴ
        lift-rng-⊆ ∈ᴮ with HF.∈-< (rng-⊆ ∈ᴮ)
        ... | ≤₁ rewrite sym (∥ μ₂ ∥-≡ᴴ) = HC.<-∈ ≤₁

        lift-lift-≅ : C.Lift-≅ ⟪ μ₁ ⟫ᴴ ⟪ μ₂ ⟫ᴴ β
        lift-lift-≅ {τ₁ = τ₁} {τ₂ = τ₂} {v₁ = v₁} ∈ᴮ ∈₁ ∈₂ with unlift-⟪ ∈₁ ⟫∈′′ | unlift-⟪ ∈₂ ⟫∈′′
        ... | τ₁′ , v₁′ , ∈₁′ , refl , refl | τ₂′ , v₂′ , ∈₂′ , refl , refl with lift-≅ ∈ᴮ ∈₁′ ∈₂′
        ... | F.⌞ v≈ ⌟ = CH.⌞ lift-≈ⱽ v≈  ⌟

lift-≈ᴾ : ∀ {p₁ p₂ β} → p₁ F.≈⟨ β ⟩ᴾ p₂ → ⟪ p₁ ⟫ᴾ C.≈⟨ β ⟩ᴾ ⟪ p₂ ⟫ᴾ
lift-≈ᴾ F.⟨ Σ₁≈Σ₂ , μ₁≈μ₂ ⟩ = C.⟨ lift-≈ˢ Σ₁≈Σ₂ , lift-≈ᴴ μ₁≈μ₂ ⟩

-- Initial configurations.
lift-≈ᴵ : ∀ {τ Γ β} {c₁ c₂ : FG.IConf Γ τ} → (pc : Label) →
         c₁ F.≈⟨ β ⟩ᴵ c₂  → ⟪ c₁ ⟫ᴵ pc C.≈⟨ β ⟩ᴵ ⟪ c₂ ⟫ᴵ pc
lift-≈ᴵ pc ⟨ ≈ᴾ , refl ⟩ = ⟨  lift-≈ᴾ ≈ᴾ , refl , refl ⟩
