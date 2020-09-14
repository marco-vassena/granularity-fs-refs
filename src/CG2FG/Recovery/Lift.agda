-- CG L-equivalence (≈) of source terms implies FG L-equivalence of
-- the target (translated) terms.

open import Lattice

module CG2FG.Recovery.Lift {{𝑳 : Lattice}} (A : Label) where

open import CG as CG
open import FG as FG
open import CG.LowEq A as C
open import FG.LowEq A as F
open import CG2FG.Syntax
open import CG2FG.CrossEq using (𝑽ᴸ ; ⌞_⌟ᴸ ; unlift-∈ᴹ′ ; refl-↓≈ᴹ)
open import CG2FG.Graph
open import Generic.Heap.CrossEq {{𝑳}} {CG.Ty} {FG.Ty} 𝑻 {CG.LValue} {FG.Value} 𝑽ᴸ
open import CG2FG.Recovery.Injective
open import CG2FG.Recovery.Unlift A

open import Data.Unit
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

mutual

  -- Environments
  lift-≈ᴱ : ∀ {Γ pc β} {θ₁ θ₂ : CG.Env Γ} → θ₁ C.≈⟨ β ⟩ᴱ θ₂ → ⟦ θ₁ ⟧ᵉ pc F.≈⟨ β ⟩ᴱ ⟦ θ₂ ⟧ᵉ pc
  lift-≈ᴱ [] = []
  lift-≈ᴱ (v₁≈v₂ ∷ θ₁≈θ₂) = lift-≈ⱽ v₁≈v₂ ∷ lift-≈ᴱ θ₁≈θ₂

  -- Values.
  lift-≈ⱽ : ∀ {τ pc β} {v₁ v₂ : CG.Value τ} → v₁ C.≈⟨ β ⟩ⱽ v₂ → ⟦ v₁ ⟧ⱽ pc F.≈⟨ β ⟩ⱽ ⟦ v₂ ⟧ⱽ pc
  lift-≈ⱽ {pc = pc} v₁≈v₂ with pc ⊑? A
  ... | yes p = Valueᴸ p (lift-≈ᴿ p v₁≈v₂)
  ... | no ¬p = Valueᴴ ¬p ¬p

  -- Raw values.
  lift-≈ᴿ :  ∀ {τ pc β} {v₁ v₂ : CG.Value τ} → pc ⊑ A → v₁ C.≈⟨ β ⟩ⱽ v₂ → ⟦ v₁ ⟧ᴿ pc F.≈⟨ β ⟩ᴿ ⟦ v₂ ⟧ᴿ pc
  lift-≈ᴿ pc⊑A Unit = Unit
  lift-≈ᴿ pc⊑A (Lbl ℓ) = Lbl ℓ
  lift-≈ᴿ pc⊑A (Inl v₁≈v₂) = Inl (lift-≈ⱽ v₁≈v₂)
  lift-≈ᴿ pc⊑A (Inr v₁≈v₂) = Inr (lift-≈ⱽ v₁≈v₂)
  lift-≈ᴿ pc⊑A (Pair v₁≈v₂ v₁≈v₃) = Pair (lift-≈ⱽ v₁≈v₂) (lift-≈ⱽ v₁≈v₃)
  lift-≈ᴿ pc⊑A (Fun x) = Fun (lift-≈ᴱ x)
  lift-≈ᴿ pc⊑A (Thunk′ x) = Fun (lift-≈ᴱ x)
  lift-≈ᴿ pc⊑A (Labeledᴸ {ℓ = ℓ} ℓ⊑A v₁≈v₂) = Id (Valueᴸ pc⊑A (Pair (Valueᴸ ℓ⊑A (Lbl ℓ)) (lift-≈ⱽ v₁≈v₂)))
  lift-≈ᴿ pc⊑A (Labeledᴴ x x₁) = Id (Valueᴸ pc⊑A (Pair (Valueᴴ x x₁) (Valueᴴ x x₁)))
  lift-≈ᴿ pc⊑A (Ref-Iᴸ ℓ⊑A n) = Ref-Iᴸ ℓ⊑A
  lift-≈ᴿ pc⊑A (Ref-Iᴴ ℓ₁⋤A ℓ₂⋤A) = Ref-Iᴴ ℓ₁⋤A ℓ₂⋤A
  lift-≈ᴿ pc⊑A (Ref-S ∈ᴮ) = Ref-S ∈ᴮ

open import Generic.Memory.LowEq {CG.Ty} {CG.Value} C._≈⟨_⟩ⱽ_ as CM
open import Generic.Memory.LowEq {FG.Ty} {FG.Raw} F._≈⟨_⟩ᴿ_ as FM

-- Public memories.
lift-≈ᴹ : ∀ {ℓ β} {M₁ M₂ : CG.Memory ℓ} → ℓ ⊑ A → M₁ C.≈⟨ β ⟩ᴹ M₂ → ⟦ M₁ ⟧ᴹ F.≈⟨ β ⟩ᴹ ⟦ M₂ ⟧ᴹ
lift-≈ᴹ ℓ⊑A CM.[] = FM.[]
lift-≈ᴹ ℓ⊑A (v₁≈v₂ CM.∷ M₁≈M₂) = lift-≈ᴿ ℓ⊑A v₁≈v₂ FM.∷ lift-≈ᴹ ℓ⊑A M₁≈M₂

-- Memories.
lift-≈⟨_⟩ᴹ : ∀ {ℓ β} {M₁ M₂ : CG.Memory ℓ} → (x : Dec (ℓ ⊑ A)) → M₁ C.≈⟨ β , x ⟩ᴹ M₂ → ⟦ M₁ ⟧ᴹ F.≈⟨ β , x ⟩ᴹ ⟦ M₂ ⟧ᴹ
lift-≈⟨ yes p ⟩ᴹ M₁≈M₂ = lift-≈ᴹ p M₁≈M₂
lift-≈⟨ no ¬p ⟩ᴹ M₁≈M₂ = tt

-- Stores.
lift-≈ˢ : ∀ {Σ₁ Σ₂ β} → Σ₁ C.≈⟨ β ⟩ˢ Σ₂ → ⟦ Σ₁ ⟧ˢ F.≈⟨ β ⟩ˢ ⟦ Σ₂ ⟧ˢ
lift-≈ˢ Σ₁≈Σ₂ = λ ℓ → lift-≈⟨ ℓ ⊑? A ⟩ᴹ (Σ₁≈Σ₂ ℓ)

lift-≈ᴸ : ∀ {τ β} {lv₁ lv₂ : LValue τ} → lv₁ C.≈⟨ β ⟩ᴸ lv₂ → ⟦ lv₁ ⟧ᴸ F.≈⟨ β ⟩ⱽ ⟦ lv₂ ⟧ᴸ
lift-≈ᴸ (Labeledᴸ ⊑₁ r≈) = Valueᴸ ⊑₁ (lift-≈ᴿ ⊑₁ r≈)
lift-≈ᴸ (Labeledᴴ ⋤₁ ⋤₂) = Valueᴴ ⋤₁ ⋤₂

lift-≈ᴴ : ∀ {μ₁ μ₂ β} → μ₁ C.≈⟨ β ⟩ᴴ μ₂ → ⟦ μ₁ ⟧ᴴ F.≈⟨ β ⟩ᴴ ⟦ μ₂ ⟧ᴴ
lift-≈ᴴ {μ₁} {μ₂} {β} ≈ᴴ = record { dom-⊆ = lift-dom-⊆ ; rng-⊆ = lift-rng-⊆ ; lift-≅ = lift-lift-≅ }
  where open C._≈⟨_⟩ᴴ_ ≈ᴴ
        open import Generic.Heap.Lemmas CG.Ty CG.LValue as HC
        open import Generic.Heap.Lemmas FG.Ty FG.Value as HF
        open import Generic.Value.HLowEq {CG.Ty} {CG.LValue} C._≈⟨_⟩ᴸ_ as CH
        open import Generic.Value.HLowEq {FG.Ty} {FG.Value} F._≈⟨_⟩ⱽ_ as FH
        open import Data.Product

        lift-dom-⊆ : β F.⊆ᴰ ⟦ μ₁ ⟧ᴴ
        lift-dom-⊆ ∈₁ with HC.∈-< (dom-⊆ ∈₁)
        ... | ≤₁ rewrite sym (∥ μ₁ ∥-≡ᴴ) = HF.<-∈ ≤₁

        lift-rng-⊆ : β F.⊆ᴿ ⟦ μ₂ ⟧ᴴ
        lift-rng-⊆ ∈₁ with HC.∈-< (rng-⊆ ∈₁)
        ... | ≤₁ rewrite sym (∥ μ₂ ∥-≡ᴴ) = HF.<-∈ ≤₁

        lift-lift-≅ : F.Lift-≅ ⟦ μ₁ ⟧ᴴ ⟦ μ₂ ⟧ᴴ β
        lift-lift-≅ ∈ᴮ ∈₁ ∈₂ with unlift-∈ᴴ′ ∈₁ (refl-↓≈ᴴ μ₁) | unlift-∈ᴴ′ ∈₂ (refl-↓≈ᴴ μ₂)
        ... | τ₁ , (v₁ , refl) , ∈₁′ , refl | τ₂ , (v₂ , refl) , ∈₂′ , refl with lift-≅ ∈ᴮ ∈₁′ ∈₂′
        ... | CH.⌞ ≈lv ⌟ = FH.⌞ lift-≈ᴸ ≈lv ⌟


lift-≈ᴾ : ∀ {P₁ P₂ β} → P₁ C.≈⟨ β ⟩ᴾ P₂ → ⟦ P₁ ⟧ᴾ F.≈⟨ β ⟩ᴾ ⟦ P₂ ⟧ᴾ
lift-≈ᴾ C.⟨ ≈ˢ , ≈ᴴ ⟩ = F.⟨ lift-≈ˢ ≈ˢ , lift-≈ᴴ ≈ᴴ ⟩

-- Initial configurations.
lift-≈ᴵ : ∀ {τ Γ β} {c₁ c₂ : EConf Γ (LIO τ)} → c₁ C.≈⟨ β ⟩ᴵ c₂ → ⟦ c₁ ⟧ᴵ F.≈⟨ β ⟩ᴵ ⟦ c₂ ⟧ᴵ
lift-≈ᴵ ⟨ P₁≈P₂ , refl , refl ⟩ = ⟨ lift-≈ᴾ P₁≈P₂  , refl ⟩


--------------------------------------------------------------------------------
-- Lift valid proofs

open import Data.Product

mutual

  lift-Validᴱ : ∀ {n Γ pc} (θ : CG.Env Γ) → CG.Validᴱ n θ → FG.Validᴱ n (⟦ θ ⟧ᵉ pc)
  lift-Validᴱ [] isVᴱ = tt
  lift-Validᴱ (v ∷ θ) (isVⱽ , isVᴱ) = (lift-Validⱽ v isVⱽ) , (lift-Validᴱ θ isVᴱ)

  lift-Validⱽ : ∀ {n τ pc} (v : CG.Value τ) → CG.Validⱽ n v → FG.Validⱽ n (⟦ v ⟧ⱽ pc)
  lift-Validⱽ v isV = lift-Validᴿ v isV

  lift-Validᴿ : ∀ {n τ pc} (v : CG.Value τ) → CG.Validⱽ n v → FG.Validᴿ n (⟦ v ⟧ᴿ pc)
  lift-Validᴿ （） isVᴿ = tt
  lift-Validᴿ ⟨ x , θ ⟩ᶜ isVᴱ = lift-Validᴱ θ isVᴱ
  lift-Validᴿ (inl v) isVⱽ = lift-Validⱽ v isVⱽ
  lift-Validᴿ (inr v) isVⱽ = lift-Validⱽ v isVⱽ
  lift-Validᴿ ⟨ v₁ , v₂ ⟩ (isV₁ⱽ , isV₂ⱽ) = lift-Validⱽ v₁ isV₁ⱽ , lift-Validⱽ v₂ isV₂ⱽ
  lift-Validᴿ (Refᴵ v v₁) isVⱽ = tt
  lift-Validᴿ (Refˢ v) isVⱽ = isVⱽ
  lift-Validᴿ ⌞ _ ⌟ isVⱽ = tt
  lift-Validᴿ ⟨ t , θ ⟩ᵀ isVᴱ = lift-Validᴱ θ isVᴱ
  lift-Validᴿ (Labeled ℓ v) isVⱽ = tt , (lift-Validⱽ v isVⱽ)

import Generic.Memory CG.Ty CG.Value as MF
import Generic.Memory FG.Ty FG.Value as MC

lift-Validᴹ : ∀ {n ℓ} {M : CG.Memory ℓ} → CG.Validᴹ n M → FG.Validᴹ n ⟦ M ⟧ᴹ
lift-Validᴹ {n} {ℓ} {M} isVᴹ ∈₁ with unlift-∈ᴹ′ ∈₁ (refl-↓≈ᴹ M)
... | τ , (r , refl) , ⟦∈₁⟧ , refl = lift-Validᴿ r (isVᴹ ⟦∈₁⟧)

lift-Validˢ : ∀ {Σ n} → CG.Validˢ n Σ → FG.Validˢ n ⟦ Σ ⟧ˢ
lift-Validˢ isVˢ ℓ = lift-Validᴹ (isVˢ ℓ)

lift-Validᴴ : ∀ {μ} → CG.Validᴴ μ → FG.Validᴴ ⟦ μ ⟧ᴴ
lift-Validᴴ {μ} isVᴴ ∈₁ with unlift-∈ᴴ′ ∈₁ (refl-↓≈ᴴ μ)
... | τ , (lv , refl) , ⟦∈₁⟧ , refl
  rewrite sym (∥ μ ∥-≡ᴴ) = lift-Validⱽ (proj₁ lv) (isVᴴ ⟦∈₁⟧)

lift-Validᴾ : ∀ {p} → CG.Validᴾ p → FG.Validᴾ ⟦ p ⟧ᴾ
lift-Validᴾ {p} CG.⟨ isVˢ , isVᴴ ⟩ with lift-Validᴴ isVᴴ
... | isVᴴ′ rewrite sym (∥ CG.PState.heap p ∥-≡ᴴ) = FG.⟨ lift-Validˢ isVˢ , isVᴴ′ ⟩

lift-Valid-Inputs : ∀ {τ Γ} (c : CG.EConf Γ (LIO τ)) (θ : CG.Env Γ) →
                      CG.Valid-Inputs c θ → FG.Valid-Inputs ⟦ c ⟧ᴵ (⟦ θ ⟧ᵉ (CG.Conf.pc c))
lift-Valid-Inputs c θ (isVᴾ , isVᴱ)
  rewrite ∥ CG.Conf.heap c ∥-≡ᴴ = lift-Validᴾ isVᴾ , lift-Validᴱ θ isVᴱ
