-- L-equivalence of FG target terms that are semantically equivalent
-- to source CG terms (up to FG extra annotations) implies
-- L-equivalence of the source CG terms.

open import Lattice

module CG2FG.Recovery.Unlift {{𝑳 : Lattice}} (A : Label) where

open import FG as FG
open import CG as CG
open import CG.LowEq A as C
import FG.LowEq A as F
open import CG2FG.CrossEq renaming (CEqᵉ to CEqᴱ)
open import CG2FG.Graph
open import CG2FG.Recovery.Injective

open import Data.Unit
open import Data.Empty
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

mutual

  -- Environemnts.
  unlift-≈ᴱ : ∀ {Γ Γ' θ₁ θ₂ θ₁' θ₂' pc β} {{c₁ c₂ : MkCtx Γ Γ'}} →
              pc ⊑ A →
              θ₁' F.≈⟨ β ⟩ᴱ θ₂' →
              CEqᴱ pc c₁ θ₁ θ₁' →
              CEqᴱ pc c₂ θ₂ θ₂' →
              θ₁ C.≈⟨ β ⟩ᴱ θ₂
  unlift-≈ᴱ pc⊑A F.[] [] [] = []
  unlift-≈ᴱ pc⊑A (v₁≈v₂ F.∷ θ₁≈θ₂) (v₁↓ ∷ θ₁↓) (v₂↓ ∷ θ₂↓) = unlift-≈ⱽ pc⊑A v₁≈v₂ v₁↓ v₂↓ ∷ unlift-≈ᴱ pc⊑A θ₁≈θ₂ θ₁↓ θ₂↓

  -- Values.
  unlift-≈ⱽ : ∀ {pc τ τ' v₁ v₂ v₁' v₂' β} {{p₁ p₂ : MkTy τ τ'}} →
                pc ⊑ A →
                v₁' F.≈⟨ β ⟩ⱽ v₂' →
                CEqⱽ pc p₁ v₁ v₁' →
                CEqⱽ pc p₂ v₂ v₂' →
                v₁ C.≈⟨ β ⟩ⱽ v₂
  unlift-≈ⱽ pc⊑A (F.Valueᴸ ℓ⊑A r≈) (_ ↓ r₁↓) (_ ↓ r₂↓) = unlift-≈ᴿ pc⊑A r≈ r₁↓ r₂↓
  unlift-≈ⱽ pc⊑A (F.Valueᴴ ℓ₁⋤A ℓ₂⋤A) (ℓ₁⊑pc ↓ _) (ℓ₂⊑pc ↓ _) = ⊥-elim (ℓ₁⋤A (trans-⊑ ℓ₁⊑pc pc⊑A))

  -- Raw values.
  unlift-≈ᴿ : ∀ {pc τ τ' v₁ v₂ r₁ r₂ β} {{p₁ p₂ : MkTy τ τ'}} →
                pc ⊑ A →
                r₁ F.≈⟨ β ⟩ᴿ r₂ →
                CEqᴿ pc p₁ v₁ r₁ →
                CEqᴿ pc p₂ v₂ r₂ →
                v₁ C.≈⟨ β ⟩ⱽ v₂
  unlift-≈ᴿ pc⊑A F.Unit （） （） = Unit
  unlift-≈ᴿ pc⊑A (F.Lbl ℓ) ⌞ .ℓ ⌟ ⌞ .ℓ ⌟ = Lbl ℓ
  unlift-≈ᴿ pc⊑A (F.Inl x) (Inl y) (Inl z) = Inl (unlift-≈ⱽ pc⊑A x y z )
  unlift-≈ᴿ pc⊑A (F.Inr x) (Inr y) (Inr z) = Inr (unlift-≈ⱽ pc⊑A x y z )
  unlift-≈ᴿ pc⊑A (F.Pair x₁ x₂) (Pair y₁ y₂) (Pair z₁ z₂) = Pair (unlift-≈ⱽ pc⊑A x₁ y₁ z₁) (unlift-≈ⱽ pc⊑A x₂ y₂ z₂)
  unlift-≈ᴿ pc⊑A (F.Fun θ≈) (Fun {{c = c₁}} y θ₁↓) (Fun {{c = c₂}} z θ₂↓) with inj-MkCtx c₁ c₂
  ... | refl rewrite inj-⟦·⟧ᴱ y z = Fun (unlift-≈ᴱ pc⊑A θ≈ θ₁↓ θ₂↓)
  unlift-≈ᴿ pc⊑A (F.Fun θ≈) (Thunk′ {{c = c₁}} y θ₁↓) (Thunk′ {{c = c₂}} z θ₂↓) with inj-MkCtx c₁ c₂
  ... | refl rewrite inj-⟦·⟧ᵀ y z = Thunk′ (unlift-≈ᴱ pc⊑A θ≈ θ₁↓ θ₂↓)
  unlift-≈ᴿ pc⊑A (F.Ref-Iᴸ ℓ⊑A) (Refᴵ ℓ ._) (Refᴵ .ℓ ._) = Ref-Iᴸ ℓ⊑A _
  unlift-≈ᴿ pc⊑A (F.Ref-Iᴴ ℓ₁⋤A ℓ₂⋤A) (Refᴵ ℓ n) (Refᴵ ℓ₁ n₁) = Ref-Iᴴ ℓ₁⋤A ℓ₂⋤A
  unlift-≈ᴿ pc⊑A (F.Ref-S ∈₁) (Refˢ ._) (Refˢ ._) = Ref-S ∈₁
  unlift-≈ᴿ pc⊑A (F.Id (F.Valueᴸ ℓ⊑A (F.Pair (F.Valueᴸ ℓ₁⊑A r≈) r₁≈r₂))) (Labeled _ r₁↓) (Labeled _ r₂↓)
    = Labeledᴸ ℓ₁⊑A (unlift-≈ⱽ ℓ₁⊑A r₁≈r₂ r₁↓ r₂↓)
  unlift-≈ᴿ pc⊑A (F.Id (F.Valueᴸ ℓ⊑A (F.Pair (F.Valueᴴ ℓ₁⋤A ℓ₂⋤A) x₅))) (Labeled x₁ x₂) (Labeled x₃ x₄) = Labeledᴴ ℓ₁⋤A ℓ₂⋤A
  unlift-≈ᴿ pc⊑A (F.Id (F.Valueᴴ ℓ₁⋤A ℓ₂⋤A)) (Labeled x₁ x₂) (Labeled x₃ x₄) = ⊥-elim (ℓ₂⋤A (trans-⊑ x₃ pc⊑A))

import Generic.Memory.LowEq {FG.Ty} {FG.Value} F._≈⟨_⟩ⱽ_ as FM
import Generic.Memory.LowEq {CG.Ty} {CG.Value} C._≈⟨_⟩ⱽ_ as CM

-- Public memories.
unlift-≈ᴹ : ∀ {ℓ β} {M₁' M₂'} {M₁ M₂ : FG.Memory ℓ} → ℓ ⊑ A →
                  M₁ F.≈⟨ β ⟩ᴹ M₂ → M₁ ↓≈ᴹ M₁' → M₂ ↓≈ᴹ M₂' → M₁' C.≈⟨ β ⟩ᴹ M₂'
unlift-≈ᴹ ℓ⊑A FM.[] nilᴹ nilᴹ = CM.[]
unlift-≈ᴹ ℓ⊑A (r₁≈r₂ FM.∷ M₁≈M₂) (consᴹ p₁ r₁↓  M₁↓) (consᴹ p₂ r₂↓ M₂↓) with inj-⟦·⟧ᵗ′ p₁ p₂
... | refl = unlift-≈ᴿ {{p₁}} {{p₂}} ℓ⊑A r₁≈r₂ r₁↓ r₂↓ CM.∷ unlift-≈ᴹ ℓ⊑A M₁≈M₂ M₁↓ M₂↓

-- Memories.
unlift-≈⟨_⟩ᴹ : ∀ {ℓ β} {M₁' M₂'} {M₁ M₂ : FG.Memory ℓ} →
                 (x : Dec (ℓ ⊑ A)) →
                 M₁ F.≈⟨ β , x ⟩ᴹ M₂ →
                 M₁ ↓≈ᴹ M₁' →
                 M₂ ↓≈ᴹ M₂' →
                 M₁' C.≈⟨ β , x ⟩ᴹ M₂'
unlift-≈⟨ yes p ⟩ᴹ M₁≈M₂ M₁↓ M₂↓ = unlift-≈ᴹ p M₁≈M₂ M₁↓ M₂↓
unlift-≈⟨ no ¬p ⟩ᴹ M₁≈M₂ M₁↓ M₂↓ = tt

-- Stores
unlift-≈ˢ : ∀ {Σ₁ Σ₂ Σ₁' Σ₂' β} →
               Σ₁ F.≈⟨ β ⟩ˢ Σ₂ →
               Σ₁ ↓≈ˢ Σ₁' →
               Σ₂ ↓≈ˢ Σ₂' →
               Σ₁' C.≈⟨ β ⟩ˢ Σ₂'
unlift-≈ˢ Σ₁≈Σ₂ Σ₁↓ Σ₂↓ = λ ℓ → unlift-≈⟨ ℓ ⊑? A ⟩ᴹ (Σ₁≈Σ₂ ℓ) (Σ₁↓ ℓ) (Σ₂↓ ℓ)

unlift-≈ᴸ : ∀ {τ τ' v₁ v₂ v₁′ v₂′ β} {{p₁ p₂ : MkTy τ τ'}} →
                v₁′ F.≈⟨ β ⟩ⱽ v₂′ →
                CEqᴸ p₁ v₁ v₁′ →
                CEqᴸ p₂ v₂ v₂′ →
                v₁ C.≈⟨ β ⟩ᴸ v₂
unlift-≈ᴸ (F.Valueᴸ ℓ⊑A r≈) ⌞ r₁↓ ⌟ᴸ ⌞ r₂↓ ⌟ᴸ = Labeledᴸ ℓ⊑A (unlift-≈ᴿ ℓ⊑A r≈ r₁↓ r₂↓)
unlift-≈ᴸ (F.Valueᴴ ℓ₁⋤A ℓ₂⋤A) ⌞ r₁↓ ⌟ᴸ ⌞ r₂↓ ⌟ᴸ = Labeledᴴ ℓ₁⋤A ℓ₂⋤A

unlift-≈ᴴ : ∀ {μ₁ μ₂ μ₁' μ₂' β} →
               μ₁ F.≈⟨ β ⟩ᴴ μ₂ →
               μ₁ ↓≈ᴴ μ₁' →
               μ₂ ↓≈ᴴ μ₂' →
               μ₁' C.≈⟨ β ⟩ᴴ μ₂'
unlift-≈ᴴ {μ₁} {μ₂} {μ₁'} {μ₂'} {β}  μ₁≈μ₂ μ₁↓ μ₂↓
  = record { dom-⊆ = unlift-dom-⊆ ; rng-⊆ = unlift-rng-⊆ ; lift-≅ = unlift-lift-≅ }
  where open F._≈⟨_⟩ᴴ_ μ₁≈μ₂
        open import Generic.Heap.Lemmas CG.Ty CG.LValue as HC
        open import Generic.Heap.Lemmas FG.Ty FG.Value as HF
        open import Generic.Value.HLowEq {CG.Ty} {CG.LValue} C._≈⟨_⟩ᴸ_ as CH
        open import Generic.Value.HLowEq {FG.Ty} {FG.Value} F._≈⟨_⟩ⱽ_ as FH
        open import Data.Product

        unlift-dom-⊆ : β ⊆ᴰ μ₁'
        unlift-dom-⊆ ∈₁ with HF.∈-< (dom-⊆ ∈₁)
        ... | ≤₁ rewrite ∥ μ₁↓ ∥-↓≈ᴴ = HC.<-∈ ≤₁

        unlift-rng-⊆ : β ⊆ᴿ μ₂'
        unlift-rng-⊆ ∈₁ with HF.∈-< (rng-⊆ ∈₁)
        ... | ≤₁ rewrite ∥ μ₂↓ ∥-↓≈ᴴ = HC.<-∈ ≤₁

        unlift-lift-≅ : Lift-≅ μ₁' μ₂' β
        unlift-lift-≅ {τ₁ = τ₁} {τ₂} ∈ᴮ ∈₁ ∈₂ with lookup-↓≈ᴴ ∈₁ μ₁↓ | lookup-↓≈ᴴ ∈₂ μ₂↓
        ... | v₁ , ∈₁′ , v₁↓ | v₂ , ∈₂′ , v₂↓ with lift-≅ ∈ᴮ ∈₁′ ∈₂′
        ... | ≅v with FH.≅ⱽ-type-≡ ≅v
        ... | eq with inj-⟦_⟧ᵗ {τ = τ₁} {τ' = τ₂} eq
        unlift-lift-≅ {τ₁ = τ₁} {.τ₁} ∈ᴮ ∈₁ ∈₂ | v₁ , ∈₁′ , v₁↓ | v₂ , ∈₂′ , v₂↓ | FH.⌞ ≈v ⌟ | refl | refl
          = CH.⌞ unlift-≈ᴸ ≈v v₁↓ v₂↓ ⌟

unlift-≈ᴾ : ∀ {P₁ P₂ P₁' P₂' β} →
               P₁ F.≈⟨ β ⟩ᴾ P₂ →
               P₁ ↓≈ᴾ P₁' →
               P₂ ↓≈ᴾ P₂' →
               P₁' C.≈⟨ β ⟩ᴾ P₂'
unlift-≈ᴾ ⟨ Σ₁≈Σ₂ , μ₁≈μ₂ ⟩ ⟨ Σ₁↓ , μ₁↓ ⟩ ⟨ Σ₂↓ , μ₂↓ ⟩ = ⟨ unlift-≈ˢ Σ₁≈Σ₂ Σ₁↓ Σ₂↓ , unlift-≈ᴴ μ₁≈μ₂ μ₁↓ μ₂↓ ⟩

-- Final configurations.
unlift-≈ᶜ : ∀ {τ τ' β} {c₁' c₂' : CG.FConf τ} {c₁ c₂ : FG.FConf τ'} →
              c₁ F.≈⟨ β ⟩ᶜ c₂ →
              c₁ ↓≈ᶜ c₁' →
              c₂ ↓≈ᶜ c₂' →
              c₁' C.≈⟨ β ⟩ᶜ c₂'
unlift-≈ᶜ F.⟨ P₁≈P₂ , F.Valueᴸ ℓ⊑A r≈ ⟩ ⟨ P₁↓P₁' , v₁↓v₁' ⟩ ⟨ P₂↓P₂' , v₂↓v₂' ⟩ = pcᴸ P₁'≈P₂' ℓ⊑A v₁'≈v₂'
  where P₁'≈P₂' = unlift-≈ᴾ P₁≈P₂ P₁↓P₁' P₂↓P₂'
        v₁'≈v₂' = unlift-≈ⱽ ℓ⊑A (F.Valueᴸ ℓ⊑A r≈) (refl-⊑ ↓ v₁↓v₁') (refl-⊑ ↓ v₂↓v₂')
unlift-≈ᶜ F.⟨ P₁≈P₂ , F.Valueᴴ ℓ₁⋤A ℓ₂⋤A ⟩ ⟨ P₁↓P₁' , v₁↓v₁' ⟩ ⟨ P₂↓P₂' , v₂↓v₂' ⟩ = pcᴴ P₁'≈P₂' ℓ₁⋤A ℓ₂⋤A
  where P₁'≈P₂' = unlift-≈ᴾ P₁≈P₂ P₁↓P₁' P₂↓P₂'
