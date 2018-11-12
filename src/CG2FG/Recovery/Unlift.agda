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
  unlift-≈ᴱ : ∀ {Γ Γ' θ₁ θ₂ θ₁' θ₂' pc} {{c₁ c₂ : MkCtx Γ Γ'}} →
              pc ⊑ A →
              θ₁' F.≈ᴱ θ₂' →
              CEqᴱ pc c₁ θ₁ θ₁' →
              CEqᴱ pc c₂ θ₂ θ₂' →
              θ₁ C.≈ᴱ θ₂
  unlift-≈ᴱ pc⊑A F.[] [] [] = []
  unlift-≈ᴱ pc⊑A (v₁≈v₂ F.∷ θ₁≈θ₂) (v₁↓ ∷ θ₁↓) (v₂↓ ∷ θ₂↓) = unlift-≈ⱽ pc⊑A v₁≈v₂ v₁↓ v₂↓ ∷ unlift-≈ᴱ pc⊑A θ₁≈θ₂ θ₁↓ θ₂↓

  -- Values.
  unlift-≈ⱽ : ∀ {pc τ τ' v₁ v₂ v₁' v₂'} {{p₁ p₂ : MkTy τ τ'}} →
                pc ⊑ A →
                v₁' F.≈ⱽ v₂' →
                CEqⱽ pc p₁ v₁ v₁' →
                CEqⱽ pc p₂ v₂ v₂' →
                v₁ C.≈ⱽ v₂
  unlift-≈ⱽ pc⊑A (F.Valueᴸ ℓ⊑A r≈) (_ ↓ r₁↓) (_ ↓ r₂↓) = unlift-≈ᴿ pc⊑A r≈ r₁↓ r₂↓
  unlift-≈ⱽ pc⊑A (F.Valueᴴ ℓ₁⋤A ℓ₂⋤A) (ℓ₁⊑pc ↓ _) (ℓ₂⊑pc ↓ _) = ⊥-elim (ℓ₁⋤A (trans-⊑ ℓ₁⊑pc pc⊑A))

  -- Raw values.
  unlift-≈ᴿ : ∀ {pc τ τ' v₁ v₂ r₁ r₂} {{p₁ p₂ : MkTy τ τ'}} →
                pc ⊑ A →
                r₁ F.≈ᴿ r₂ →
                CEqᴿ pc p₁ v₁ r₁ →
                CEqᴿ pc p₂ v₂ r₂ →
                v₁ C.≈ⱽ v₂
  unlift-≈ᴿ pc⊑A F.Unit （） （） = Unit
  unlift-≈ᴿ pc⊑A (F.Lbl ℓ) ⌞ .ℓ ⌟ ⌞ .ℓ ⌟ = Lbl ℓ
  unlift-≈ᴿ pc⊑A (F.Inl x) (Inl y) (Inl z) = Inl (unlift-≈ⱽ pc⊑A x y z )
  unlift-≈ᴿ pc⊑A (F.Inr x) (Inr y) (Inr z) = Inr (unlift-≈ⱽ pc⊑A x y z )
  unlift-≈ᴿ pc⊑A (F.Pair x₁ x₂) (Pair y₁ y₂) (Pair z₁ z₂) = Pair (unlift-≈ⱽ pc⊑A x₁ y₁ z₁) (unlift-≈ⱽ pc⊑A x₂ y₂ z₂)
  unlift-≈ᴿ pc⊑A (F.Fun θ≈) (Fun {{c = c₁}} y θ₁↓) (Fun {{c = c₂}} z θ₂↓) with inj-MkCtx c₁ c₂
  ... | refl rewrite inj-⟦·⟧ᴱ y z = Fun (unlift-≈ᴱ pc⊑A θ≈ θ₁↓ θ₂↓)
  unlift-≈ᴿ pc⊑A (F.Fun θ≈) (Thunk′ {{c = c₁}} y θ₁↓) (Thunk′ {{c = c₂}} z θ₂↓) with inj-MkCtx c₁ c₂
  ... | refl rewrite inj-⟦·⟧ᵀ y z = Thunk′ (unlift-≈ᴱ pc⊑A θ≈ θ₁↓ θ₂↓)
  unlift-≈ᴿ pc⊑A (F.Refᴸ ℓ⊑A n) (Ref ℓ .n) (Ref .ℓ .n) = Refᴸ ℓ⊑A n
  unlift-≈ᴿ pc⊑A (F.Refᴴ ℓ₁⋤A ℓ₂⋤A) (Ref ℓ n) (Ref ℓ₁ n₁) = Refᴴ ℓ₁⋤A ℓ₂⋤A
  unlift-≈ᴿ pc⊑A (F.Id (F.Valueᴸ ℓ⊑A (F.Pair (F.Valueᴸ ℓ₁⊑A r≈) r₁≈r₂))) (Labeled _ r₁↓) (Labeled _ r₂↓)
    = Labeledᴸ ℓ₁⊑A (unlift-≈ⱽ ℓ₁⊑A r₁≈r₂ r₁↓ r₂↓)
  unlift-≈ᴿ pc⊑A (F.Id (F.Valueᴸ ℓ⊑A (F.Pair (F.Valueᴴ ℓ₁⋤A ℓ₂⋤A) x₅))) (Labeled x₁ x₂) (Labeled x₃ x₄) = Labeledᴴ ℓ₁⋤A ℓ₂⋤A
  unlift-≈ᴿ pc⊑A (F.Id (F.Valueᴴ ℓ₁⋤A ℓ₂⋤A)) (Labeled x₁ x₂) (Labeled x₃ x₄) = ⊥-elim (ℓ₂⋤A (trans-⊑ x₃ pc⊑A))

-- Public memories.
unlift-≈ᴹ : ∀ {ℓ} {M₁' M₂'} {M₁ M₂ : FG.Memory ℓ} → ℓ ⊑ A → M₁ F.≈ᴹ M₂ → M₁ ↓≈ᴹ M₁' → M₂ ↓≈ᴹ M₂' → M₁' C.≈ᴹ M₂'
unlift-≈ᴹ ℓ⊑A F.[] [] [] = C.[]
unlift-≈ᴹ ℓ⊑A (r₁≈r₂ ∷ M₁≈M₂) (_∷_ {{p = p₁}} r₁↓  M₁↓) (_∷_ {{p = p₂}} r₂↓  M₂↓) with inj-⟦·⟧ᵗ′ p₁ p₂
... | refl = unlift-≈ᴿ ℓ⊑A r₁≈r₂ r₁↓ r₂↓ ∷ unlift-≈ᴹ ℓ⊑A M₁≈M₂ M₁↓ M₂↓

-- Memories.
unlift-≈⟨_⟩ᴹ : ∀ {ℓ} {M₁' M₂'} {M₁ M₂ : FG.Memory ℓ} →
                 (x : Dec (ℓ ⊑ A)) →
                 M₁ F.≈⟨ x ⟩ᴹ M₂ →
                 M₁ ↓≈ᴹ M₁' →
                 M₂ ↓≈ᴹ M₂' →
                 M₁' C.≈⟨ x ⟩ᴹ M₂'
unlift-≈⟨ yes p ⟩ᴹ M₁≈M₂ M₁↓ M₂↓ = unlift-≈ᴹ p M₁≈M₂ M₁↓ M₂↓
unlift-≈⟨ no ¬p ⟩ᴹ M₁≈M₂ M₁↓ M₂↓ = tt

-- Stores
unlift-≈ˢ : ∀ {Σ₁ Σ₂ Σ₁' Σ₂'} →
               Σ₁ F.≈ˢ Σ₂ →
               Σ₁ ↓≈ˢ Σ₁' →
               Σ₂ ↓≈ˢ Σ₂' →
               Σ₁' C.≈ˢ Σ₂'
unlift-≈ˢ Σ₁≈Σ₂ Σ₁↓ Σ₂↓ = λ ℓ → unlift-≈⟨ ℓ ⊑? A ⟩ᴹ (Σ₁≈Σ₂ ℓ) (Σ₁↓ ℓ) (Σ₂↓ ℓ)

-- Final configurations.
unlift-≈ᶜ : ∀ {τ τ'} {c₁' c₂' : CG.FConf τ} {c₁ c₂ : FG.FConf τ'} →
              c₁ F.≈ᶜ c₂ →
              c₁ ↓≈ᶜ c₁' →
              c₂ ↓≈ᶜ c₂' →
              c₁' C.≈ᶜ c₂'
unlift-≈ᶜ F.⟨ Σ₁≈Σ₂ , F.Valueᴸ ℓ⊑A r≈ ⟩ ⟨ Σ₁↓Σ₁' , v₁↓v₁' ⟩ ⟨ Σ₂↓Σ₂' , v₂↓v₂' ⟩ = pcᴸ Σ₁'≈Σ₂' ℓ⊑A v₁'≈v₂'
  where Σ₁'≈Σ₂' = unlift-≈ˢ Σ₁≈Σ₂ Σ₁↓Σ₁' Σ₂↓Σ₂'
        v₁'≈v₂' = unlift-≈ⱽ ℓ⊑A (F.Valueᴸ ℓ⊑A r≈) (refl-⊑ ↓ v₁↓v₁') (refl-⊑ ↓ v₂↓v₂')
unlift-≈ᶜ F.⟨ Σ₁≈Σ₂ , F.Valueᴴ ℓ₁⋤A ℓ₂⋤A ⟩ ⟨ Σ₁↓Σ₁' , v₁↓v₁' ⟩ ⟨ Σ₂↓Σ₂' , v₂↓v₂' ⟩ = pcᴴ Σ₁'≈Σ₂' ℓ₁⋤A ℓ₂⋤A
  where Σ₁'≈Σ₂' = unlift-≈ˢ Σ₁≈Σ₂ Σ₁↓Σ₁' Σ₂↓Σ₂'
