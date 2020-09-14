-- CG L-equivalence (≈) of source terms implies FG L-equivalence of
-- the target (translated) terms.

open import Lattice

module CG2FG.Recovery.Lift {{𝑳 : Lattice}} (A : Label) where

open import CG as CG
open import FG as FG
open import CG.LowEq A as C
open import FG.LowEq A as F
open import CG2FG.Syntax
open import CG2FG.CrossEq using (𝑽ᴸ ; ⌞_⌟ᴸ)
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



lift-≈ᴴ : ∀ {μ₁ μ₂ β} → μ₁ C.≈⟨ β ⟩ᴴ μ₂ → ⟦ μ₁ ⟧ᴴ F.≈⟨ β ⟩ᴴ ⟦ μ₂ ⟧ᴴ
lift-≈ᴴ {μ₁} {μ₂} {β} ≈ᴴ = record { dom-⊆ = lift-dom-⊆ ; rng-⊆ = lift-rng-⊆ ; lift-≅ = lift-lift-≅ }
  where open C._≈⟨_⟩ᴴ_ ≈ᴴ
        open import Generic.Heap.Lemmas CG.Ty CG.LValue as HC
        open import Generic.Heap.Lemmas FG.Ty FG.Value as HF
        open import Generic.Value.HLowEq {CG.Ty} {CG.LValue} C._≈⟨_⟩ᴸ_ as CH
        open import Generic.Value.HLowEq {FG.Ty} {FG.Value} F._≈⟨_⟩ⱽ_ as FH
        open import Data.Product
--        open import Generic.Heap.Convert ? ? renaming (⟪_⟫∈ᴴ to ⟦_⟧∈ᴴ)

        --------------------------------------------------------------------------------
--        open import
        -- Needed?
        -- open import CG2FG.Graph
        -- open import CG2FG.Graph.Types
        -- open import Generic.Heap.Graph Graph-⟦·⟧ᵗ {!Graph-⟦·⟧ⱽ!} -- Graph-⟪·⟫ᵗ′ ? -- Graph-⟪·⟫ᴸ
--        open import Generic.Memory.Graph {!!}  {!!} -- Graph-⟪·⟫ᴿ

        lift-dom-⊆ : β F.⊆ᴰ ⟦ μ₁ ⟧ᴴ
        lift-dom-⊆ ∈₁ with HC.∈-< (dom-⊆ ∈₁)
        ... | ≤₁ rewrite sym (∥ μ₁ ∥-≡ᴴ) = HF.<-∈ ≤₁

        lift-rng-⊆ : β F.⊆ᴿ ⟦ μ₂ ⟧ᴴ
        lift-rng-⊆ ∈₁ with HC.∈-< (rng-⊆ ∈₁)
        ... | ≤₁ rewrite sym (∥ μ₂ ∥-≡ᴴ) = HF.<-∈ ≤₁

        lift-lift-≅ : F.Lift-≅ ⟦ μ₁ ⟧ᴴ ⟦ μ₂ ⟧ᴴ β
        lift-lift-≅ ∈ᴮ ∈₁ ∈₂ with unlift-⟦ ∈₁ ⟧∈ᴴ (refl-↓≈ᴴ μ₁) | unlift-⟦ ∈₂ ⟧∈ᴴ (refl-↓≈ᴴ μ₂)
        ... | τ₁ , (τ₁↓ , v₁) , ∈₁′ , v₁↓ | τ₂ , (τ₂↓ , v₂) , ∈₂′ , v₂↓ with lift-≅ ∈ᴮ ∈₁′ ∈₂′
        ... | ≅v with CH.≅ⱽ-type-≡ ≅v
        lift-lift-≅ ∈ᴮ ∈₁ ∈₂ | τ₁ , (τ₁↓ , v₁) , ∈₁′ , v₁↓ | .τ₁ , (τ₂↓ , v₂) , ∈₂′ , v₂↓ | CH.⌞ ≈v ⌟ | refl
          with trans (≡-MkTy τ₁↓) (sym (≡-MkTy τ₂↓))
        lift-lift-≅ ∈ᴮ ∈₁ ∈₂ | τ₁ , (τ₁↓ , v₁) , ∈₁′ , ⌞ r₁↓ ⌟ᴸ | .τ₁ , (τ₂↓ , v₂) , ∈₂′ , ⌞ r₂↓ ⌟ᴸ
          | ⌞ Labeledᴸ ⊑A r≈ ⌟ | refl | refl = FH.⌞ {!unlift-≈ᴿ ⊑A (lift-≈ᴿ ⊑A r≈) r₁↓ r₂↓  !} ⌟
        lift-lift-≅ ∈ᴮ ∈₁ ∈₂ | τ₁ , (τ₁↓ , v₁) , ∈₁′ , ⌞ r₁↓ ⌟ᴸ | .τ₁ , (τ₂↓ , v₂) , ∈₂′ , ⌞ r₂↓ ⌟ᴸ
          | ⌞ Labeledᴴ ⋤₁ ⋤₂ ⌟ | refl | refl = FH.⌞ {!≈ᴴ!} ⌟

-- with inj-⟦_⟧ᵗ {τ = τ₁} {τ' = τ₂} eq
--         ... | eq' = {!!}

 -- unlift-⟪ ∈₁ ⟫∈ᴴ | unlift-⟪ ∈₂ ⟫∈ᴴ
 --        ... | τ₁′ , v₁′ , ∈₁′ , refl , refl | τ₂′ , v₂′ , ∈₂′ , refl , refl
 --        ... | C.⌞ v≈ ⌟ = FH.⌞ lift-≈ⱽ v≈  ⌟

lift-≈ᴾ : ∀ {P₁ P₂ β} → P₁ C.≈⟨ β ⟩ᴾ P₂ → ⟦ P₁ ⟧ᴾ F.≈⟨ β ⟩ᴾ ⟦ P₂ ⟧ᴾ
lift-≈ᴾ C.⟨ ≈ˢ , ≈ᴴ ⟩ = F.⟨ lift-≈ˢ ≈ˢ , lift-≈ᴴ ≈ᴴ ⟩

-- Initial configurations.
lift-≈ᴵ : ∀ {τ Γ β} {c₁ c₂ : EConf Γ (LIO τ)} → c₁ C.≈⟨ β ⟩ᴵ c₂ → ⟦ c₁ ⟧ᴵ F.≈⟨ β ⟩ᴵ ⟦ c₂ ⟧ᴵ
lift-≈ᴵ ⟨ P₁≈P₂ , refl , refl ⟩ = ⟨ lift-≈ᴾ P₁≈P₂  , refl ⟩
