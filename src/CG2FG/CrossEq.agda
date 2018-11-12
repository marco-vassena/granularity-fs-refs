-- This module defines the cross-language logical relation v₁ ↓≈⟨ pc ⟩
-- v₂ between FG value v₁ and CG value v₂ such that v₁ and v₂ are
-- semantically the same value except that v₁ contains extra label
-- annotations at most at security level pc.

open import Lattice

module CG2FG.CrossEq {{𝑳 : Lattice}} where

open import FG as F hiding (_×_)
open import CG as C hiding (_↑¹ ; _×_)
open import CG2FG.Syntax
open import CG2FG.Graph

mutual

  -- Values.
  data CEqⱽ {τ τ'} (pc : Label) (p : MkTy τ τ') (v : C.Value τ) : F.Value τ' → Set where
    _↓_ : ∀ {ℓ r} → ℓ ⊑ pc → CEqᴿ pc p v r → CEqⱽ pc p v (r ^ ℓ)

  -- Raw values.
  data CEqᴿ (pc : Label) : ∀ {τ τ'} → MkTy τ τ' → C.Value τ → F.Raw τ' → Set where

     ⌞_⌟ : ∀ ℓ → CEqᴿ pc 𝓛 ⌞ ℓ ⌟ ⌞ ℓ ⌟

     （） : CEqᴿ pc Unit （） （）

     Ref : ∀ {τ τ'} {{p : MkTy τ τ'}} ℓ n → CEqᴿ pc (Ref p) (Ref ℓ n) (Ref ℓ n)

     Fun : ∀ {τ₁ τ₁' τ₂ τ₂' Γ Γ' θ θ' e e'} {{p₁ : MkTy τ₁ τ₁'}} {{p₂ : MkTy τ₂ τ₂'}} {{c : MkCtx Γ Γ'}} →
           Cg2Fgᴱ (p₁ ∷ c) p₂ e e' →
           CEqᵉ pc c θ θ' →
           CEqᴿ pc (Fun p₁ p₂) ⟨ e , θ ⟩ᶜ ⟨ e' , θ' ⟩ᶜ

     Thunk′ : ∀ {τ τ' Γ Γ' θ θ' t e} {{p : MkTy τ τ'}} {{c : MkCtx Γ Γ'}} →
                Cg2Fgᵀ c p t e →
                CEqᵉ pc c θ θ' →
                CEqᴿ pc (LIO p) ⟨ t , θ ⟩ᵀ ⟨ e ↑¹ , θ' ⟩ᶜ

     Pair : ∀ {τ₁ τ₂ τ₁' τ₂' v₁ v₁' v₂ v₂'} {{p₁ : MkTy τ₁ τ₁'}} {{p₂ : MkTy τ₂ τ₂'}} →
              CEqⱽ pc p₁ v₁ v₁' →
              CEqⱽ pc p₂ v₂ v₂' →
              CEqᴿ pc (Prod p₁ p₂) ⟨ v₁ , v₂ ⟩ ⟨ v₁' , v₂' ⟩

     Inl : ∀ {τ₁ τ₂ τ₁' τ₂' v₁ v₁'} {{p₁ : MkTy τ₁ τ₁'}} {{p₂ : MkTy τ₂ τ₂'}} →
             CEqⱽ pc p₁ v₁ v₁' →
             CEqᴿ pc (Sum p₁ p₂) (inl v₁) (inl v₁')

     Inr : ∀ {τ₁ τ₂ τ₁' τ₂' v₂ v₂'} {{p₁ : MkTy τ₁ τ₁'}} {{p₂ : MkTy τ₂ τ₂'}} →
             CEqⱽ pc p₂ v₂ v₂' →
             CEqᴿ pc (Sum p₁ p₂) (inr v₂) (inr v₂')


     Labeled : ∀ {τ τ' ℓ ℓ' v v'} {{p : MkTy τ τ'}} →
                 ℓ' ⊑ pc →
                 CEqⱽ ℓ p v v' →
                 CEqᴿ pc (Labeled p) (Labeled ℓ v) (Id (⟨ ⌞ ℓ ⌟ ^ ℓ , v' ⟩ ^ ℓ'))

  -- Environments.
  data CEqᵉ (pc : Label) : ∀ {Γ Γ'} → MkCtx Γ Γ' → C.Env Γ → F.Env Γ' → Set where
    [] : CEqᵉ pc [] [] []
    _∷_ : ∀ {τ τ' Γ Γ' v v' θ θ'} {{p : MkTy τ τ'}} {{c : MkCtx Γ Γ'}} →
            CEqⱽ pc p v v' →
            CEqᵉ pc c θ θ' →
            CEqᵉ pc (p ∷ c) (v ∷ θ ) (v' ∷ θ')

trueᴿ : ∀ {pc} → CEqᴿ pc (Sum Unit Unit) C.true (F.true pc)
trueᴿ = Inl (refl-⊑ ↓ （）)

falseᴿ : ∀ {pc} → CEqᴿ pc (Sum Unit Unit) C.false (F.false pc)
falseᴿ = Inr (refl-⊑ ↓ （）)


--------------------------------------------------------------------------------
-- Pretty syntax.

-- Notice that this definition use instance arguments, e.g., {{p :
-- MkTy τ τ'}} to automatically infer that the types of the terms are
-- related. This proof is automatically found if one is in scope or if
-- τ' ≡ ⟦ τ ⟧ᵗ.

_↓≈⟨_⟩ᴿ_ : ∀ {τ τ'} {{p : MkTy τ τ'}} → F.Raw τ' → Label → C.Value τ → Set
_↓≈⟨_⟩ᴿ_ {{p}} r pc v = CEqᴿ pc p v r

⌞_⌟ᴿ  : ∀ {τ τ' r pc v} {p q : MkTy τ τ'} → CEqᴿ pc p v r → CEqᴿ pc q v r
⌞_⌟ᴿ {p = p} {q} x rewrite !-MkTy p q = x

_↓≈⟨_⟩ᵉ_ : ∀ {Γ Γ'} {{c : MkCtx Γ Γ'}} → F.Env Γ' → Label → C.Env Γ → Set
_↓≈⟨_⟩ᵉ_ {{c}} θ' pc θ = CEqᵉ pc c θ θ'

_↓≈⟨_⟩ⱽ_ : ∀ {τ τ'} {{c : MkTy τ τ'}} → F.Value τ' → Label → C.Value τ → Set
_↓≈⟨_⟩ⱽ_ {{c}} v' pc v = CEqⱽ pc c v v'

_↓≈ᴱ_ : ∀ {τ τ' Γ Γ'} {{p : MkTy τ τ'}} {{c : MkCtx Γ Γ'}} → F.Expr Γ' (Id unit ➔ τ') → C.Expr Γ (LIO τ) → Set
_↓≈ᴱ_ {{p}} {{c}} e e' = Cg2Fgᴱ c (LIO p) e' e

-- Memories.
data _↓≈ᴹ_ {ℓ} : F.Memory ℓ → C.Memory ℓ → Set where
  [] : F.[] ↓≈ᴹ C.[]
  _∷_ : ∀ {M M' τ τ'} {v : C.Value τ} {r : F.Raw τ'} {{p : MkTy τ τ'}} →
          r ↓≈⟨ ℓ ⟩ᴿ v →
          M ↓≈ᴹ M' →
          (r F.∷ M) ↓≈ᴹ (v C.∷ M')

-- Stores
_↓≈ˢ_ : F.Store → C.Store → Set
Σ ↓≈ˢ Σ' = ∀ (ℓ : Label) → (Σ ℓ) ↓≈ᴹ (Σ' ℓ)

infixr 2 _↓≈ˢ_

open F.Conf
open C.Conf

-- Initial configurations (Expr)
data _↓≈ᴵ_ {Γ τ} : F.IConf ⟦ Γ ⟧ᶜ ⟦ τ ⟧ᵗ → C.EConf Γ (LIO τ) → Set where
  ⌞_⌟ᴵ : ∀ {Σ pc Σ'} {e : C.Expr Γ (LIO τ)} → Σ ↓≈ˢ Σ' → ⟨ Σ , ⟦ e ⟧ᴱ ∘ (Id （）) ⟩ ↓≈ᴵ ⟨ Σ' , pc , e ⟩

⌜_⌝ᴵ : ∀ {Γ τ c₁} {c₂ : EConf Γ (LIO τ)} → c₁ ↓≈ᴵ c₂ → (store c₁) ↓≈ˢ (store c₂)
⌜_⌝ᴵ ⌞ Σ≈ ⌟ᴵ = Σ≈

-- Initial configurations (Thunk)
data _↓≈ᵀ_ {Γ τ} : F.IConf ⟦ Γ ⟧ᶜ ⟦ τ ⟧ᵗ → C.TConf Γ (LIO τ) → Set where
  ⌞_⌟ᵀ : ∀ {Σ pc Σ'} {t : C.Thunk Γ (LIO τ)} → Σ ↓≈ˢ Σ' → ⟨ Σ , ⟦ t ⟧ᵀ ⟩ ↓≈ᵀ ⟨ Σ' , pc , t ⟩

⌜_⌝ᵀ : ∀ {Γ τ c₁} {c₂ : TConf Γ (LIO τ)} → c₁ ↓≈ᵀ c₂ → (store c₁) ↓≈ˢ (store c₂)
⌜_⌝ᵀ ⌞ Σ≈ ⌟ᵀ = Σ≈

-- Final configurations.
data _↓≈ᶜ_ {τ τ'} : F.FConf τ' → C.FConf τ → Set where
  ⟨_,_⟩ : ∀ {Σ Σ' pc r v} {{p : MkTy τ τ'}} →  Σ ↓≈ˢ Σ' → r ↓≈⟨ pc ⟩ᴿ v → F.⟨ Σ , r ^ pc ⟩ ↓≈ᶜ ⟨ Σ' , pc , v ⟩

--------------------------------------------------------------------------------
-- Properties
-- Equivalence up to annotations is "reflexive" under value transformation.

mutual

  refl-≈⟨_⟩ⱽ_ : ∀ {τ} → (pc : Label) (v : C.Value τ) → ⟦ v ⟧ⱽ pc ↓≈⟨ pc ⟩ⱽ v
  refl-≈⟨ pc ⟩ⱽ v = refl-⊑ ↓ (refl-≈⟨ pc ⟩ᴿ v)

  refl-≈⟨_⟩ᴿ_ : ∀ {τ} → (pc : Label) (v : C.Value τ) → ⟦ v ⟧ᴿ pc ↓≈⟨ pc ⟩ᴿ v
  refl-≈⟨ pc ⟩ᴿ C.（）  = （）
  refl-≈⟨ pc ⟩ᴿ C.⟨ e , θ ⟩ᶜ  = Fun (mkCg2Fgᴱ e) (refl-≈⟨ pc ⟩ᵉ θ )
  refl-≈⟨ pc ⟩ᴿ C.⟨ t , θ ⟩ᵀ = Thunk′ (mkCg2Fgᵀ t) (refl-≈⟨ pc ⟩ᵉ θ) -- thunk (refl-≈⟨ pc ⟩ᵉ θ)
  refl-≈⟨ pc ⟩ᴿ (C.inl v) = Inl (refl-≈⟨ pc ⟩ⱽ v)
  refl-≈⟨ pc ⟩ᴿ (C.inr v) = Inr (refl-≈⟨ pc ⟩ⱽ v)
  refl-≈⟨ pc ⟩ᴿ C.⟨ v , v₁ ⟩ = Pair (refl-≈⟨ pc ⟩ⱽ v) (refl-≈⟨ pc ⟩ⱽ v₁)
  refl-≈⟨ pc ⟩ᴿ (C.Labeled ℓ v) = Labeled refl-⊑ (refl-≈⟨ ℓ ⟩ⱽ v)
  refl-≈⟨ pc ⟩ᴿ (C.Ref ℓ n) = Ref ℓ n
  refl-≈⟨ pc ⟩ᴿ C.⌞ ℓ ⌟ = ⌞ ℓ ⌟

  refl-≈⟨_⟩ᵉ_ : ∀ {Γ} → (pc : Label) (θ : C.Env Γ) → ⟦ θ ⟧ᵉ pc ↓≈⟨ pc ⟩ᵉ θ
  refl-≈⟨ _ ⟩ᵉ C.[] = []
  refl-≈⟨ pc ⟩ᵉ (v C.∷ θ) = refl-≈⟨ pc ⟩ⱽ v ∷ (refl-≈⟨ pc ⟩ᵉ θ)

refl-≈ᴹ : ∀ {ℓ} → (M : C.Memory ℓ) → ⟦ M ⟧ᴹ ↓≈ᴹ M
refl-≈ᴹ C.[] = []
refl-≈ᴹ (v C.∷ M) = (refl-≈⟨ _ ⟩ᴿ v) ∷ refl-≈ᴹ M

refl-≈ˢ : ∀ (Σ : C.Store) → ⟦ Σ ⟧ˢ ↓≈ˢ Σ
refl-≈ˢ Σ = λ ℓ → refl-≈ᴹ (Σ ℓ)

refl-≈ᴵ : ∀ {Γ τ} → (c : C.EConf Γ (LIO τ)) → ⟦ c ⟧ᴵ ↓≈ᴵ c
refl-≈ᴵ ⟨ Σ , pc , e ⟩ = ⌞ refl-≈ˢ Σ ⌟ᴵ

mutual

  -- Weakening. We can always increase the upper bound (pc) over the label  annotations.
  ≈ⱽ-⊑  : ∀ {τ τ' pc₁ pc₂} {v : C.Value τ} {v' : F.Value τ'} {{p : MkTy τ τ'}} → v' ↓≈⟨ pc₁ ⟩ⱽ v → pc₁ ⊑ pc₂ → v' ↓≈⟨ pc₂ ⟩ⱽ v
  ≈ⱽ-⊑ (p₁ ↓ r≈) p₂ = (trans-⊑ p₁ p₂) ↓ (≈ᴿ-⊑ r≈ p₂)

  ≈ᴿ-⊑ : ∀ {τ τ' pc₁ pc₂} {v : C.Value τ} {v' : F.Raw τ'} {{p : MkTy τ τ'}} → v' ↓≈⟨ pc₁ ⟩ᴿ v → pc₁ ⊑ pc₂ → v' ↓≈⟨ pc₂ ⟩ᴿ v
  ≈ᴿ-⊑ ⌞ ℓ ⌟ p = ⌞ ℓ ⌟
  ≈ᴿ-⊑ （） p = （）
  ≈ᴿ-⊑ (Ref ℓ n) p = Ref ℓ n
  ≈ᴿ-⊑ (Fun x₁ x₂) p = Fun x₁ (≈ᵉ-⊑ x₂ p)
  ≈ᴿ-⊑ (Thunk′ x₁ x₂) p = Thunk′ x₁ (≈ᵉ-⊑ x₂ p)
  ≈ᴿ-⊑ (Pair x₁ x₂) p = Pair (≈ⱽ-⊑ x₁ p) (≈ⱽ-⊑ x₂ p)
  ≈ᴿ-⊑ (Inl v≈) p = Inl (≈ⱽ-⊑ v≈ p)
  ≈ᴿ-⊑ (Inr v≈) p = Inr (≈ⱽ-⊑ v≈ p)
  ≈ᴿ-⊑ (Labeled pc⊑ℓ' v≈) p = Labeled (trans-⊑ pc⊑ℓ' p) v≈

  ≈ᵉ-⊑  : ∀ {Γ Γ' pc₁ pc₂} {θ : C.Env Γ} {θ' : F.Env Γ'} {{c : MkCtx Γ Γ'}} → θ' ↓≈⟨ pc₁ ⟩ᵉ θ → pc₁ ⊑ pc₂ → θ' ↓≈⟨ pc₂ ⟩ᵉ θ
  ≈ᵉ-⊑ [] p = []
  ≈ᵉ-⊑ (v≈ ∷ θ≈) p = ≈ⱽ-⊑ v≈ p ∷ ≈ᵉ-⊑ θ≈ p

--------------------------------------------------------------------------------
-- Lemmas about equivalent (↓≈) environments, memories and stores and
-- their operations.

open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Function
open import Data.Product

slice-↓≈ : ∀ {Γ Γ' pc} {θ₁ : F.Env ⟦ Γ ⟧ᶜ} {θ₂ : C.Env Γ} (p : Γ' C.⊆ Γ) → θ₁ ↓≈⟨ pc ⟩ᵉ θ₂  → F.slice θ₁ ⟦ p ⟧⊆ ↓≈⟨ pc ⟩ᵉ C.slice θ₂ p
slice-↓≈ C.base [] = []
slice-↓≈ (C.cons p) (x ∷ y) = x ∷ (slice-↓≈ p y)
slice-↓≈ (C.drop p) (x ∷ y) = slice-↓≈ p y

!!-↓≈ : ∀ {pc τ Γ θ₁} {θ₂ : C.Env Γ} → (τ∈Γ : τ C.∈ Γ) → θ₁ ↓≈⟨ pc ⟩ᵉ θ₂ → (θ₁ F.!! ⟦ τ∈Γ ⟧∈) ↓≈⟨ pc ⟩ⱽ (θ₂ C.!! τ∈Γ)
!!-↓≈ C.here (x ∷ θ₁≈θ₂) = x
!!-↓≈ (C.there τ∈Γ) (x ∷ θ₁≈θ₂) = !!-↓≈ τ∈Γ θ₁≈θ₂

-- Updating related stores with related memory gives related stores
update-≈ˢ : ∀ {ℓ Σ Σ'} {M : F.Memory ℓ} {M' : C.Memory ℓ} → Σ ↓≈ˢ Σ' → M ↓≈ᴹ M' → (Σ F.[ ℓ ↦ M ]ˢ) ↓≈ˢ (Σ' C.[ ℓ ↦ M' ]ˢ)
update-≈ˢ {ℓ} Σ≈ M≈ ℓ' with ℓ ≟ ℓ'
... | yes refl = M≈
... | no ℓ≢ℓ' = Σ≈ ℓ'

-- Extending related memories with related values gives related memoryes.
new-≈ᴹ : ∀ {ℓ τ} {M : F.Memory ℓ} {M' : C.Memory ℓ} {v : C.Value τ} {r : F.Raw ⟦ τ ⟧ᵗ} →
           M ↓≈ᴹ M' →
           r ↓≈⟨ ℓ ⟩ᴿ v →
           (M F.∷ᴿ r) ↓≈ᴹ (M' C.∷ᴿ v)
new-≈ᴹ [] r≈ = r≈ ∷ []
new-≈ᴹ (r≈' ∷ M≈) r≈ = r≈' ∷ (new-≈ᴹ M≈ r≈)


∥_∥-≈ᴹ : ∀ {ℓ} {M : F.Memory ℓ} {M' : C.Memory ℓ} → M ↓≈ᴹ M' → F.∥ M ∥ ≡ C.∥ M' ∥
∥ [] ∥-≈ᴹ = refl
∥ _ ∷ M≈ ∥-≈ᴹ rewrite ∥ M≈ ∥-≈ᴹ = refl

Ref′ : ∀ {n₁ n₂ τ τ' pc} {{p : MkTy τ τ'}} ℓ → n₁ ≡ n₂ → Ref {τ = τ'} ℓ n₁ ↓≈⟨ pc ⟩ᴿ Ref {τ = τ} ℓ n₂
Ref′ {n} {.n} ℓ refl = Ref ℓ n

lookup-≈ᴹ : ∀ {n ℓ τ} {v : C.Value τ} {M : F.Memory ℓ} {M' : C.Memory ℓ} →
                 n C.↦ v ∈ᴹ M' →
                 M ↓≈ᴹ M' →
                 Σ (Raw ⟦ τ ⟧ᵗ) (λ r → (n F.↦ r ∈ᴹ M) × (r ↓≈⟨ ℓ ⟩ᴿ v))
lookup-≈ᴹ C.Here (_∷_ {{p = p}} r≈ _) with ≡-MkTy p
... | refl rewrite !-MkTy p (mkTy _) = _ Σ., F.Here Σ., r≈
lookup-≈ᴹ (C.There n∈M) (_ ∷ M≈) = map id (map F.There id) (lookup-≈ᴹ n∈M M≈)

write-≈ᴹ : ∀ {n ℓ τ} {v : C.Value τ} {r : F.Raw ⟦ τ ⟧ᵗ} {M₁ : F.Memory ℓ} {M₂ M₂' : C.Memory ℓ} →
             r ↓≈⟨ ℓ ⟩ᴿ v →
             M₂' C.≔ M₂ [ n ↦ v ]ᴹ →
             M₁ ↓≈ᴹ M₂ →
             ∃ (λ M₁' → M₁' F.≔ M₁ [ n ↦ r ]ᴹ × M₁' ↓≈ᴹ M₂')
write-≈ᴹ r≈ C.Here (_∷_ {{p}} _ M≈) with ≡-MkTy p
... | refl = _ Σ., F.Here Σ., (r≈ ∷ M≈)
write-≈ᴹ r≈ (C.There M≔) (r≈' ∷ M≈) = map _ (map F.There (_∷_ r≈')) (write-≈ᴹ r≈ M≔ M≈)
