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
open import Data.Unit using (⊤)
open import Data.Product renaming (_,_ to _^_)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

mutual

  -- The relation is parametric in the cross-language relation for
  -- types (MkTy) to ensure that only type-related values can be
  -- related.

  -- Values.
  data CEqⱽ {τ τ'} (pc : Label) (p : MkTy τ τ') (v : C.Value τ) : F.Value τ' → Set where
    _↓_ : ∀ {ℓ r} → ℓ ⊑ pc → CEqᴿ pc p v r → CEqⱽ pc p v (r ^ ℓ)

  -- Raw values.
  data CEqᴿ (pc : Label) : ∀ {τ τ'} → MkTy τ τ' → C.Value τ → F.Raw τ' → Set where

     ⌞_⌟ : ∀ ℓ → CEqᴿ pc 𝓛 ⌞ ℓ ⌟ ⌞ ℓ ⌟

     （） : CEqᴿ pc Unit （） （）

     Refᴵ : ∀ {τ τ'} {{p : MkTy τ τ'}} ℓ n → CEqᴿ pc (Ref p) (Refᴵ ℓ n) (Refᴵ ℓ n)

     Refˢ : ∀ {τ τ'} {{p : MkTy τ τ'}} n → CEqᴿ pc (Ref p) (Refˢ n) (Refˢ n)

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

-- _↓≈⟨_⟩ᴸ_ : ∀ {τ τ'} {{c : MkTy (Labeled τ) τ'}} → F.Value τ' → Label → C.LValue τ → Set
-- _↓≈⟨_⟩ᴸ_ {{c}} v' pc (v ^ ℓ) = CEq pc c (Labeled ℓ v) v'

_↓≈ᴱ_ : ∀ {τ τ' Γ Γ'} {{p : MkTy τ τ'}} {{c : MkCtx Γ Γ'}} → F.Expr Γ' (Id unit ➔ τ') → C.Expr Γ (LIO τ) → Set
_↓≈ᴱ_ {{p}} {{c}} e e' = Cg2Fgᴱ c (LIO p) e' e

--------------------------------------------------------------------------------
-- Shorthands

trueᴿ : ∀ {pc} → (F.true pc) ↓≈⟨ pc ⟩ᴿ C.true
trueᴿ = Inl (refl-⊑ ↓ （）)

falseᴿ : ∀ {pc} → (F.false pc) ↓≈⟨ pc ⟩ᴿ C.false
falseᴿ = Inr (refl-⊑ ↓ （）)

-- TODO: rename Refᴵ′
Ref′ : ∀ {n₁ n₂ τ τ' pc} {{p : MkTy τ τ'}} ℓ → n₁ ≡ n₂ → Refᴵ {τ = τ'} ℓ n₁ ↓≈⟨ pc ⟩ᴿ Refᴵ {τ = τ} ℓ n₂
Ref′ {n} {.n} ℓ refl = Refᴵ ℓ n

Refˢ′ : ∀ {n₁ n₂ τ τ' pc} {{p : MkTy τ τ'}} → n₁ ≡ n₂ → Refˢ {τ = τ'} n₁ ↓≈⟨ pc ⟩ᴿ Refˢ {τ = τ} n₂
Refˢ′ refl = Refˢ _
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
  refl-≈⟨ pc ⟩ᴿ (C.Refᴵ ℓ n) = Refᴵ ℓ n
  refl-≈⟨ pc ⟩ᴿ (C.Refˢ n) = Refˢ n
  refl-≈⟨ pc ⟩ᴿ C.⌞ ℓ ⌟ = ⌞ ℓ ⌟

  refl-≈⟨_⟩ᵉ_ : ∀ {Γ} → (pc : Label) (θ : C.Env Γ) → ⟦ θ ⟧ᵉ pc ↓≈⟨ pc ⟩ᵉ θ
  refl-≈⟨ _ ⟩ᵉ C.[] = []
  refl-≈⟨ pc ⟩ᵉ (v C.∷ θ) = refl-≈⟨ pc ⟩ⱽ v ∷ (refl-≈⟨ pc ⟩ᵉ θ)

import Generic.ICrossEq Label 𝑻 as R

𝑽 : R.ICEq C.Value F.Raw
𝑽 = record { ⟦_⟧ = ⟦_⟧ᴿ
           ; _↓≈⟨_,_⟩_ = λ v₁ ℓ τ≈ v₂ → CEqᴿ ℓ τ≈ v₂ v₁
           ; refl-↓≈⟨_⟩ = refl-≈⟨_⟩ᴿ_ }

import Generic.ICrossEq ⊤ 𝑻 as L

data CEqᴸ {τ τ'} (p : MkTy τ τ') (v : C.LValue τ) : F.Value τ' → Set where
  ⌞_⌟ᴸ : ∀ {r} → CEqᴿ (proj₂ v) p (proj₁ v) r → CEqᴸ p v (r ^ proj₂ v)

_↓≈ᴸ_ :  ∀ {τ τ'} {{c : MkTy τ τ'}} → F.Value τ' → C.LValue τ → Set
_↓≈ᴸ_  {{c}} v lv = CEqᴸ c lv v

refl-≈ᴸ : ∀ {τ} → (v : C.LValue τ) → ⟦ v ⟧ᴸ ↓≈ᴸ v
refl-≈ᴸ (v ^ ℓ) = ⌞ refl-≈⟨ ℓ ⟩ᴿ v  ⌟ᴸ

𝑽ᴸ : L.ICEq C.LValue F.Value
𝑽ᴸ = record { ⟦_⟧ = λ lv _ → ⟦ lv ⟧ᴸ
            ; _↓≈⟨_,_⟩_ = λ v₁ pc p v₂ → CEqᴸ p v₂ v₁
            ; refl-↓≈⟨_⟩ = λ pc v → refl-≈ᴸ v }

mutual

  -- Weakening. We can always increase the upper bound (pc) over the label  annotations.
  ≈ⱽ-⊑  : ∀ {τ τ' pc₁ pc₂} {v : C.Value τ} {v' : F.Value τ'} {{p : MkTy τ τ'}} → v' ↓≈⟨ pc₁ ⟩ⱽ v → pc₁ ⊑ pc₂ → v' ↓≈⟨ pc₂ ⟩ⱽ v
  ≈ⱽ-⊑ (p₁ ↓ r≈) p₂ = (trans-⊑ p₁ p₂) ↓ (≈ᴿ-⊑ r≈ p₂)

  ≈ᴿ-⊑ : ∀ {τ τ' pc₁ pc₂} {v : C.Value τ} {v' : F.Raw τ'} {{p : MkTy τ τ'}} → v' ↓≈⟨ pc₁ ⟩ᴿ v → pc₁ ⊑ pc₂ → v' ↓≈⟨ pc₂ ⟩ᴿ v
  ≈ᴿ-⊑ ⌞ ℓ ⌟ p = ⌞ ℓ ⌟
  ≈ᴿ-⊑ （） p = （）
  ≈ᴿ-⊑ (Refˢ n) p = Refˢ n
  ≈ᴿ-⊑ (Refᴵ ℓ n) p = Refᴵ ℓ n
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

slice-↓≈ : ∀ {Γ Γ' pc} {θ₁ : F.Env ⟦ Γ ⟧ᶜ} {θ₂ : C.Env Γ} (p : Γ' C.⊆ Γ) → θ₁ ↓≈⟨ pc ⟩ᵉ θ₂  → F.slice θ₁ ⟦ p ⟧⊆ ↓≈⟨ pc ⟩ᵉ C.slice θ₂ p
slice-↓≈ C.base [] = []
slice-↓≈ (C.cons p) (x ∷ y) = x ∷ (slice-↓≈ p y)
slice-↓≈ (C.drop p) (x ∷ y) = slice-↓≈ p y

!!-↓≈ : ∀ {pc τ Γ θ₁} {θ₂ : C.Env Γ} → (τ∈Γ : τ C.∈ Γ) → θ₁ ↓≈⟨ pc ⟩ᵉ θ₂ → (θ₁ F.!! ⟦ τ∈Γ ⟧∈) ↓≈⟨ pc ⟩ⱽ (θ₂ C.!! τ∈Γ)
!!-↓≈ C.here (x ∷ θ₁≈θ₂) = x
!!-↓≈ (C.there τ∈Γ) (x ∷ θ₁≈θ₂) = !!-↓≈ τ∈Γ θ₁≈θ₂

--------------------------------------------------------------------------------
-- Derive cross equivalence for program state (store and heap)

open import Generic.PState.CrossEq 𝑻 𝑻 𝑽 𝑽ᴸ public

--------------------------------------------------------------------------------

-- Initial configurations (Expr)
data _↓≈ᴵ_ {Γ τ} : F.IConf ⟦ Γ ⟧ᶜ ⟦ τ ⟧ᵗ → C.EConf Γ (LIO τ) → Set where
  ⌞_⌟ᴵ : ∀ {Σ pc μ μ' Σ'} {e : C.Expr Γ (LIO τ)} → F.⟨ Σ , μ ⟩ ↓≈ᴾ C.⟨ Σ' , μ' ⟩ →
           ⟨ Σ , μ , ⟦ e ⟧ᴱ ∘ (Id （）) ⟩ ↓≈ᴵ ⟨ Σ' , μ' , pc , e ⟩

⌜_⌝ᴵ : ∀ {Γ τ c₁} {c₂ : EConf Γ (LIO τ)} → c₁ ↓≈ᴵ c₂ →
            let ⟨ Σ₁ , μ₁ ,  _ ⟩ = c₁
                ⟨ Σ₂ , μ₂ , _ , _ ⟩ = c₂ in
                F.⟨ Σ₁ , μ₁ ⟩ ↓≈ᴾ C.⟨ Σ₂ , μ₂ ⟩
⌜_⌝ᴵ ⌞ p≈ ⌟ᴵ = p≈

-- Initial configurations (Thunk)
data _↓≈ᵀ_ {Γ τ} : F.IConf ⟦ Γ ⟧ᶜ ⟦ τ ⟧ᵗ → C.TConf Γ (LIO τ) → Set where
  ⌞_⌟ᵀ : ∀ {Σ pc Σ' μ μ'} {t : C.Thunk Γ (LIO τ)} →
           F.⟨ Σ , μ ⟩ ↓≈ᴾ C.⟨ Σ' , μ' ⟩ →
           ⟨ Σ , μ , ⟦ t ⟧ᵀ ⟩ ↓≈ᵀ ⟨ Σ' , μ' , pc , t ⟩

⌜_⌝ᵀ : ∀ {Γ τ c₁} {c₂ : TConf Γ (LIO τ)} → c₁ ↓≈ᵀ c₂ →
            let ⟨ Σ₁ , μ₁ ,  _ ⟩ = c₁
                ⟨ Σ₂ , μ₂ , _ , _ ⟩ = c₂ in
                F.⟨ Σ₁ , μ₁ ⟩ ↓≈ᴾ C.⟨ Σ₂ , μ₂ ⟩
⌜_⌝ᵀ ⌞ p≈ ⌟ᵀ = p≈

-- Final configurations.
data _↓≈ᶜ_ {τ τ'} : F.FConf τ' → C.FConf τ → Set where
  ⟨_,_⟩ : ∀ {Σ Σ' μ μ' pc r v} {{p : MkTy τ τ'}} →
            F.⟨ Σ , μ ⟩ ↓≈ᴾ C.⟨ Σ' , μ' ⟩ →
            r ↓≈⟨ pc ⟩ᴿ v →
            F.⟨ Σ , μ , r ^ pc ⟩ ↓≈ᶜ ⟨ Σ' , μ' , pc , v ⟩

refl-≈ᴵ : ∀ {Γ τ} → (c : C.EConf Γ (LIO τ)) → ⟦ c ⟧ᴵ ↓≈ᴵ c
refl-≈ᴵ ⟨ Σ , μ , pc , e ⟩ = ⌞ refl-↓≈ᴾ C.⟨ Σ , μ ⟩ ⌟ᴵ
