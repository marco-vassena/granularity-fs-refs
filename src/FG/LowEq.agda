-- This module defines a L-equivalence relation for all the categoris
-- of the calculus.  L-equivalence relates terms that are
-- indistinguishabile to an attacker at security level L.
--
-- This module is parametric in the security lattice 𝑳 = (𝓛, ⊑) and in
-- the attacker's security A ∈ 𝓛.

-- {-# OPTIONS --allow-unsolved-metas #-}

open import Lattice

module FG.LowEq {{𝑳 : Lattice}} (A : Label) where

open import FG.Types renaming (_∈_ to _∈ᵀ_ ; _⊆_ to _⊆ᵀ_)
open import FG.Syntax
open import Data.Empty
open import Data.Nat using (ℕ ; _≤_ ; _<_ ; s≤s ; z≤n) renaming (_⊔_ to _⊔ᴺ_)
open import Data.Nat.Properties
open import Data.Fin hiding (_≤_ ; _<_)
open import Function as F
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Generic.Bijection renaming (_∘_ to _∘ᴮ_)
open import Data.Product as P renaming (_,_ to ⟨_,_⟩)
open import FG.Valid

mutual

  -- Labeled values
  data _≈⟨_⟩ⱽ_ {τ} : Value τ → Bij → Value τ → Set where
    Valueᴸ : ∀ {r₁ r₂ ℓ β} → (ℓ⊑A : ℓ ⊑ A) (r≈ : r₁ ≈⟨ β ⟩ᴿ r₂) → (r₁ ^ ℓ) ≈⟨ β ⟩ⱽ (r₂ ^ ℓ)
    Valueᴴ : ∀ {r₁ r₂ ℓ₁ ℓ₂ β} → (ℓ₁⋤A : ℓ₁ ⋤ A) (ℓ₂⋤A : ℓ₂ ⋤ A) → (r₁ ^ ℓ₁) ≈⟨ β ⟩ⱽ (r₂ ^ ℓ₂)

  -- Raw values
  data _≈⟨_⟩ᴿ_ : ∀ {τ} → Raw τ → Bij → Raw τ → Set where

    Unit : ∀ {β} → （） ≈⟨ β ⟩ᴿ （）

    Lbl : ∀ {β} ℓ → ⌞ ℓ ⌟ ≈⟨ β ⟩ᴿ ⌞ ℓ ⌟

    Inl : ∀ {β} {τ₁ τ₂} {v₁ v₂ : Value τ₁} →
          v₁ ≈⟨ β ⟩ⱽ v₂ →
          inl {τ₂ = τ₂} v₁ ≈⟨ β ⟩ᴿ inl v₂

    Inr : ∀ {β} {τ₁ τ₂} {v₁ v₂ : Value τ₂} →
            v₁ ≈⟨ β ⟩ⱽ v₂ →
            inr {τ₁ = τ₁} v₁ ≈⟨ β ⟩ᴿ inr v₂

    Pair : ∀ {β} {τ₁ τ₂} {v₁ v₁' : Value τ₁} {v₂ v₂' : Value τ₂} →
             v₁ ≈⟨ β ⟩ⱽ v₁' →
             v₂ ≈⟨ β ⟩ⱽ v₂' →
             ⟨ v₁ , v₂ ⟩  ≈⟨ β ⟩ᴿ ⟨ v₁' , v₂' ⟩

    Fun : ∀ {β} {τ' τ Γ} {e : Expr (τ' ∷ Γ) τ}
            {θ₁ : Env Γ} {θ₂ : Env Γ} →
            θ₁ ≈⟨ β ⟩ᴱ θ₂ →
            ⟨ e , θ₁ ⟩ᶜ ≈⟨ β ⟩ᴿ ⟨ e , θ₂ ⟩ᶜ

    -- Flow-insensitive refs
    Ref-Iᴸ : ∀ {β} {ℓ τ n} →
               (ℓ⊑A : ℓ ⊑ A) → -- ⟨ n , m ⟩ ∈ᵗ β → -- We should not need the bijection anymore
               Refᴵ {τ = τ} ℓ n ≈⟨ β ⟩ᴿ Refᴵ ℓ n

    Ref-Iᴴ : ∀ {β} {ℓ₁ ℓ₂ n₁ n₂ τ} →
               (ℓ₁⋤A : ℓ₁ ⋤ A) (ℓ₂⋤A : ℓ₂ ⋤ A) →
               Refᴵ {τ = τ} ℓ₁ n₁ ≈⟨ β ⟩ᴿ Refᴵ ℓ₂ n₂

    -- Flow-sensitive refs
    Ref-S : ∀ {τ n m β} → ⟨ n , m ⟩ ∈ᵗ β →
              Refˢ {τ = τ} n ≈⟨ β ⟩ᴿ Refˢ m

    Id : ∀ {β} {τ} {v₁ v₂ : Value τ} →
           v₁ ≈⟨ β ⟩ⱽ v₂ →
           Id v₁ ≈⟨ β ⟩ᴿ Id v₂

  -- Environments.
  data _≈⟨_⟩ᴱ_  : ∀ {Γ} → Env Γ → Bij → Env Γ → Set where
    [] : ∀ {β} → [] ≈⟨ β ⟩ᴱ []
    _∷_ : ∀ {τ Γ β} {v₁ v₂ : Value τ} {θ₁ θ₂ : Env Γ} →
             (≈ⱽ : v₁ ≈⟨ β ⟩ⱽ v₂) →
             (≈ᴱ : θ₁ ≈⟨ β ⟩ᴱ θ₂) →
             (v₁ ∷ θ₁) ≈⟨ β ⟩ᴱ (v₂ ∷ θ₂)

-- Shorthands
Ref-Iᴸ′ : ∀ {τ ℓ n₁ n₂} {β : Bij} → ℓ ⊑ A → n₁ ≡ n₂ → Refᴵ {τ = τ} ℓ n₁ ≈⟨ β ⟩ᴿ Refᴵ ℓ n₂
Ref-Iᴸ′ ℓ⊑A refl = Ref-Iᴸ ℓ⊑A

Trueᴸ : ∀ {ℓ} {β : Bij} → ℓ ⊑ A → true ℓ ≈⟨ β ⟩ᴿ true ℓ
Trueᴸ ℓ⊑A = Inl (Valueᴸ ℓ⊑A Unit)

Falseᴸ : ∀ {ℓ} {β : Bij} → ℓ ⊑ A → false ℓ ≈⟨ β ⟩ᴿ false ℓ
Falseᴸ ℓ⊑A = Inr (Valueᴸ ℓ⊑A Unit)

-- Lemma
≈ⱽ-⊑ : ∀ {τ β} {v₁ v₂ : Value τ} (pc : Label) →
                   let r₁ ^ ℓ₁ = v₁
                       r₂ ^ ℓ₂ = v₂ in
                       v₁ ≈⟨ β ⟩ⱽ v₂ → (r₁ ^ (pc ⊔ ℓ₁)) ≈⟨ β ⟩ⱽ (r₂ ^ (pc ⊔ ℓ₂))
≈ⱽ-⊑ {v₁ = r₁ ^ ℓ} pc (Valueᴸ x x₁) with (pc ⊔ ℓ) ⊑? A
... | yes p = Valueᴸ p x₁
... | no ¬p = Valueᴴ ¬p ¬p
≈ⱽ-⊑ pc (Valueᴴ x x₁) = Valueᴴ (trans-⋤ (join-⊑₂ _ _) x) (trans-⋤ (join-⊑₂ _ _) x₁)

--------------------------------------------------------------------------------
-- Lemmas on L-equivalent environments.

-- Lookup in L-equivalent envs gives L-equivalent values
lookup-≈ⱽ : ∀ {τ Γ θ₁ θ₂ β} → (τ∈Γ : τ ∈ᵀ Γ) →
              θ₁ ≈⟨ β ⟩ᴱ θ₂ → (θ₁ !! τ∈Γ) ≈⟨ β ⟩ⱽ (θ₂ !! τ∈Γ)
lookup-≈ⱽ here (v₁≈v₂ ∷ θ₁≈θ₂) = v₁≈v₂
lookup-≈ⱽ (there τ∈Γ) (v₁≈v₂ ∷ θ₁≈θ₂) = lookup-≈ⱽ τ∈Γ θ₁≈θ₂


-- Slicing L-equivalent envs gives gives L-equivalent envs.
slice-≈ᴱ : ∀ {Γ₁ Γ₂ β} {θ₁ θ₂ : Env Γ₂} →
                 θ₁ ≈⟨ β ⟩ᴱ θ₂ →
                 (Γ₁⊆Γ₂ : Γ₁ ⊆ᵀ Γ₂) →
                 slice θ₁ Γ₁⊆Γ₂ ≈⟨ β ⟩ᴱ slice θ₂ Γ₁⊆Γ₂
slice-≈ᴱ [] base = []
slice-≈ᴱ (v₁≈v₂ ∷ θ₁≈θ₂) (cons p) = v₁≈v₂ ∷ slice-≈ᴱ θ₁≈θ₂ p
slice-≈ᴱ (v₁≈v₂ ∷ θ₁≈θ₂) (drop p) = slice-≈ᴱ θ₁≈θ₂ p

--------------------------------------------------------------------------------

-- Subsumed by the above
-- -- Derive L-equivalence for heaps
-- open import Generic.Heap.LowEq {Ty} {Value} _≈⟨_⟩ⱽ_ A public -- TODO: using just that?

-- -- Derive L-equivalence for stores,
-- open import Generic.Store.LowEq {Ty} {Raw} _≈⟨_⟩ᴿ_ A public -- TODO: using just that?

--------------------------------------------------------------------------------
-- TODO: these should either not be needed anymore or moved to HLowEq (e.g., ⌞_⌟ ; ≈ᶜ-⊑)
-- This seems to be needed in the FG2CG translation.
open import Generic.Value.HLowEq {Ty} {Value} _≈⟨_⟩ⱽ_ public

label-of-≈ⱽ : ∀ {τ β} {v₁ v₂ : Value τ} → v₁ ≈⟨ β ⟩ⱽ v₂ →
                let (r₁ ^ ℓ₁) = v₁
                    (r₂ ^ ℓ₂) = v₂ in (⌞ ℓ₁ ⌟ ^ ℓ₁) ≈⟨ β ⟩ⱽ (⌞ ℓ₂ ⌟ ^ ℓ₂)
label-of-≈ⱽ (Valueᴸ x x₁) = Valueᴸ x (Lbl _)
label-of-≈ⱽ (Valueᴴ x x₁) = Valueᴴ x x₁

extract-≈ᴿ : ∀ {τ β} {v₁ v₂ : Value τ} → v₁ ≈⟨ β ⟩ⱽ v₂ →
               let r₁ ^ ℓ₁ = v₁
                   r₂ ^ ℓ₂ = v₂ in ℓ₁ ⊑ A → r₁ ≈⟨ β ⟩ᴿ r₂
extract-≈ᴿ (Valueᴸ ℓ⊑A r≈) ⊑₁ = r≈
extract-≈ᴿ (Valueᴴ ℓ₁⋤A ℓ₂⋤A) ⊑₁ = ⊥-elim (ℓ₁⋤A ⊑₁)

-- Lift low-equivalence to configurations
open Conf

-- Derive L-equivalence relation for stores and heaps.
open import Generic.PState.LowEq {Ty} {Ty} {Raw} {Value} _≈⟨_⟩ᴿ_ _≈⟨_⟩ⱽ_ A public

record _≈⟨_,_⟩ᴬ_ {V : Set} (c₁ : Conf V) (R : V  → V → Set) (β : Bij) (c₂ : Conf V) : Set where
  constructor ⟨_,_⟩
  field
    pstate-≈ᴾ : ⟨ store c₁ , heap c₁ ⟩ ≈⟨ β ⟩ᴾ ⟨ store c₂ , heap c₂ ⟩
    term-≈ : R (term c₁) (term c₂)

  open _≈⟨_⟩ᴾ_ pstate-≈ᴾ public

open _≈⟨_,_⟩ᴬ_ {{ ... }}

-- L-Equivalence for initial configurations.  For terms we do not use
-- the bijection but simply require syntactic equivalence.
_≈⟨_⟩ᴵ_ : ∀ {Γ τ} → IConf Γ τ → Bij → IConf Γ τ → Set
c₁ ≈⟨ β ⟩ᴵ c₂ = c₁ ≈⟨ _≡_ , β ⟩ᴬ c₂

-- Final configurations.
_≈⟨_⟩ᶜ_ : ∀ {τ} → FConf τ → Bij → FConf τ → Set
c₁ ≈⟨ β ⟩ᶜ c₂ = c₁ ≈⟨ _≈⟨ β ⟩ⱽ_ , β ⟩ᴬ c₂

--------------------------------------------------------------------------------
-- Properties: L-equivalence for raw, labeled values, and environment is an
-- equivalence relation, where reflexivity is defined over the domain
-- of terms.  Notice that this is not the case for heaps because the
-- domain and the range of the bijection must be included in the
-- address space of the heap itself, therefore reflexivity holds only
-- for valid heaps free of dangling references.

open import Generic.Bijection

private module R = IProps Ty Raw
private module V = IProps Ty Value
private module E = IProps Ctx Env

mutual

  wken-≈ⱽ : V.Wkenᴮ _≈⟨_⟩ⱽ_
  wken-≈ⱽ β⊆β' (Valueᴸ ℓ⊑A r≈) = Valueᴸ ℓ⊑A (wken-≈ᴿ β⊆β' r≈)
  wken-≈ⱽ β⊆β' (Valueᴴ ℓ₁⋤A ℓ₂⋤A) = Valueᴴ ℓ₁⋤A ℓ₂⋤A

  wken-≈ᴱ : E.Wkenᴮ _≈⟨_⟩ᴱ_
  wken-≈ᴱ β⊆β' [] = []
  wken-≈ᴱ β⊆β' (≈ⱽ ∷ ≈ᴱ) = wken-≈ⱽ β⊆β' ≈ⱽ ∷ wken-≈ᴱ β⊆β' ≈ᴱ

  wken-≈ᴿ : R.Wkenᴮ _≈⟨_⟩ᴿ_
  wken-≈ᴿ β⊆β' Unit = Unit
  wken-≈ᴿ β⊆β' (Lbl ℓ) = Lbl ℓ
  wken-≈ᴿ β⊆β' (Inl x) = Inl (wken-≈ⱽ β⊆β' x)
  wken-≈ᴿ β⊆β' (Inr x) = Inr (wken-≈ⱽ β⊆β' x)
  wken-≈ᴿ β⊆β' (Pair x y) = Pair (wken-≈ⱽ β⊆β' x) (wken-≈ⱽ β⊆β' y)
  wken-≈ᴿ β⊆β' (Fun x) = Fun (wken-≈ᴱ β⊆β' x)
  wken-≈ᴿ β⊆β' (Ref-Iᴸ ℓ⊑A) = Ref-Iᴸ ℓ⊑A
  wken-≈ᴿ β⊆β' (Ref-Iᴴ ℓ₁⋤A ℓ₂⋤A) = Ref-Iᴴ ℓ₁⋤A ℓ₂⋤A
  wken-≈ᴿ β⊆β' (Ref-S ∈ᴮ) = Ref-S (bij-⊆ β⊆β' ∈ᴮ)
  wken-≈ᴿ β⊆β' (Id x) = Id (wken-≈ⱽ β⊆β' x)

--------------------------------------------------------------------------------

  -- Reflexive
  refl-≈ⱽ : V.Reflexiveᴮ _≈⟨_⟩ⱽ_ ∥_∥ⱽ
  refl-≈ⱽ {x = r ^ ℓ} with ℓ ⊑? A
  refl-≈ⱽ {x = r ^ ℓ} | yes ℓ⊑A = Valueᴸ ℓ⊑A refl-≈ᴿ
  refl-≈ⱽ {x = r ^ ℓ} | no ℓ⋤A = Valueᴴ ℓ⋤A ℓ⋤A

  refl-≈ᴿ : R.Reflexiveᴮ _≈⟨_⟩ᴿ_ ∥_∥ᴿ
  refl-≈ᴿ {x = （）} = Unit
  refl-≈ᴿ {x = ⟨ _ , θ ⟩ᶜ} = Fun refl-≈ᴱ
  refl-≈ᴿ {x = (inl v)} = Inl refl-≈ⱽ
  refl-≈ᴿ {x = (inr v)} = Inr refl-≈ⱽ
  refl-≈ᴿ {x = ⟨ v₁ , v₂ ⟩} = Pair ≈₁ ≈₂
    where ≈₁ = wken-≈ⱽ (ι-⊆ (m≤m⊔n ∥ v₁ ∥ⱽ ∥ v₂ ∥ⱽ)) refl-≈ⱽ
          ≈₂ = wken-≈ⱽ (ι-⊆ (n≤m⊔n ∥ v₁ ∥ⱽ ∥ v₂ ∥ⱽ)) refl-≈ⱽ
  refl-≈ᴿ {x = (Refᴵ ℓ n)} with ℓ ⊑? A
  ... | yes ℓ⊑A = Ref-Iᴸ ℓ⊑A
  ... | no ℓ⋤A = Ref-Iᴴ ℓ⋤A ℓ⋤A
  refl-≈ᴿ {x = (Refˢ n)} = Ref-S (ι-∈ (s≤s ≤-refl))
  refl-≈ᴿ {x = ⌞ ℓ ⌟} = Lbl ℓ
  refl-≈ᴿ {x = (Id v)} = Id refl-≈ⱽ

  refl-≈ᴱ : E.Reflexiveᴮ _≈⟨_⟩ᴱ_ ∥_∥ᴱ
  refl-≈ᴱ {x = []} = []
  refl-≈ᴱ {x = (v ∷ θ)} = ≈₁ ∷ ≈₂
    where ≈₁ = wken-≈ⱽ (ι-⊆ (m≤m⊔n ∥ v ∥ⱽ ∥ θ ∥ᴱ)) refl-≈ⱽ
          ≈₂ = wken-≈ᴱ (ι-⊆ (n≤m⊔n ∥ v ∥ⱽ ∥ θ ∥ᴱ)) refl-≈ᴱ

----------------------------------------------------------------------------------

  -- Symmetric
  sym-≈ⱽ : V.Symmetricᴮ _≈⟨_⟩ⱽ_
  sym-≈ⱽ (Valueᴸ ℓ⊑A r≈) = Valueᴸ ℓ⊑A (sym-≈ᴿ r≈)
  sym-≈ⱽ (Valueᴴ ℓ₁⋤A ℓ₂⋤A) = Valueᴴ ℓ₂⋤A ℓ₁⋤A

  sym-≈ᴿ : R.Symmetricᴮ _≈⟨_⟩ᴿ_
  sym-≈ᴿ Unit = Unit
  sym-≈ᴿ (Lbl ℓ) = Lbl ℓ
  sym-≈ᴿ (Inl x) = Inl (sym-≈ⱽ x)
  sym-≈ᴿ (Inr x) = Inr (sym-≈ⱽ x)
  sym-≈ᴿ (Pair x y) = Pair (sym-≈ⱽ x) (sym-≈ⱽ y)
  sym-≈ᴿ (Fun x) = Fun (sym-≈ᴱ x)
  sym-≈ᴿ {β = β} (Ref-Iᴸ ℓ⊑A) = Ref-Iᴸ ℓ⊑A
  sym-≈ᴿ (Ref-Iᴴ ℓ₁⋤A ℓ₂⋤A) = Ref-Iᴴ ℓ₂⋤A ℓ₁⋤A
  sym-≈ᴿ {β = β} (Ref-S x) = Ref-S (Bijectionᴾ.right-inverse-of β x)
  sym-≈ᴿ (Id x) = Id (sym-≈ⱽ x)

  sym-≈ᴱ : E.Symmetricᴮ _≈⟨_⟩ᴱ_
  sym-≈ᴱ [] = []
  sym-≈ᴱ (≈ⱽ ∷ ≈ᴱ) = sym-≈ⱽ ≈ⱽ ∷ sym-≈ᴱ ≈ᴱ

  -- Transitive
  trans-≈ᴿ : R.Transitiveᴮ _≈⟨_⟩ᴿ_
  trans-≈ᴿ Unit Unit = Unit
  trans-≈ᴿ (Lbl ℓ) (Lbl .ℓ) = Lbl ℓ
  trans-≈ᴿ (Inl x) (Inl y) = Inl (trans-≈ⱽ x y)
  trans-≈ᴿ (Inr x) (Inr y) = Inr (trans-≈ⱽ x y)
  trans-≈ᴿ (Pair x₁ y₁) (Pair x₂ y₂) = Pair (trans-≈ⱽ x₁ x₂) (trans-≈ⱽ y₁ y₂)
  trans-≈ᴿ (Fun x) (Fun y) = Fun (trans-≈ᴱ x y)
  trans-≈ᴿ {β₁ = β₁} {β₂} (Ref-Iᴸ ℓ⊑A) (Ref-Iᴸ ℓ⊑A₁)
    = Ref-Iᴸ ℓ⊑A₁
  trans-≈ᴿ (Ref-Iᴸ ℓ⊑A) (Ref-Iᴴ ℓ₁⋤A ℓ₂⋤A) = ⊥-elim (ℓ₁⋤A ℓ⊑A)
  trans-≈ᴿ (Ref-Iᴴ ℓ₁⋤A ℓ₂⋤A) (Ref-Iᴸ ℓ⊑A) = ⊥-elim (ℓ₂⋤A ℓ⊑A)
  trans-≈ᴿ (Ref-Iᴴ ℓ₁⋤A ℓ₂⋤A) (Ref-Iᴴ ℓ₁⋤A₁ ℓ₂⋤A₁) = Ref-Iᴴ ℓ₁⋤A ℓ₂⋤A₁
  trans-≈ᴿ {β₁ = β₁} {β₂} (Ref-S x) (Ref-S y)
    = Ref-S (join-∈ᵗ {β₁ = β₁} {β₂} x y)
  trans-≈ᴿ (Id x) (Id y) = Id (trans-≈ⱽ x y)

  trans-≈ⱽ : V.Transitiveᴮ _≈⟨_⟩ⱽ_
  trans-≈ⱽ (Valueᴸ ℓ⊑A r≈) (Valueᴸ ℓ⊑A₁ r≈₁) = Valueᴸ ℓ⊑A₁ (trans-≈ᴿ r≈ r≈₁)
  trans-≈ⱽ (Valueᴸ ℓ⊑A r≈) (Valueᴴ ℓ₁⋤A ℓ₂⋤A) = ⊥-elim (ℓ₁⋤A ℓ⊑A)
  trans-≈ⱽ (Valueᴴ ℓ₁⋤A ℓ₂⋤A) (Valueᴸ ℓ⊑A r≈) = ⊥-elim (ℓ₂⋤A ℓ⊑A)
  trans-≈ⱽ (Valueᴴ ℓ₁⋤A ℓ₂⋤A) (Valueᴴ ℓ₁⋤A₁ ℓ₂⋤A₁) = Valueᴴ ℓ₁⋤A ℓ₂⋤A₁

  trans-≈ᴱ : E.Transitiveᴮ _≈⟨_⟩ᴱ_
  trans-≈ᴱ [] [] = []
  trans-≈ᴱ (≈ⱽ₁ ∷ ≈ᴱ₁) (≈ⱽ₂ ∷ ≈ᴱ₂) = trans-≈ⱽ ≈ⱽ₁ ≈ⱽ₂ ∷ trans-≈ᴱ ≈ᴱ₁ ≈ᴱ₂

--------------------------------------------------------------------------------

open import Generic.Bijection

-- Why do we need this?
isEquivⱽ : V.IsEquivalenceᴮ _≈⟨_⟩ⱽ_ ∥_∥ⱽ
isEquivⱽ = record { reflᴮ = refl-≈ⱽ
           ; wkenᴮ = wken-≈ⱽ
           ; symᴮ = sym-≈ⱽ
           ; transᴮ = trans-≈ⱽ }

isEquivᴿ : R.IsEquivalenceᴮ _≈⟨_⟩ᴿ_ ∥_∥ᴿ
isEquivᴿ = record { reflᴮ = refl-≈ᴿ
           ; wkenᴮ = wken-≈ᴿ
           ; symᴮ = sym-≈ᴿ
           ; transᴮ = trans-≈ᴿ }

isEquivᴱ : E.IsEquivalenceᴮ _≈⟨_⟩ᴱ_  ∥_∥ᴱ
isEquivᴱ = record { reflᴮ = refl-≈ᴱ
           ; wkenᴮ = wken-≈ᴱ
           ; symᴮ = sym-≈ᴱ
           ; transᴮ = trans-≈ᴱ }

-- Why this?
import Generic.ValidEquivalence as G
open G Ty

𝑹 : IsValidEquivalence Raw _≈⟨_⟩ᴿ_
𝑹 = record { ∥_∥ = ∥_∥ᴿ ; isValid = isValidᴿ ; isEquiv = isEquivᴿ }

𝑽 : IsValidEquivalence Value _≈⟨_⟩ⱽ_
𝑽 = record { ∥_∥ = ∥_∥ⱽ ; isValid = isValidⱽ ; isEquiv = isEquivⱽ }

𝑬 : G.IsValidEquivalence Ctx Env _≈⟨_⟩ᴱ_
𝑬 = record { ∥_∥ = ∥_∥ᴱ ; isValid = isValidᴱ ; isEquiv = isEquivᴱ }

open ≈ᴾ-Props 𝑹 𝑽 public
