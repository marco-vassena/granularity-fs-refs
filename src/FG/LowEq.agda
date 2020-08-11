-- This module defines a L-equivalence relation for all the categoris
-- of the calculus.  L-equivalence relates terms that are
-- indistinguishabile to an attacker at security level L.
--
-- This module is parametric in the security lattice 𝑳 = (𝓛, ⊑) and in
-- the attacker's security A ∈ 𝓛.

-- {-# OPTIONS --allow-unsolved-metas #-}

open import Lattice

module FG.LowEq {{𝑳 : Lattice}} (A : Label) where

open import FG.Types hiding (_⊆_)
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
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import FG.Valid

-- mutual
  -- Moved to Valid
  -- "Size" of a value
  -- ∣_∣ⱽ : ∀ {τ} → Value τ → ℕ
  -- ∣ r ^ ℓ ∣ⱽ = ∣ r ∣ᴿ

  -- ∣_∣ᴿ : ∀ {τ} → Raw τ → ℕ
  -- ∣ （） ∣ᴿ = 0
  -- ∣ ⟨ x , θ ⟩ᶜ ∣ᴿ = ∣ θ ∣ᴱ
  -- ∣ inl x ∣ᴿ = ∣ x ∣ⱽ
  -- ∣ inr x ∣ᴿ = ∣ x ∣ⱽ
  -- ∣ ⟨ x , y ⟩ ∣ᴿ = ∣ x ∣ⱽ ⊔ᴺ ∣ y ∣ⱽ
  -- ∣ Refᴵ x n ∣ᴿ = ℕ.suc n
  -- ∣ Refˢ n ∣ᴿ = ℕ.suc n
  -- ∣ ⌞ x ⌟ ∣ᴿ = 0
  -- ∣ Id x ∣ᴿ = ∣ x ∣ⱽ

  -- ∣_∣ᴱ : ∀ {Γ} → Env Γ → ℕ
  -- ∣ [] ∣ᴱ = 0
  -- ∣ v ∷ θ ∣ᴱ = ∣ v ∣ⱽ ⊔ᴺ ∣ θ ∣ᴱ


mutual

-- Adding a bijection after the fact is a bit inconvenient.  Ideally,
-- we would parametrize values, expressions and all the other
-- categories with a number n to keep track of the minimum size of the
-- domain of the heap. Since this change would involve virtually
-- the whole formalization, I will add extra assumptions only
-- where needed.
--
-- Maybe this is not true. Only values would need this extra parameter
-- and it seems we can universally quantify the bijection in the
-- low-equivalence relation without the need for pervasive changes to
-- the syntax.

  -- This is not a good idea because it is too restrictive.  We need
  -- at least a bijection that is "large" enough, but it can also be
  -- larger.
  -- data Value-≈ⱽ {τ} : (v₁ v₂ : Value τ) → Bij⟨ v₁ , v₂ ⟩ⱽ → Set where

  -- data Raw-≈ᴿ : ∀ {τ} (r₁ r₂ : Raw τ) → Bij⟨ r₁ , r₂ ⟩ᴿ → Set where
  --   Pair : ∀ {τ₁ τ₂} {v₁ v₁' : Value τ₁} {v₂ v₂' : Value τ₂}
  --            {β : Bij (∣ v₁ ∣ⱽ ⊔ᴺ ∣ v₂ ∣ⱽ) (∣ v₁' ∣ⱽ ⊔ᴺ ∣ v₂' ∣ⱽ)}  →
  --            Value-≈ⱽ v₁ v₁ β  →
  --            Value-≈ⱽ v₂ v₂' β →
  --            Raw-≈ᴿ ⟨ v₁ , v₂ ⟩ ⟨ v₁' , v₂' ⟩ β

  data _≈⟨_⟩ⱽ_ {τ} : Value τ → Bij → Value τ → Set where
    Valueᴸ : ∀ {r₁ r₂ ℓ β} → (ℓ⊑A : ℓ ⊑ A) (r≈ : r₁ ≈⟨ β ⟩ᴿ r₂) → (r₁ ^ ℓ) ≈⟨ β ⟩ⱽ (r₂ ^ ℓ)
    Valueᴴ : ∀ {r₁ r₂ ℓ₁ ℓ₂ β} → (ℓ₁⋤A : ℓ₁ ⋤ A) (ℓ₂⋤A : ℓ₂ ⋤ A) → (r₁ ^ ℓ₁) ≈⟨ β ⟩ⱽ (r₂ ^ ℓ₂)

  -- _≈⟨_⟩ⱽ_ : ∀ {τ n m} → Value τ → Bij n m → Value τ → Set
  -- v₁ ≈⟨ β ⟩ⱽ v₂ = Value-≈ β v₁ v₂

  -- Raw values
  -- TODO: n m could be paramters
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
    Ref-Iᴸ : ∀ {β} {ℓ τ n m} →
               (ℓ⊑A : ℓ ⊑ A) → ⟨ n , m ⟩ ∈ᵗ β →
               Refᴵ {τ = τ} ℓ n ≈⟨ β ⟩ᴿ Refᴵ ℓ m

    Ref-Iᴴ : ∀ {β} {ℓ₁ ℓ₂ n₁ n₂ τ} →
               (ℓ₁⋤A : ℓ₁ ⋤ A) (ℓ₂⋤A : ℓ₂ ⋤ A) →
               Refᴵ {τ = τ} ℓ₁ n₁ ≈⟨ β ⟩ᴿ Refᴵ ℓ₂ n₂

    -- Flow-sensitive refs
    Ref-S : ∀ {τ n m β} → ⟨ n , m ⟩ ∈ᵗ β →
              Refˢ {τ = τ} n ≈⟨ β ⟩ᴿ Refˢ m

    -- TODO: Case when the indexes are not in the bijection ?

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

-- Shorthand
Ref-Iᴸ′ : ∀ {τ ℓ n₁ n₂} {β : Bij} → ℓ ⊑ A → ⟨ n₁ , n₂ ⟩ ∈ᵗ β → Refᴵ {τ = τ} ℓ n₁ ≈⟨ β ⟩ᴿ Refᴵ ℓ n₂
Ref-Iᴸ′ ℓ⊑A x = Ref-Iᴸ ℓ⊑A x

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

-- Derive L-equivalence for stores,
open import Generic.Store.LowEq {Ty} {Raw} _≈⟨_⟩ᴿ_ A as S using (_≈⟨_⟩ˢ_ ; cellᴸ) public

-- _≈⟨_⟩ˢ_ : Store → Bij → Store → Set
-- Σ₁ ≈⟨ β ⟩ˢ Σ₂ = Σ₁ ≈ˢ Σ₂
--   where open import Generic.Store.LowEq {Ty} {Raw} (λ r₁ r₂ → r₁ ≈⟨ β ⟩ᴿ r₂) A

-- -- Derive L-equivalence for heaps
-- _≈⟨_⟩ᴴ_ : ∀ (μ₁ : Heap) → Bij → (μ₂ : Heap) → Set
-- μ₁ ≈⟨ β ⟩ᴴ μ₂ = μ₁ H.≈⟨ β ⟩ᴴ μ₂
--   where open import Generic.Heap.LowEq {Ty} {Value} 𝑯 (λ v₁ v₂ → v₁ ≈⟨ β ⟩ⱽ v₂) A as H

-- --
-- -- using (_≈⟨_⟩ᴴ_ ; _≈ᴴ_ ; new-≈ᴴ ; Bij⟨_,_⟩)



-- Lift low-equivalence to configurations
open Conf

-- open import Generic.Bijection as B

record _≈⟨_,_⟩ᴬ_ {V : Set} (c₁ : Conf V) (R : V  → V → Set) (β : Bij) (c₂ : Conf V) : Set where
  constructor ⟨_,_⟩
  field
    store-≈ˢ : store c₁ ≈⟨ β ⟩ˢ store c₂
    term-≈ : R (term c₁) (term c₂)

open _≈⟨_,_⟩ᴬ_ {{ ... }}

-- L-Equivalence for initial configurations.  For terms we do not use
-- the bijection but simply require syntactic equivalence.
_≈⟨_⟩ᴵ_ : ∀ {Γ τ} → IConf Γ τ → Bij → IConf Γ τ → Set
c₁ ≈⟨ β ⟩ᴵ c₂ = c₁ ≈⟨ _≡_ , β ⟩ᴬ c₂

-- Final configurations.
_≈⟨_⟩ᶜ_ : ∀ {τ} → FConf τ → Bij → FConf τ → Set
c₁ ≈⟨ β ⟩ᶜ c₂ = c₁ ≈⟨ _≈⟨ β ⟩ⱽ_ , β ⟩ᴬ c₂

--------------------------------------------------------------------------------
-- Properties: L-equivalence is an equivalence relation.

mutual

  -- TODO: update description
  -- Weaken the identity bijection to progressively construct a bijection
  -- large enough for all the references in a value.
  wken-≈ⱽ : ∀ {β β' τ} {v₁ v₂ : Value τ} → β ⊆ β' → v₁ ≈⟨ β  ⟩ⱽ v₂ → v₁ ≈⟨ β' ⟩ⱽ v₂
  wken-≈ⱽ β⊆β' (Valueᴸ ℓ⊑A r≈) = Valueᴸ ℓ⊑A (wken-≈ᴿ β⊆β' r≈)
  wken-≈ⱽ β⊆β' (Valueᴴ ℓ₁⋤A ℓ₂⋤A) = Valueᴴ ℓ₁⋤A ℓ₂⋤A

  wken-≈ᴱ : ∀ {β β' Γ} {θ₁ θ₂ : Env Γ} → β ⊆ β' → θ₁ ≈⟨ β  ⟩ᴱ θ₂ → θ₁ ≈⟨ β' ⟩ᴱ θ₂
  wken-≈ᴱ β⊆β' [] = []
  wken-≈ᴱ β⊆β' (≈ⱽ ∷ ≈ᴱ) = wken-≈ⱽ β⊆β' ≈ⱽ ∷ wken-≈ᴱ β⊆β' ≈ᴱ

  wken-≈ᴿ : ∀ {τ β β'} {r₁ r₂ : Raw τ} → β ⊆ β' → r₁ ≈⟨ β  ⟩ᴿ r₂ → r₁ ≈⟨ β' ⟩ᴿ r₂
  wken-≈ᴿ β⊆β' Unit = Unit
  wken-≈ᴿ β⊆β' (Lbl ℓ) = Lbl ℓ
  wken-≈ᴿ β⊆β' (Inl x) = Inl (wken-≈ⱽ β⊆β' x)
  wken-≈ᴿ β⊆β' (Inr x) = Inr (wken-≈ⱽ β⊆β' x)
  wken-≈ᴿ β⊆β' (Pair x y) = Pair (wken-≈ⱽ β⊆β' x) (wken-≈ⱽ β⊆β' y)
  wken-≈ᴿ β⊆β' (Fun x) = Fun (wken-≈ᴱ β⊆β' x)
  wken-≈ᴿ β⊆β' (Ref-Iᴸ ℓ⊑A ∈ᴮ) = Ref-Iᴸ ℓ⊑A (bij-⊆ β⊆β' ∈ᴮ)
  wken-≈ᴿ β⊆β' (Ref-Iᴴ ℓ₁⋤A ℓ₂⋤A) = Ref-Iᴴ ℓ₁⋤A ℓ₂⋤A
  wken-≈ᴿ β⊆β' (Ref-S ∈ᴮ) = Ref-S (bij-⊆ β⊆β' ∈ᴮ)
  wken-≈ᴿ β⊆β' (Id x) = Id (wken-≈ⱽ β⊆β' x)

--------------------------------------------------------------------------------

  -- Reflexive
  refl-≈ⱽ : ∀ {τ} (v : Value τ) → v ≈⟨ ι ∥ v ∥ⱽ ⟩ⱽ v
  refl-≈ⱽ (r ^ ℓ) with ℓ ⊑? A
  refl-≈ⱽ (r ^ ℓ) | yes ℓ⊑A = Valueᴸ ℓ⊑A (refl-≈ᴿ r)
  refl-≈ⱽ (r ^ ℓ) | no ℓ⋤A = Valueᴴ ℓ⋤A ℓ⋤A

  refl-≈ᴿ : ∀ {τ} (r : Raw τ) → r ≈⟨ ι ∥ r ∥ᴿ ⟩ᴿ r
  refl-≈ᴿ （） = Unit
  refl-≈ᴿ ⟨ x , θ ⟩ᶜ = Fun (refl-≈ᴱ θ)
  refl-≈ᴿ (inl v) = Inl (refl-≈ⱽ v)
  refl-≈ᴿ (inr v) = Inr (refl-≈ⱽ v)
  refl-≈ᴿ ⟨ v₁ , v₂ ⟩ = Pair ≈₁′ ≈₂′
    where ≈₁′ = wken-≈ⱽ (ι-⊆ (m≤m⊔n ∥ v₁ ∥ⱽ ∥ v₂ ∥ⱽ)) (refl-≈ⱽ v₁)
          ≈₂′ = wken-≈ⱽ (ι-⊆ (n≤m⊔n ∥ v₁ ∥ⱽ ∥ v₂ ∥ⱽ)) (refl-≈ⱽ v₂)
  refl-≈ᴿ (Refᴵ ℓ n) with ℓ ⊑? A
  ... | yes ℓ⊑A = Ref-Iᴸ ℓ⊑A (ι-∈ (s≤s ≤-refl))
  ... | no ℓ⋤A = Ref-Iᴴ ℓ⋤A ℓ⋤A
  refl-≈ᴿ (Refˢ n) = Ref-S (ι-∈ (s≤s ≤-refl))
  refl-≈ᴿ ⌞ ℓ ⌟ = Lbl ℓ
  refl-≈ᴿ (Id v) = Id (refl-≈ⱽ v)

  refl-≈ᴱ : ∀ {Γ} (θ : Env Γ) → θ ≈⟨ ι ∥ θ ∥ᴱ ⟩ᴱ θ
  refl-≈ᴱ [] = []
  refl-≈ᴱ (v ∷ θ) = ≈₁ ∷ ≈₂
    where ≈₁ = wken-≈ⱽ (ι-⊆ (m≤m⊔n ∥ v ∥ⱽ ∥ θ ∥ᴱ)) (refl-≈ⱽ v)
          ≈₂ = wken-≈ᴱ (ι-⊆ (n≤m⊔n ∥ v ∥ⱽ ∥ θ ∥ᴱ)) (refl-≈ᴱ θ)

----------------------------------------------------------------------------------

  -- Symmetric
  sym-≈ⱽ : ∀ {β τ} {v₁ v₂ : Value τ} → v₁ ≈⟨ β ⟩ⱽ v₂ → v₂ ≈⟨ β ⁻¹ ⟩ⱽ v₁
  sym-≈ⱽ (Valueᴸ ℓ⊑A r≈) = Valueᴸ ℓ⊑A (sym-≈ᴿ r≈)
  sym-≈ⱽ (Valueᴴ ℓ₁⋤A ℓ₂⋤A) = Valueᴴ ℓ₂⋤A ℓ₁⋤A

  sym-≈ᴿ : ∀ {β τ} {r₁ r₂ : Raw τ} → r₁ ≈⟨ β ⟩ᴿ r₂ → r₂ ≈⟨ β ⁻¹ ⟩ᴿ r₁
  sym-≈ᴿ Unit = Unit
  sym-≈ᴿ (Lbl ℓ) = Lbl ℓ
  sym-≈ᴿ (Inl x) = Inl (sym-≈ⱽ x)
  sym-≈ᴿ (Inr x) = Inr (sym-≈ⱽ x)
  sym-≈ᴿ (Pair x y) = Pair (sym-≈ⱽ x) (sym-≈ⱽ y)
  sym-≈ᴿ (Fun x) = Fun (sym-≈ᴱ x)
  sym-≈ᴿ {β = β} (Ref-Iᴸ ℓ⊑A x) = Ref-Iᴸ ℓ⊑A (Bijectionᴾ.right-inverse-of β x)
  sym-≈ᴿ (Ref-Iᴴ ℓ₁⋤A ℓ₂⋤A) = Ref-Iᴴ ℓ₂⋤A ℓ₁⋤A
  sym-≈ᴿ {β = β} (Ref-S x) = Ref-S (Bijectionᴾ.right-inverse-of β x)
  sym-≈ᴿ (Id x) = Id (sym-≈ⱽ x)

  sym-≈ᴱ : ∀ {β Γ} {θ₁ θ₂ : Env Γ} → θ₁ ≈⟨ β ⟩ᴱ θ₂ → θ₂ ≈⟨ β ⁻¹ ⟩ᴱ θ₁
  sym-≈ᴱ [] = []
  sym-≈ᴱ (≈ⱽ ∷ ≈ᴱ) = sym-≈ⱽ ≈ⱽ ∷ sym-≈ᴱ ≈ᴱ

  -- Transitive
  trans-≈ᴿ : ∀ {β₁ β₂ τ} {r₁ r₂ r₃ : Raw τ} →
               r₁ ≈⟨ β₁ ⟩ᴿ r₂ → r₂ ≈⟨ β₂ ⟩ᴿ r₃ → r₁ ≈⟨ β₂ ∘ᴮ β₁ ⟩ᴿ r₃
  trans-≈ᴿ Unit Unit = Unit
  trans-≈ᴿ (Lbl ℓ) (Lbl .ℓ) = Lbl ℓ
  trans-≈ᴿ (Inl x) (Inl y) = Inl (trans-≈ⱽ x y)
  trans-≈ᴿ (Inr x) (Inr y) = Inr (trans-≈ⱽ x y)
  trans-≈ᴿ (Pair x₁ y₁) (Pair x₂ y₂) = Pair (trans-≈ⱽ x₁ x₂) (trans-≈ⱽ y₁ y₂)
  trans-≈ᴿ (Fun x) (Fun y) = Fun (trans-≈ᴱ x y)
  trans-≈ᴿ {β₁ = β₁} {β₂} (Ref-Iᴸ ℓ⊑A x) (Ref-Iᴸ ℓ⊑A₁ y)
    = Ref-Iᴸ ℓ⊑A₁ (join-∈ᵗ {β₁ = β₁} {β₂} x y)
  trans-≈ᴿ (Ref-Iᴸ ℓ⊑A n) (Ref-Iᴴ ℓ₁⋤A ℓ₂⋤A) = ⊥-elim (ℓ₁⋤A ℓ⊑A)
  trans-≈ᴿ (Ref-Iᴴ ℓ₁⋤A ℓ₂⋤A) (Ref-Iᴸ ℓ⊑A n) = ⊥-elim (ℓ₂⋤A ℓ⊑A)
  trans-≈ᴿ (Ref-Iᴴ ℓ₁⋤A ℓ₂⋤A) (Ref-Iᴴ ℓ₁⋤A₁ ℓ₂⋤A₁) = Ref-Iᴴ ℓ₁⋤A ℓ₂⋤A₁
  trans-≈ᴿ {β₁ = β₁} {β₂} (Ref-S x) (Ref-S y)
    = Ref-S (join-∈ᵗ {β₁ = β₁} {β₂} x y)
  trans-≈ᴿ (Id x) (Id y) = Id (trans-≈ⱽ x y)

  trans-≈ⱽ : ∀ {β₁ β₂ τ} {v₁ v₂ v₃ : Value τ} →
               v₁ ≈⟨ β₁ ⟩ⱽ v₂ → v₂ ≈⟨ β₂ ⟩ⱽ v₃ → v₁ ≈⟨ β₂ ∘ᴮ β₁ ⟩ⱽ v₃
  trans-≈ⱽ (Valueᴸ ℓ⊑A r≈) (Valueᴸ ℓ⊑A₁ r≈₁) = Valueᴸ ℓ⊑A₁ (trans-≈ᴿ r≈ r≈₁)
  trans-≈ⱽ (Valueᴸ ℓ⊑A r≈) (Valueᴴ ℓ₁⋤A ℓ₂⋤A) = ⊥-elim (ℓ₁⋤A ℓ⊑A)
  trans-≈ⱽ (Valueᴴ ℓ₁⋤A ℓ₂⋤A) (Valueᴸ ℓ⊑A r≈) = ⊥-elim (ℓ₂⋤A ℓ⊑A)
  trans-≈ⱽ (Valueᴴ ℓ₁⋤A ℓ₂⋤A) (Valueᴴ ℓ₁⋤A₁ ℓ₂⋤A₁) = Valueᴴ ℓ₁⋤A ℓ₂⋤A₁

  trans-≈ᴱ : ∀ {β₁ β₂ Γ} {θ₁ θ₂ θ₃ : Env Γ} →
               θ₁ ≈⟨ β₁ ⟩ᴱ θ₂ → θ₂ ≈⟨ β₂ ⟩ᴱ θ₃ → θ₁ ≈⟨ β₂ ∘ᴮ β₁ ⟩ᴱ θ₃
  trans-≈ᴱ [] [] = []
  trans-≈ᴱ (≈ⱽ₁ ∷ ≈ᴱ₁) (≈ⱽ₂ ∷ ≈ᴱ₂) = trans-≈ⱽ ≈ⱽ₁ ≈ⱽ₂ ∷ trans-≈ᴱ ≈ᴱ₁ ≈ᴱ₂

--------------------------------------------------------------------------------

open import Generic.Bijection

-- Why do we need this?
𝑽 : IProps.IsEquivalenceᴮ Ty Value  _≈⟨_⟩ⱽ_
𝑽 = record { Dom = ∥_∥ⱽ
           ; reflᴮ = refl-≈ⱽ _
           ; wkenᴮ = wken-≈ⱽ
           ; symᴮ = sym-≈ⱽ
           ; transᴮ = trans-≈ⱽ }

𝑹 : IProps.IsEquivalenceᴮ Ty Raw  _≈⟨_⟩ᴿ_

𝑹 = record { Dom = ∥_∥ᴿ
           ; reflᴮ = refl-≈ᴿ _
           ; wkenᴮ = wken-≈ᴿ
           ; symᴮ = sym-≈ᴿ
           ; transᴮ = trans-≈ᴿ }

-- TODO: remove
  -- Make them instance of my own Equivalence bijection-indexed relation
-- instance
  -- ≈ᴿ-isEquivalence : ∀ {τ} → IsEquivalence (_≈ᴿ_ {τ})
  -- ≈ᴿ-isEquivalence = {!!} -- record { refl = ? refl-≈ᴿ ; sym = sym-≈ᴿ ; trans = trans-≈ᴿ }

--   ≈ⱽ-isEquivalence : ∀ {τ} → IsEquivalence (_≈ⱽ_ {τ})
--   ≈ⱽ-isEquivalence = record { refl = refl-≈ⱽ ; sym = sym-≈ⱽ ; trans = trans-≈ⱽ }

--   ≈ᴱ-isEquivalence : ∀ {Γ} → IsEquivalence (_≈ᴱ_ {Γ})
--   ≈ᴱ-isEquivalence = record { refl = refl-≈ᴱ ; sym = sym-≈ᴱ ; trans = trans-≈ᴱ }

--   ≡-isEquivalence : ∀ {A : Set} → IsEquivalence (_≡_ {_} {A})
--   ≡-isEquivalence = record { refl = refl ; sym = sym ; trans = trans }



-- It doesn't seem we use this. Let's leave it out for now.
-- refl-≈ᴬ : ∀ {A} {R : Relᴮ A} {{𝑹 : IsEquivalenceᴮ R}} {c} → c ≈⟨ R ⟩ᴬ c
-- refl-≈ᴬ {{𝑹}} {c = ⟨ _ , μ , _ ⟩} = ⟨ ι , {!!} , {!!} , {!refl-≈ᴬ!} ⟩ -- refl-≈ˢ , refl-≈ᴴ
--   where _≈ᴿ_ : ∀ {τ} → Raw τ → Raw τ → Set
--         _≈ᴿ_ = _≈⟨ ι′ ∥ μ ∥ᴴ ⟩ᴿ_

--         open IsEquivalenceᴮ 𝑹
--         open import Generic.Store.LowEq {Ty} {Raw} _≈ᴿ_ A
--         open Props {!!}

-- sym-≈ᴬ : ∀ {A} {R : A → A → Set} {{𝑹 : IsEquivalence R}} {c₁ c₂} →
--            c₁ ≈⟨ R ⟩ᴬ c₂ →
--            c₂ ≈⟨ R ⟩ᴬ c₁
-- sym-≈ᴬ {{𝑹}} ⟨ β , Σ≈ , μ≈ , t≈ ⟩ = ⟨ β ⁻¹ , sym-≈ˢ Σ≈ , sym-≈ᴴ {β = β} μ≈ , IsEquivalence.sym 𝑹 t≈  ⟩

-- trans-≈ᴬ : ∀ {A} {R : A → A → Set} {{𝑹 : IsEquivalence R}} {c₁ c₂ c₃} →
--              c₁ ≈⟨ R ⟩ᴬ c₂ →
--              c₂ ≈⟨ R ⟩ᴬ c₃ →
--              c₁ ≈⟨ R ⟩ᴬ c₃
-- trans-≈ᴬ {{𝑹 = 𝑹}} ⟨ β₁ , Σ≈₁ , μ≈₁ , t≈₁ ⟩ ⟨ β₂ , Σ≈₂ , μ≈₂ , t≈₂ ⟩
--   = ⟨ β₂ ∘ᴮ β₁ , trans-≈ˢ Σ≈₁ Σ≈₂ , trans-≈ᴴ {β₁ = β₁} {β₂ = β₂} μ≈₁ μ≈₂ , IsEquivalence.trans 𝑹 t≈₁ t≈₂ ⟩

-- instance
--   ≈ᴬ-IsEquivalence : ∀ {A} {R : A → A → Set} {{𝑹 : IsEquivalence R}}  → IsEquivalence _≈⟨ R ⟩ᴬ_
--   ≈ᴬ-IsEquivalence {{𝑹}} = record { refl = refl-≈ᴬ ; sym = sym-≈ᴬ ; trans = trans-≈ᴬ }

-- TODO: we probably need to make the bijection explicit in the relation.
-- Define the "Equivalence up to bijection" class.

-- TODO: fix the export here ...
open S.Props 𝑹 using (square-≈ˢ ; ∣_∣ˢ ; refl-≈ˢ ; trans-≈ˢ ; trans-≈ˢ-ι ; snoc-≈ˢ ; writeᴴ-≈ˢ ; square-≈ˢ-ι ; sym-≈ˢ ; newᴴ-≈ˢ ; newᴸ-≈ˢ ; ≈-# ) public
