-- remove indexes from bijection

{-# OPTIONS --allow-unsolved-metas #-}

-- This module defines a L-equivalence relation for all the categoris
-- of the calculus.  L-equivalence relates terms that are
-- indistinguishabile to an attacker at security level L.
--
-- This module is parametric in the security lattice 𝑳 = (𝓛, ⊑) and in
-- the attacker's security A ∈ 𝓛.

open import Lattice

module FG.LowEq {{𝑳 : Lattice}} (A : Label) where

open import FG.Types
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

mutual

  -- "Size" of a value
  ∣_∣ⱽ : ∀ {τ} → Value τ → ℕ
  ∣ r ^ ℓ ∣ⱽ = ∣ r ∣ᴿ

  ∣_∣ᴿ : ∀ {τ} → Raw τ → ℕ
  ∣ （） ∣ᴿ = 0
  ∣ ⟨ x , θ ⟩ᶜ ∣ᴿ = ∣ θ ∣ᴱ
  ∣ inl x ∣ᴿ = ∣ x ∣ⱽ
  ∣ inr x ∣ᴿ = ∣ x ∣ⱽ
  ∣ ⟨ x , y ⟩ ∣ᴿ = ∣ x ∣ⱽ ⊔ᴺ ∣ y ∣ⱽ
  ∣ Refᴵ x x₁ ∣ᴿ = 0
  ∣ Refˢ n ∣ᴿ = ℕ.suc n
  ∣ ⌞ x ⌟ ∣ᴿ = 0
  ∣ Id x ∣ᴿ = ∣ x ∣ⱽ

  ∣_∣ᴱ : ∀ {Γ} → Env Γ → ℕ
  ∣ [] ∣ᴱ = 0
  ∣ v ∷ θ ∣ᴱ = ∣ v ∣ⱽ ⊔ᴺ ∣ θ ∣ᴱ


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
    Ref-Iᴸ : ∀ {β} {ℓ τ} →
               (ℓ⊑A : ℓ ⊑ A) (n : ℕ) →
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

-- Shorthand
Ref-Iᴸ′ : ∀ {τ ℓ n₁ n₂} {β : Bij} → ℓ ⊑ A → n₁ ≡ n₂ → Refᴵ {τ = τ} ℓ n₁ ≈⟨ β ⟩ᴿ Refᴵ ℓ n₂
Ref-Iᴸ′ ℓ⊑A refl = Ref-Iᴸ ℓ⊑A _

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
-- open import Generic.Store.LowEq {Ty} {Raw} _≈ᴿ_ A as S using (_≈ˢ_) public
-- _≈⟨_⟩ˢ_ : Store → Bij → Store → Set
-- Σ₁ ≈⟨ β ⟩ˢ Σ₂ = Σ₁ ≈ˢ Σ₂
--   where open import Generic.Store.LowEq {Ty} {Raw} (λ r₁ r₂ → r₁ ≈⟨ β ⟩ᴿ r₂) A

-- -- Derive L-equivalence for heaps
-- _≈⟨_⟩ᴴ_ : ∀ (μ₁ : Heap) → Bij → (μ₂ : Heap) → Set
-- μ₁ ≈⟨ β ⟩ᴴ μ₂ = μ₁ H.≈⟨ β ⟩ᴴ μ₂
--   where open import Generic.Heap.LowEq {Ty} {Value} 𝑯 (λ v₁ v₂ → v₁ ≈⟨ β ⟩ⱽ v₂) A as H

-- --
-- -- using (_≈⟨_⟩ᴴ_ ; _≈ᴴ_ ; new-≈ᴴ ; Bij⟨_,_⟩)



-- -- -- Lift low-equivalence to configurations
-- open Conf

-- -- open import Generic.Bijection as B

-- record _≈⟨_⟩ᴬ_ {V : Set} (c₁ : Conf V) (R : V → Bij → V → Set) (c₂ : Conf V) : Set where
--   constructor ⟨_,_,_⟩
--   field
--     bij : Bij
--     store-≈ˢ : store c₁ ≈⟨ bij ⟩ˢ store c₂
--     heap-≈ᴴ : heap c₁ ≈⟨ bij ⟩ᴴ heap c₂
--     term-≈ : R (term c₁) bij (term c₂)

-- -- open _≈⟨_⟩ᴬ_ {{ ... }}

-- -- L-Equivalence for initial configurations.  For terms we do not use
-- -- the bijection but simply require syntactic equivalence.
-- _≈ᴵ_ : ∀ {Γ τ} → IConf Γ τ → IConf Γ τ → Set
-- _≈ᴵ_ = _≈⟨ (λ e₁ β e₂ → e₁ ≡ e₂) ⟩ᴬ_

-- -- Final configurations.
-- _≈ᶜ_ : ∀ {τ} → FConf τ → FConf τ → Set
-- _≈ᶜ_ = _≈⟨ _≈⟨_⟩ⱽ_ ⟩ᴬ_

--------------------------------------------------------------------------------
-- Properties: L-equivalence is an equivalence relation.

mutual

  -- Weaken the identity bijection to progressively construct a bijection
  -- large enough for all the references in a value.
  wken-≈ⱽ : ∀ {n m τ} {v : Value τ} → n ≤ m → v ≈⟨ ι n  ⟩ⱽ v → v ≈⟨ ι m ⟩ⱽ v
  wken-≈ⱽ n≤m (Valueᴸ ℓ⊑A r≈) = Valueᴸ ℓ⊑A (wken-≈ᴿ n≤m r≈)
  wken-≈ⱽ n≤m (Valueᴴ ℓ₁⋤A ℓ₂⋤A) = Valueᴴ ℓ₂⋤A ℓ₂⋤A

  wken-≈ᴱ : ∀ {n m Γ} {θ : Env Γ} → n ≤ m → θ ≈⟨ ι n  ⟩ᴱ θ → θ ≈⟨ ι m ⟩ᴱ θ
  wken-≈ᴱ n≤m [] = []
  wken-≈ᴱ n≤m (≈ⱽ ∷ ≈ᴱ) = wken-≈ⱽ n≤m ≈ⱽ ∷ wken-≈ᴱ n≤m ≈ᴱ

  wken-≈ᴿ : ∀ {τ n m} {r : Raw τ} → n ≤ m → r ≈⟨ ι n  ⟩ᴿ r → r ≈⟨ ι m ⟩ᴿ r
  wken-≈ᴿ n≤m Unit = Unit
  wken-≈ᴿ n≤m (Lbl ℓ) = Lbl ℓ
  wken-≈ᴿ n≤m (Inl x) = Inl (wken-≈ⱽ n≤m x)
  wken-≈ᴿ n≤m (Inr x) = Inr (wken-≈ⱽ n≤m x)
  wken-≈ᴿ n≤m (Pair x y) = Pair (wken-≈ⱽ n≤m x) (wken-≈ⱽ n≤m y)
  wken-≈ᴿ n≤m (Fun x) = Fun (wken-≈ᴱ n≤m x)
  wken-≈ᴿ n≤m (Ref-Iᴸ ℓ⊑A n) = Ref-Iᴸ ℓ⊑A n
  wken-≈ᴿ n≤m (Ref-Iᴴ ℓ₁⋤A ℓ₂⋤A) = Ref-Iᴴ ℓ₂⋤A ℓ₂⋤A
  wken-≈ᴿ n≤m (Ref-S ∈ᴮ) = Ref-S (ι-∈ (≤-trans (ι-≤ᴰ ∈ᴮ) n≤m))
  wken-≈ᴿ n≤m (Id x) = Id (wken-≈ⱽ n≤m x)

--------------------------------------------------------------------------------

  -- Reflexive
  refl-≈ⱽ : ∀ {τ} (v : Value τ) → v ≈⟨ ι ∣ v ∣ⱽ ⟩ⱽ v
  refl-≈ⱽ (r ^ ℓ) with ℓ ⊑? A
  refl-≈ⱽ (r ^ ℓ) | yes ℓ⊑A = Valueᴸ ℓ⊑A (refl-≈ᴿ r)
  refl-≈ⱽ (r ^ ℓ) | no ℓ⋤A = Valueᴴ ℓ⋤A ℓ⋤A

  refl-≈ᴿ : ∀ {τ} (r : Raw τ) → r ≈⟨ ι ∣ r ∣ᴿ ⟩ᴿ r
  refl-≈ᴿ （） = Unit
  refl-≈ᴿ ⟨ x , θ ⟩ᶜ = Fun (refl-≈ᴱ θ)
  refl-≈ᴿ (inl v) = Inl (refl-≈ⱽ v)
  refl-≈ᴿ (inr v) = Inr (refl-≈ⱽ v)
  refl-≈ᴿ ⟨ v₁ , v₂ ⟩ = Pair ≈₁′ ≈₂′
    where ≈₁′ = wken-≈ⱽ (m≤m⊔n ∣ v₁ ∣ⱽ ∣ v₂ ∣ⱽ) (refl-≈ⱽ v₁)
          ≈₂′ = wken-≈ⱽ (n≤m⊔n ∣ v₁ ∣ⱽ ∣ v₂ ∣ⱽ) (refl-≈ⱽ v₂)
  refl-≈ᴿ (Refᴵ ℓ n) with ℓ ⊑? A
  ... | yes ℓ⊑A = Ref-Iᴸ ℓ⊑A n
  ... | no ℓ⋤A = Ref-Iᴴ ℓ⋤A ℓ⋤A
  refl-≈ᴿ (Refˢ n) = Ref-S (ι-∈ (s≤s ≤-refl))
  refl-≈ᴿ ⌞ ℓ ⌟ = Lbl ℓ
  refl-≈ᴿ (Id v) = Id (refl-≈ⱽ v)

  refl-≈ᴱ : ∀ {Γ} (θ : Env Γ) → θ ≈⟨ ι ∣ θ ∣ᴱ ⟩ᴱ θ
  refl-≈ᴱ [] = []
  refl-≈ᴱ (v ∷ θ) = ≈₁ ∷ ≈₂
    where ≈₁ = wken-≈ⱽ (m≤m⊔n ∣ v ∣ⱽ ∣ θ ∣ᴱ) (refl-≈ⱽ v)
          ≈₂ = wken-≈ᴱ (n≤m⊔n ∣ v ∣ⱽ ∣ θ ∣ᴱ) (refl-≈ᴱ θ)

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
  sym-≈ᴿ (Ref-Iᴸ ℓ⊑A n) = Ref-Iᴸ ℓ⊑A n
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
  trans-≈ᴿ (Ref-Iᴸ ℓ⊑A n) (Ref-Iᴸ ℓ⊑A₁ .n) = Ref-Iᴸ ℓ⊑A₁ n
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
-- Do we even use these instances?

-- Why do we need this?
-- 𝑹 : ∀ {τ} → IsEquivalenceᴮ {A = Value τ}  _≈⟨_⟩ⱽ_
-- 𝑹 = record { Dom = ∣_∣ⱽ ; reflᴮ = refl-≈ⱽ _ ; symᴮ = sym-≈ⱽ ; transᴮ = trans-≈ⱽ }

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


-- open H.Props ≈ⱽ-isEquivalence public


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

-- open import Generic.Heap.LowEq {Ty} {Value} 𝑯 (λ v₁ v₂ → v₁ ≈⟨ {!!} ⟩ⱽ v₂) A as H
-- open Props {!!}
