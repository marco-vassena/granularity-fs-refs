-- {-# OPTIONS --allow-unsolved-metas #-}

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
open import Data.Nat using (ℕ ; _≤_ ; _<_) renaming (_⊔_ to _⊔ᴺ_)
open import Data.Nat.Properties
open import Data.Fin hiding (_≤_ ; _<_)
open import Function as F
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Generic.Bijection renaming (_∘_ to _∘ᴮ_)
open import Data.Product renaming (_,_ to ⟨_,_⟩)

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

  data _≈⟨_⟩ⱽ_ {τ n m} : Value τ → Bij n m → Value τ → Set where
    Valueᴸ : ∀ {r₁ r₂ ℓ β} → (ℓ⊑A : ℓ ⊑ A) (r≈ : r₁ ≈⟨ β ⟩ᴿ r₂) → (r₁ ^ ℓ) ≈⟨ β ⟩ⱽ (r₂ ^ ℓ)
    Valueᴴ : ∀ {r₁ r₂ ℓ₁ ℓ₂ β} → (ℓ₁⋤A : ℓ₁ ⋤ A) (ℓ₂⋤A : ℓ₂ ⋤ A) → (r₁ ^ ℓ₁) ≈⟨ β ⟩ⱽ (r₂ ^ ℓ₂)

  -- _≈⟨_⟩ⱽ_ : ∀ {τ n m} → Value τ → Bij n m → Value τ → Set
  -- v₁ ≈⟨ β ⟩ⱽ v₂ = Value-≈ β v₁ v₂

  -- Raw values
  data _≈⟨_⟩ᴿ_ : ∀ {τ n m} → Raw τ → Bij n m → Raw τ → Set where

    Unit : ∀ {n m} {β : Bij n m} → （） ≈⟨ β ⟩ᴿ （）

    Lbl : ∀ {n m} {β : Bij n m} ℓ → ⌞ ℓ ⌟ ≈⟨ β ⟩ᴿ ⌞ ℓ ⌟

    Inl : ∀ {n m} {β : Bij n m} {τ₁ τ₂} {v₁ v₂ : Value τ₁} →
          v₁ ≈⟨ β ⟩ⱽ v₂ →
          inl {τ₂ = τ₂} v₁ ≈⟨ β ⟩ᴿ inl v₂

    Inr : ∀ {n m} {β : Bij n m} {τ₁ τ₂} {v₁ v₂ : Value τ₂} →
            v₁ ≈⟨ β ⟩ⱽ v₂ →
            inr {τ₁ = τ₁} v₁ ≈⟨ β ⟩ᴿ inr v₂

    Pair : ∀ {n m} {β : Bij n m} {τ₁ τ₂} {v₁ v₁' : Value τ₁} {v₂ v₂' : Value τ₂} →
             v₁ ≈⟨ β ⟩ⱽ v₁' →
             v₂ ≈⟨ β ⟩ⱽ v₂' →
             ⟨ v₁ , v₂ ⟩  ≈⟨ β ⟩ᴿ ⟨ v₁' , v₂' ⟩

    Fun : ∀ {n m} {β : Bij n m} {τ' τ Γ} {e : Expr (τ' ∷ Γ) τ}
            {θ₁ : Env Γ} {θ₂ : Env Γ} →
            θ₁ ≈⟨ β ⟩ᴱ θ₂ →
            ⟨ e , θ₁ ⟩ᶜ ≈⟨ β ⟩ᴿ ⟨ e , θ₂ ⟩ᶜ

    -- Flow-insensitive refs
    Ref-Iᴸ : ∀ {n m} {β : Bij n m} {ℓ τ} →
               (ℓ⊑A : ℓ ⊑ A) (n : ℕ) →
               Refᴵ {τ = τ} ℓ n ≈⟨ β ⟩ᴿ Refᴵ ℓ n

    Ref-Iᴴ : ∀ {n m} {β : Bij n m} {ℓ₁ ℓ₂ n₁ n₂ τ} →
               (ℓ₁⋤A : ℓ₁ ⋤ A) (ℓ₂⋤A : ℓ₂ ⋤ A) →
               Refᴵ {τ = τ} ℓ₁ n₁ ≈⟨ β ⟩ᴿ Refᴵ ℓ₂ n₂

    -- Flow-sensitive refs
    Ref-S : ∀ {τ n m n' m'} {β : Bij n' m'} →
              (n<n' : n < n') (m<m' : m < m') →
              ⟨ fromℕ≤ n<n' , fromℕ≤ m<m' ⟩ ∈ᵗ β →
              Refˢ {τ = τ} n ≈⟨ β ⟩ᴿ Refˢ m

    Id : ∀ {n m} {β : Bij n m} {τ} {v₁ v₂ : Value τ} →
           v₁ ≈⟨ β ⟩ⱽ v₂ →
           Id v₁ ≈⟨ β ⟩ᴿ Id v₂

  -- Environments.
  data _≈⟨_⟩ᴱ_  {n m} : ∀ {Γ} → Env Γ → Bij n m → Env Γ → Set where
    [] : ∀ {β} → [] ≈⟨ β ⟩ᴱ []
    _∷_ : ∀ {τ Γ β} {v₁ v₂ : Value τ} {θ₁ θ₂ : Env Γ} →
             (≈ⱽ : v₁ ≈⟨ β ⟩ⱽ v₂) →
             (≈ᴱ : θ₁ ≈⟨ β ⟩ᴱ θ₂) →
             (v₁ ∷ θ₁) ≈⟨ β ⟩ᴱ (v₂ ∷ θ₂)

  --------------------------------------------------------------------------------
  -- TODO: remove old definitions.

  -- Values
  data _≈ⱽ_ {τ} : Value τ → Value τ → Set where
    Valueᴸ : ∀ {r₁ r₂ ℓ} → (ℓ⊑A : ℓ ⊑ A) (r≈ : r₁ ≈ᴿ r₂) → (r₁ ^ ℓ) ≈ⱽ (r₂ ^ ℓ)
    Valueᴴ : ∀ {r₁ r₂ ℓ₁ ℓ₂} → (ℓ₁⋤A : ℓ₁ ⋤ A) (ℓ₂⋤A : ℓ₂ ⋤ A) → (r₁ ^ ℓ₁) ≈ⱽ (r₂ ^ ℓ₂)

  -- Raw values
  data _≈ᴿ_ : ∀ {τ} → Raw τ → Raw τ → Set where
    Unit : （） ≈ᴿ （）
    Lbl : ∀ ℓ → ⌞ ℓ ⌟ ≈ᴿ ⌞ ℓ ⌟
    Inl : ∀ {τ₁ τ₂} {v₁ v₂ : Value τ₁} → v₁ ≈ⱽ v₂ → inl {τ₂ = τ₂} v₁ ≈ᴿ inl v₂
    Inr : ∀ {τ₁ τ₂} {v₁ v₂ : Value τ₂} → v₁ ≈ⱽ v₂ → inr {τ₁ = τ₁} v₁ ≈ᴿ inr v₂
    Pair : ∀ {τ₁ τ₂} {v₁ v₁' : Value τ₁} {v₂ v₂' : Value τ₂} →
             v₁ ≈ⱽ v₁' →
             v₂ ≈ⱽ v₂' →
             ⟨ v₁ , v₂ ⟩  ≈ᴿ ⟨ v₁' , v₂' ⟩

    Fun : ∀ {τ' τ Γ} {e : Expr (τ' ∷ Γ) τ} {θ₁ : Env Γ} {θ₂ : Env Γ} →
                θ₁ ≈ᴱ θ₂ →
                ⟨ e , θ₁ ⟩ᶜ ≈ᴿ ⟨ e , θ₂ ⟩ᶜ

    -- Flow-insensitive refs
    Ref-Iᴸ : ∀ {ℓ τ} → (ℓ⊑A : ℓ ⊑ A) (n : ℕ) → Refᴵ {τ = τ} ℓ n ≈ᴿ Refᴵ ℓ n
    Ref-Iᴴ : ∀ {ℓ₁ ℓ₂ n₁ n₂ τ} → (ℓ₁⋤A : ℓ₁ ⋤ A) (ℓ₂⋤A : ℓ₂ ⋤ A) → Refᴵ {τ = τ} ℓ₁ n₁ ≈ᴿ Refᴵ ℓ₂ n₂

    -- Flow-sensitive refs
    Ref-S : ∀ {n₁ n₂ τ} → Refˢ {τ = τ} n₁ ≈ᴿ Refˢ n₂

    Id : ∀ {τ} {v₁ v₂ : Value τ} → v₁ ≈ⱽ v₂ → Id v₁ ≈ᴿ Id v₂

  -- Environments.
  data _≈ᴱ_  : ∀ {Γ} → Env Γ → Env Γ → Set where
    [] : [] ≈ᴱ []
    _∷_ : ∀ {τ Γ} {v₁ v₂ : Value τ} {θ₁ θ₂ : Env Γ} →
             v₁ ≈ⱽ v₂ → θ₁ ≈ᴱ θ₂ → (v₁ ∷ θ₁) ≈ᴱ (v₂ ∷ θ₂)

-- Shorthand
Ref-Iᴸ′ : ∀ {τ ℓ n₁ n₂} → ℓ ⊑ A → n₁ ≡ n₂ → Refᴵ {τ = τ} ℓ n₁ ≈ᴿ Refᴵ ℓ n₂
Ref-Iᴸ′ ℓ⊑A refl = Ref-Iᴸ ℓ⊑A _

Trueᴸ : ∀ {ℓ} → ℓ ⊑ A → true ℓ ≈ᴿ true ℓ
Trueᴸ ℓ⊑A = Inl (Valueᴸ ℓ⊑A Unit)

Falseᴸ : ∀ {ℓ} → ℓ ⊑ A → false ℓ ≈ᴿ false ℓ
Falseᴸ ℓ⊑A = Inr (Valueᴸ ℓ⊑A Unit)

-- Lemma
≈ⱽ-⊑ : ∀ {τ} {v₁ v₂ : Value τ} (pc : Label) →
         let r₁ ^ ℓ₁ = v₁
             r₂ ^ ℓ₂ = v₂ in
             v₁ ≈ⱽ v₂ → (r₁ ^ (pc ⊔ ℓ₁)) ≈ⱽ (r₂ ^ (pc ⊔ ℓ₂))
≈ⱽ-⊑ {v₁ = r₁ ^ ℓ} pc (Valueᴸ x x₁) with (pc ⊔ ℓ) ⊑? A
... | yes p = Valueᴸ p x₁
... | no ¬p = Valueᴴ ¬p ¬p
≈ⱽ-⊑ pc (Valueᴴ x x₁) = Valueᴴ (trans-⋤ (join-⊑₂ _ _) x) (trans-⋤ (join-⊑₂ _ _) x₁)


-- Derive L-equivalence for stores,
open import Generic.Store.LowEq {Ty} {Raw} _≈ᴿ_ A as S using (_≈ˢ_) public

-- Derive L-equivalence for heaps
open import Generic.Heap.LowEq {Ty} {Value} 𝑯 _≈ⱽ_ A as H using (_≈⟨_⟩ᴴ_ ; _≈ᴴ_ ; new-≈ᴴ ; Bij⟨_,_⟩)

-- Lift low-equivalence to configurations
open Conf

open import Generic.Bijection as B

record _≈⟨_⟩ᴬ_ {B : Set} (c₁ : Conf B) (R : B → B → Set) (c₂ : Conf B) : Set where
  constructor ⟨_,_,_,_⟩
  field
    bij : Bij ∥ heap c₁ ∥ᴴ ∥ heap c₂ ∥ᴴ
    store-≈ˢ : store c₁ ≈ˢ store c₂
    heap-≈ᴴ : heap c₁ ≈⟨ bij ⟩ᴴ heap c₂
    term-≈ : R (term c₁) (term c₂)

open _≈⟨_⟩ᴬ_ {{ ... }}

-- Initial configurations
_≈ᴵ_ : ∀ {Γ τ} → IConf Γ τ → IConf Γ τ → Set
_≈ᴵ_ = _≈⟨ _≡_ ⟩ᴬ_

-- Final configurations.
_≈ᶜ_ : ∀ {τ} → FConf τ → FConf τ → Set
_≈ᶜ_ = _≈⟨ _≈ⱽ_ ⟩ᴬ_

--------------------------------------------------------------------------------
-- Properties: L-equivalence is an equivalence relation.

-- For testing, remove
postulate lift-≈ⱽ : ∀ {τ n m} {v : Value τ} → v ≈ⱽ v → (β : Bij n m) → v ≈⟨ β ⟩ⱽ v
postulate unlift-≈ᴿ : ∀ {τ n m} {r₁ r₂ : Raw τ} (β : Bij n m) → r₁ ≈⟨ β ⟩ᴿ r₂ → r₁ ≈ᴿ r₂

mutual

  -- Weaken the identity bijection to progressively construct a bijection
  -- large enough for all the references in a value.
  wken-≈ⱽ : ∀ {n m τ} {v : Value τ} → n ≤ m → v ≈⟨ ι′ n  ⟩ⱽ v → v ≈⟨ ι′ m ⟩ⱽ v
  wken-≈ⱽ n≤m (Valueᴸ ℓ⊑A r≈) = Valueᴸ ℓ⊑A (wken-≈ᴿ n≤m r≈)
  wken-≈ⱽ n≤m (Valueᴴ ℓ₁⋤A ℓ₂⋤A) = Valueᴴ ℓ₂⋤A ℓ₂⋤A

  wken-≈ᴱ : ∀ {n m Γ} {θ : Env Γ} → n ≤ m → θ ≈⟨ ι′ n  ⟩ᴱ θ → θ ≈⟨ ι′ m ⟩ᴱ θ
  wken-≈ᴱ n≤m [] = []
  wken-≈ᴱ n≤m (≈ⱽ ∷ ≈ᴱ) = wken-≈ⱽ n≤m ≈ⱽ ∷ wken-≈ᴱ n≤m ≈ᴱ

  wken-≈ᴿ : ∀ {τ n m} {r : Raw τ} → n ≤ m → r ≈⟨ ι′ n  ⟩ᴿ r → r ≈⟨ ι′ m ⟩ᴿ r
  wken-≈ᴿ n≤m Unit = Unit
  wken-≈ᴿ n≤m (Lbl ℓ) = Lbl ℓ
  wken-≈ᴿ n≤m (Inl x) = Inl (wken-≈ⱽ n≤m x)
  wken-≈ᴿ n≤m (Inr x) = Inr (wken-≈ⱽ n≤m x)
  wken-≈ᴿ n≤m (Pair x y) = Pair (wken-≈ⱽ n≤m x) (wken-≈ⱽ n≤m y)
  wken-≈ᴿ n≤m (Fun x) = Fun (wken-≈ᴱ n≤m x)
  wken-≈ᴿ n≤m (Ref-Iᴸ ℓ⊑A n) = Ref-Iᴸ ℓ⊑A n
  wken-≈ᴿ n≤m (Ref-Iᴴ ℓ₁⋤A ℓ₂⋤A) = Ref-Iᴴ ℓ₂⋤A ℓ₂⋤A
  wken-≈ᴿ n≤m (Ref-S n< m< x) with ≤-irrelevance n< m<
  ... | refl = Ref-S (≤-trans n< n≤m) (≤-trans m< n≤m) refl
  wken-≈ᴿ n≤m (Id x) = Id (wken-≈ⱽ n≤m x)

  -- Reflexive
  refl-≈ⱽ′ : ∀ {τ} (v : Value τ) → ∃ (λ n → v ≈⟨ ι′ n ⟩ⱽ v)
  refl-≈ⱽ′ (r ^ ℓ) with ℓ ⊑? A
  refl-≈ⱽ′ (r ^ ℓ) | yes ℓ⊑A = map F.id (Valueᴸ ℓ⊑A) (refl-≈ᴿ′ r)
  refl-≈ⱽ′ (r ^ ℓ) | no ℓ⋤A = ⟨ 0 , Valueᴴ ℓ⋤A ℓ⋤A ⟩

  refl-≈ᴿ′ : ∀ {τ} (r : Raw τ) → ∃ (λ n → r ≈⟨ ι′ n ⟩ᴿ r)
  refl-≈ᴿ′ （） = ⟨ 0 , Unit ⟩
  refl-≈ᴿ′ ⟨ x , θ ⟩ᶜ = map F.id Fun (refl-≈ᴱ′ θ)
  refl-≈ᴿ′ (inl v) = map F.id Inl (refl-≈ⱽ′ v)
  refl-≈ᴿ′ (inr v) = map F.id Inr (refl-≈ⱽ′ v)
  refl-≈ᴿ′ ⟨ v₁ , v₂ ⟩ with refl-≈ⱽ′ v₁ |  refl-≈ⱽ′ v₂
  ... | ⟨ n₁ , ≈₁ ⟩ | ⟨ n₂ , ≈₂ ⟩ =
    let ≈₁′ = wken-≈ⱽ (m≤m⊔n n₁ n₂) ≈₁
        ≈₂′ = wken-≈ⱽ (n≤m⊔n n₁ n₂) ≈₂
    in ⟨ n₁ ⊔ᴺ n₂ , Pair ≈₁′ ≈₂′ ⟩
  refl-≈ᴿ′ (Refᴵ ℓ n) with ℓ ⊑? A
  ... | yes ℓ⊑A = ⟨ 0 , Ref-Iᴸ ℓ⊑A n ⟩
  ... | no ℓ⋤A = ⟨ 0 , Ref-Iᴴ ℓ⋤A ℓ⋤A ⟩
  refl-≈ᴿ′ (Refˢ n) = ⟨ ℕ.suc n , Ref-S ≤-refl ≤-refl refl ⟩
  refl-≈ᴿ′ ⌞ ℓ ⌟ = ⟨ 0 , Lbl ℓ ⟩
  refl-≈ᴿ′ (Id v) = map F.id Id (refl-≈ⱽ′ v)

  refl-≈ᴱ′ : ∀ {Γ} (θ : Env Γ) → ∃ (λ n → θ ≈⟨ ι′ n ⟩ᴱ θ)
  refl-≈ᴱ′ [] = ⟨ 0 , [] ⟩
  refl-≈ᴱ′ (v ∷ θ) with refl-≈ⱽ′ v | refl-≈ᴱ′ θ
  ... | ⟨ n₁ , ≈ⱽ ⟩ | ⟨ n₂ , ≈ᴱ ⟩ =
    let ≈₁′ = wken-≈ⱽ (m≤m⊔n n₁ n₂) ≈ⱽ
        ≈₂′ = wken-≈ᴱ (n≤m⊔n n₁ n₂) ≈ᴱ
    in ⟨ n₁ ⊔ᴺ n₂ , ≈₁′ ∷ ≈₂′ ⟩

  -- Symmetric
  sym-≈ⱽ′ : ∀ {n m τ} {v₁ v₂ : Value τ} {β : Bij n m} → v₁ ≈⟨ β ⟩ⱽ v₂ → v₂ ≈⟨ β ⁻¹ ⟩ⱽ v₁
  sym-≈ⱽ′ (Valueᴸ ℓ⊑A r≈) = Valueᴸ ℓ⊑A (sym-≈ᴿ′ r≈)
  sym-≈ⱽ′ (Valueᴴ ℓ₁⋤A ℓ₂⋤A) = Valueᴴ ℓ₂⋤A ℓ₁⋤A

  sym-≈ᴿ′ : ∀ {n m τ} {r₁ r₂ : Raw τ} {β : Bij n m} → r₁ ≈⟨ β ⟩ᴿ r₂ → r₂ ≈⟨ β ⁻¹ ⟩ᴿ r₁
  sym-≈ᴿ′ Unit = Unit
  sym-≈ᴿ′ (Lbl ℓ) = Lbl ℓ
  sym-≈ᴿ′ (Inl x) = Inl (sym-≈ⱽ′ x)
  sym-≈ᴿ′ (Inr x) = Inr (sym-≈ⱽ′ x)
  sym-≈ᴿ′ (Pair x y) = Pair (sym-≈ⱽ′ x) (sym-≈ⱽ′ y)
  sym-≈ᴿ′ (Fun x) = Fun (sym-≈ᴱ′ x)
  sym-≈ᴿ′ (Ref-Iᴸ ℓ⊑A n) = Ref-Iᴸ ℓ⊑A n
  sym-≈ᴿ′ (Ref-Iᴴ ℓ₁⋤A ℓ₂⋤A) = Ref-Iᴴ ℓ₂⋤A ℓ₁⋤A
  sym-≈ᴿ′ {β = β} (Ref-S n<n' m<m' x) = Ref-S m<m' n<n' (Bijectionᴾ.right-inverse-of β x)
  sym-≈ᴿ′ (Id x) = Id (sym-≈ⱽ′ x)

  sym-≈ᴱ′ : ∀ {n m Γ} {θ₁ θ₂ : Env Γ} {β : Bij n m} → θ₁ ≈⟨ β ⟩ᴱ θ₂ → θ₂ ≈⟨ β ⁻¹ ⟩ᴱ θ₁
  sym-≈ᴱ′ [] = []
  sym-≈ᴱ′ (≈ⱽ ∷ ≈ᴱ) = sym-≈ⱽ′ ≈ⱽ ∷ sym-≈ᴱ′ ≈ᴱ

  -- Transitive
  trans-≈ᴿ′ : ∀ {n₁ n₂ n₃ τ} {β₁ : Bij n₁ n₂} {β₂ : Bij n₂ n₃} {r₁ r₂ r₃ : Raw τ} →
               r₁ ≈⟨ β₁ ⟩ᴿ r₂ → r₂ ≈⟨ β₂ ⟩ᴿ r₃ → r₁ ≈⟨ β₂ ∘ᴮ β₁ ⟩ᴿ r₃
  trans-≈ᴿ′ Unit Unit = Unit
  trans-≈ᴿ′ (Lbl ℓ) (Lbl .ℓ) = Lbl ℓ
  trans-≈ᴿ′ (Inl x) (Inl y) = Inl (trans-≈ⱽ′ x y)
  trans-≈ᴿ′ (Inr x) (Inr y) = Inr (trans-≈ⱽ′ x y)
  trans-≈ᴿ′ (Pair x₁ y₁) (Pair x₂ y₂) = Pair (trans-≈ⱽ′ x₁ x₂) (trans-≈ⱽ′ y₁ y₂)
  trans-≈ᴿ′ (Fun x) (Fun y) = Fun (trans-≈ᴱ′ x y)
  trans-≈ᴿ′ (Ref-Iᴸ ℓ⊑A n) (Ref-Iᴸ ℓ⊑A₁ .n) = Ref-Iᴸ ℓ⊑A₁ n
  trans-≈ᴿ′ (Ref-Iᴸ ℓ⊑A n) (Ref-Iᴴ ℓ₁⋤A ℓ₂⋤A) = ⊥-elim (ℓ₁⋤A ℓ⊑A)
  trans-≈ᴿ′ (Ref-Iᴴ ℓ₁⋤A ℓ₂⋤A) (Ref-Iᴸ ℓ⊑A n) = ⊥-elim (ℓ₂⋤A ℓ⊑A)
  trans-≈ᴿ′ (Ref-Iᴴ ℓ₁⋤A ℓ₂⋤A) (Ref-Iᴴ ℓ₁⋤A₁ ℓ₂⋤A₁) = Ref-Iᴴ ℓ₁⋤A ℓ₂⋤A₁
  trans-≈ᴿ′ {β₁ = β₁} {β₂} (Ref-S n<n' m<m' x) (Ref-S n<n'' m<m'' y)
    rewrite ≤-irrelevance m<m' n<n'' = Ref-S n<n' m<m'' (join-∈ᵗ {β₁ = β₁} {β₂} x y)
  trans-≈ᴿ′ (Id x) (Id y) = Id (trans-≈ⱽ′ x y)

  trans-≈ⱽ′ : ∀ {n₁ n₂ n₃ τ} {β₁ : Bij n₁ n₂} {β₂ : Bij n₂ n₃} {v₁ v₂ v₃ : Value τ} →
               v₁ ≈⟨ β₁ ⟩ⱽ v₂ → v₂ ≈⟨ β₂ ⟩ⱽ v₃ → v₁ ≈⟨ β₂ ∘ᴮ β₁ ⟩ⱽ v₃
  trans-≈ⱽ′ (Valueᴸ ℓ⊑A r≈) (Valueᴸ ℓ⊑A₁ r≈₁) = Valueᴸ ℓ⊑A₁ (trans-≈ᴿ′ r≈ r≈₁)
  trans-≈ⱽ′ (Valueᴸ ℓ⊑A r≈) (Valueᴴ ℓ₁⋤A ℓ₂⋤A) = ⊥-elim (ℓ₁⋤A ℓ⊑A)
  trans-≈ⱽ′ (Valueᴴ ℓ₁⋤A ℓ₂⋤A) (Valueᴸ ℓ⊑A r≈) = ⊥-elim (ℓ₂⋤A ℓ⊑A)
  trans-≈ⱽ′ (Valueᴴ ℓ₁⋤A ℓ₂⋤A) (Valueᴴ ℓ₁⋤A₁ ℓ₂⋤A₁) = Valueᴴ ℓ₁⋤A ℓ₂⋤A₁

  trans-≈ᴱ′ : ∀ {n₁ n₂ n₃ Γ} {β₁ : Bij n₁ n₂} {β₂ : Bij n₂ n₃} {θ₁ θ₂ θ₃ : Env Γ} →
               θ₁ ≈⟨ β₁ ⟩ᴱ θ₂ → θ₂ ≈⟨ β₂ ⟩ᴱ θ₃ → θ₁ ≈⟨ β₂ ∘ᴮ β₁ ⟩ᴱ θ₃
  trans-≈ᴱ′ [] [] = []
  trans-≈ᴱ′ (≈ⱽ₁ ∷ ≈ᴱ₁) (≈ⱽ₂ ∷ ≈ᴱ₂) = trans-≈ⱽ′ ≈ⱽ₁ ≈ⱽ₂ ∷ trans-≈ᴱ′ ≈ᴱ₁ ≈ᴱ₂

  -- Symmetric
  sym-≈ⱽ : ∀ {τ} {v₁ v₂ : Value τ} → v₁ ≈ⱽ v₂ → v₂ ≈ⱽ v₁
  sym-≈ⱽ (Valueᴸ ℓ⊑A r≈) = Valueᴸ ℓ⊑A (sym-≈ᴿ r≈)
  sym-≈ⱽ (Valueᴴ ℓ₁⋤A ℓ₂⋤A) = Valueᴴ ℓ₂⋤A ℓ₁⋤A

  postulate sym-≈ᴿ : ∀ {τ} {r₁ r₂ : Raw τ} → r₁ ≈ᴿ r₂ → r₂ ≈ᴿ r₁
  -- sym-≈ᴿ Unit = Unit
  -- sym-≈ᴿ (Lbl ℓ) = Lbl ℓ
  -- sym-≈ᴿ (Inl v₁≈v₂) = Inl (sym-≈ⱽ v₁≈v₂)
  -- sym-≈ᴿ (Inr v₁≈v₂) = Inr (sym-≈ⱽ v₁≈v₂)
  -- sym-≈ᴿ (Pair v₁≈v₂ v₁≈v₂') = Pair (sym-≈ⱽ v₁≈v₂) (sym-≈ⱽ v₁≈v₂')
  -- sym-≈ᴿ (Fun θ₁≈θ₂) = Fun (sym-≈ᴱ θ₁≈θ₂)
  -- sym-≈ᴿ (Ref-Iᴸ ℓ⊑A n) = Ref-Iᴸ ℓ⊑A n
  -- sym-≈ᴿ (Ref-Iᴴ ℓ₁⋤A ℓ₂⋤A) = Ref-Iᴴ ℓ₂⋤A ℓ₁⋤A
  -- sym-≈ᴿ (Id v₁≈v₂) = Id (sym-≈ⱽ v₁≈v₂)

  postulate sym-≈ᴱ : ∀ {Γ} {θ₁ θ₂ : Env Γ} → θ₁ ≈ᴱ θ₂ → θ₂ ≈ᴱ θ₁
  -- sym-≈ᴱ [] = []
  -- sym-≈ᴱ (v₁≈v₂ ∷ θ₁≈θ₂) = sym-≈ⱽ v₁≈v₂ ∷ sym-≈ᴱ θ₁≈θ₂

  -- Transitive
  postulate trans-≈ᴿ : ∀ {τ} {r₁ r₂ r₃ : Raw τ} → r₁ ≈ᴿ r₂ → r₂ ≈ᴿ r₃ → r₁ ≈ᴿ r₃
  -- trans-≈ᴿ Unit Unit = Unit
  -- trans-≈ᴿ (Lbl ℓ) (Lbl .ℓ) = Lbl ℓ
  -- trans-≈ᴿ (Inl v₁≈v₂) (Inl v₂≈v₃) = Inl (trans-≈ⱽ v₁≈v₂ v₂≈v₃)
  -- trans-≈ᴿ (Inr v₁≈v₂) (Inr v₂≈v₃) = Inr (trans-≈ⱽ v₁≈v₂ v₂≈v₃)
  -- trans-≈ᴿ (Pair v₁≈v₂ v₁≈v₃) (Pair v₂≈v₃ v₂≈v₄) = Pair (trans-≈ⱽ v₁≈v₂ v₂≈v₃) (trans-≈ⱽ v₁≈v₃ v₂≈v₄)
  -- trans-≈ᴿ (Fun θ₁≈θ₂) (Fun θ₂≈θ₃) = Fun (trans-≈ᴱ θ₁≈θ₂ θ₂≈θ₃)
  -- trans-≈ᴿ (Ref-Iᴸ ℓ⊑A n) (Ref-Iᴸ ℓ⊑A₁ .n) = Ref-Iᴸ ℓ⊑A₁ n
  -- trans-≈ᴿ (Ref-Iᴸ ℓ⊑A n) (Ref-Iᴴ ℓ₁⋤A ℓ₂⋤A) = ⊥-elim (ℓ₁⋤A ℓ⊑A)
  -- trans-≈ᴿ (Ref-Iᴴ ℓ₁⋤A ℓ₂⋤A) (Ref-Iᴸ ℓ⊑A n) = ⊥-elim (ℓ₂⋤A ℓ⊑A)
  -- trans-≈ᴿ (Ref-Iᴴ ℓ₁⋤A ℓ₂⋤A) (Ref-Iᴴ ℓ₁⋤A₁ ℓ₂⋤A₁) = Ref-Iᴴ ℓ₁⋤A ℓ₂⋤A₁
  -- trans-≈ᴿ (Id v₁≈v₂) (Id v₂≈v₃) = Id (trans-≈ⱽ v₁≈v₂ v₂≈v₃)

  postulate trans-≈ⱽ : ∀ {τ} {v₁ v₂ v₃ : Value τ} → v₁ ≈ⱽ v₂ → v₂ ≈ⱽ v₃ → v₁ ≈ⱽ v₃
  -- trans-≈ⱽ (Valueᴸ ℓ⊑A r≈) (Valueᴸ ℓ⊑A₁ r≈₁) = Valueᴸ ℓ⊑A₁ (trans-≈ᴿ r≈ r≈₁)
  -- trans-≈ⱽ (Valueᴸ ℓ⊑A r≈) (Valueᴴ ℓ₁⋤A ℓ₂⋤A) = ⊥-elim (ℓ₁⋤A ℓ⊑A)
  -- trans-≈ⱽ (Valueᴴ ℓ₁⋤A ℓ₂⋤A) (Valueᴸ ℓ⊑A r≈) = ⊥-elim (ℓ₂⋤A ℓ⊑A)
  -- trans-≈ⱽ (Valueᴴ ℓ₁⋤A ℓ₂⋤A) (Valueᴴ ℓ₁⋤A₁ ℓ₂⋤A₁) = Valueᴴ ℓ₁⋤A ℓ₂⋤A₁

  postulate trans-≈ᴱ : ∀ {Γ} {θ₁ θ₂ θ₃ : Env Γ} → θ₁ ≈ᴱ θ₂ → θ₂ ≈ᴱ θ₃ → θ₁ ≈ᴱ θ₃
  -- trans-≈ᴱ [] [] = []
  -- trans-≈ᴱ (v₁≈v₂ ∷ θ₁≈θ₂) (v₂≈v₃ ∷ θ₂≈θ₃) = trans-≈ⱽ v₁≈v₂ v₂≈v₃ ∷ trans-≈ᴱ θ₁≈θ₂ θ₂≈θ₃

-- instance
--   ≈ᴿ-isEquivalence : ∀ {τ} → IsEquivalence (_≈ᴿ_ {τ})
--   ≈ᴿ-isEquivalence = record { refl = refl-≈ᴿ ; sym = sym-≈ᴿ ; trans = trans-≈ᴿ }

--   ≈ⱽ-isEquivalence : ∀ {τ} → IsEquivalence (_≈ⱽ_ {τ})
--   ≈ⱽ-isEquivalence = record { refl = refl-≈ⱽ ; sym = sym-≈ⱽ ; trans = trans-≈ⱽ }

--   ≈ᴱ-isEquivalence : ∀ {Γ} → IsEquivalence (_≈ᴱ_ {Γ})
--   ≈ᴱ-isEquivalence = record { refl = refl-≈ᴱ ; sym = sym-≈ᴱ ; trans = trans-≈ᴱ }

--   ≡-isEquivalence : ∀ {A : Set} → IsEquivalence (_≡_ {_} {A})
--   ≡-isEquivalence = record { refl = refl ; sym = sym ; trans = trans }

-- open S.Props ≈ᴿ-isEquivalence public
-- open H.Props ≈ⱽ-isEquivalence public

-- refl-≈ᴬ : ∀ {A} {R : A → A → Set} {{𝑹 : IsEquivalence R}} {c} → c ≈⟨ R ⟩ᴬ c
-- refl-≈ᴬ {{𝑹}}  = ⟨ ι , refl-≈ˢ , refl-≈ᴴ , IsEquivalence.refl 𝑹 ⟩

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
