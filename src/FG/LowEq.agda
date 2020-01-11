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
open import Data.Nat using (ℕ)
open import Data.Fin
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Generic.Bijection

mutual

-- Adding a bijection after the fact is a bit inconvenient.  Ideally,
-- we would parametrize values, expressions and all the other
-- categories with a number n to keep track of the minimum size of the
-- domain of the heap. Since this change would involve virtually
-- the whole formalization, I will add extra assumptions only
-- where needed.

  data Value-≈ {n m τ} (β : Bij n m) : Value τ → Value τ → Set where
    Valueᴸ : ∀ {r₁ r₂ ℓ} → (ℓ⊑A : ℓ ⊑ A) (r≈ : r₁ ≈⟨ β ⟩ᴿ r₂) → Value-≈ β (r₁ ^ ℓ) (r₂ ^ ℓ)
    Valueᴴ : ∀ {r₁ r₂ ℓ₁ ℓ₂} → (ℓ₁⋤A : ℓ₁ ⋤ A) (ℓ₂⋤A : ℓ₂ ⋤ A) → Value-≈ β (r₁ ^ ℓ₁) (r₂ ^ ℓ₂)

  _≈⟨_⟩ⱽ_ : ∀ {τ n m} → Value τ → Bij n m → Value τ → Set
  v₁ ≈⟨ β ⟩ⱽ v₂ = Value-≈ β v₁ v₂

  data Raw-≈ {n m} (β : Bij n m) : ∀ {τ} → Raw τ → Raw τ → Set where
    Unit : Raw-≈ β （） （）
    Lbl : ∀ ℓ → Raw-≈ β ⌞ ℓ ⌟ ⌞ ℓ ⌟
    Inl : ∀ {τ₁ τ₂} {v₁ v₂ : Value τ₁} → v₁ ≈⟨ β ⟩ⱽ v₂ → Raw-≈ β (inl {τ₂ = τ₂} v₁) (inl v₂)
    Inr : ∀ {τ₁ τ₂} {v₁ v₂ : Value τ₂} → v₁ ≈⟨ β ⟩ⱽ v₂ → Raw-≈ β (inr {τ₁ = τ₁} v₁) (inr v₂)
    Pair : ∀ {τ₁ τ₂} {v₁ v₁' : Value τ₁} {v₂ v₂' : Value τ₂} →
             v₁ ≈⟨ β ⟩ⱽ v₁' →
             v₂ ≈⟨ β ⟩ⱽ v₂' →
             Raw-≈ β ⟨ v₁ , v₂ ⟩  ⟨ v₁' , v₂' ⟩

    Fun : ∀ {τ' τ Γ} {e : Expr (τ' ∷ Γ) τ} {θ₁ : Env Γ} {θ₂ : Env Γ} →
                θ₁ ≈ᴱ θ₂ →
                {!!} → -- TODO: equivalence up-to-bijection for code as well
                Raw-≈ β ⟨ e , θ₁ ⟩ᶜ ⟨ e , θ₂ ⟩ᶜ

    -- Flow-insensitive refs
    Ref-Iᴸ : ∀ {ℓ τ} → (ℓ⊑A : ℓ ⊑ A) (n : ℕ) → Raw-≈ β (Refᴵ {τ = τ} ℓ n) (Refᴵ ℓ n)
    Ref-Iᴴ : ∀ {ℓ₁ ℓ₂ n₁ n₂ τ} →
             (ℓ₁⋤A : ℓ₁ ⋤ A) (ℓ₂⋤A : ℓ₂ ⋤ A) →
             Raw-≈ β (Refᴵ {τ = τ} ℓ₁ n₁) (Refᴵ ℓ₂ n₂)

    -- Flow-sensitive refs
    Ref-S : ∀ {n₁ n₂ τ} → {!fromℕ n₁ ↦ fromℕ n₂ ∈ᴮ β!} →
            Raw-≈ β (Refˢ {τ = τ} n₁) (Refˢ n₂)

    Id : ∀ {τ} {v₁ v₂ : Value τ} → v₁ ≈⟨ β ⟩ⱽ v₂ → Raw-≈ β (Id v₁) (Id v₂)

  _≈⟨_⟩ᴿ_ : ∀ {τ n m} → Raw τ → Bij n m → Raw τ → Set
  r₁ ≈⟨ β ⟩ᴿ r₂ = Raw-≈ β r₁ r₂

    -- Environments.
  data Env-≈ {n m : ℕ} (β : Bij n m) : ∀ {Γ} → Env Γ → Env Γ → Set where
    [] : Env-≈ β [] []
    _∷_ : ∀ {τ Γ} {v₁ v₂ : Value τ} {θ₁ θ₂ : Env Γ} →
             v₁ ≈⟨ β ⟩ⱽ v₂ → θ₁ ≈⟨ β ⟩ᴱ θ₂ → Env-≈ β (v₁ ∷ θ₁) (v₂ ∷ θ₂)

  _≈⟨_⟩ᴱ_ : ∀ {Γ n m} → Env Γ → Bij n m → Env Γ → Set
  θ₁ ≈⟨ β ⟩ᴱ θ₂ = Env-≈ β θ₁ θ₂

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
open import Generic.Heap.LowEq {Ty} {Value} _≈ⱽ_ A as H using (_≈⟨_⟩ᴴ_) public

-- Lift low-equivalence to configurations
open Conf

open import Generic.Bijection as B

record _≈⟨_⟩ᴬ_ {A : Set} (c₁ : Conf A) (R : A → A → Set) (c₂ : Conf A) : Set where
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

mutual

  -- Reflexive
  refl-≈ⱽ : ∀ {τ} {v : Value τ} → v ≈ⱽ v
  refl-≈ⱽ {v = r ^ ℓ} with ℓ ⊑? A
  ... | yes ℓ⊑A = Valueᴸ ℓ⊑A refl-≈ᴿ
  ... | no ℓ⋤A = Valueᴴ ℓ⋤A ℓ⋤A

  refl-≈ᴿ : ∀ {τ} {r : Raw τ} → r ≈ᴿ r
  refl-≈ᴿ {r = （）} = Unit
  refl-≈ᴿ {r = ⟨ e , θ ⟩ᶜ} = Fun refl-≈ᴱ
  refl-≈ᴿ {r = inl r} = Inl refl-≈ⱽ
  refl-≈ᴿ {r = inr r} = Inr refl-≈ⱽ
  refl-≈ᴿ {r = ⟨ r , r₁ ⟩} = Pair refl-≈ⱽ refl-≈ⱽ
  refl-≈ᴿ {r = Refᴵ ℓ n} with ℓ ⊑? A
  ... | yes p = Ref-Iᴸ p n
  ... | no ¬p = Ref-Iᴴ ¬p ¬p
  refl-≈ᴿ {r = Refˢ n} = {!!} -- Reflexivity creates the identity bijection? yes!
  refl-≈ᴿ {r = ⌞ ℓ ⌟} = Lbl ℓ
  refl-≈ᴿ {r = Id v} = Id refl-≈ⱽ

  refl-≈ᴱ : ∀ {Γ} {θ : Env Γ} → θ ≈ᴱ θ
  refl-≈ᴱ {θ = []} = []
  refl-≈ᴱ {θ = v ∷ θ} = refl-≈ⱽ ∷ refl-≈ᴱ


  -- Symmetric
  sym-≈ⱽ : ∀ {τ} {v₁ v₂ : Value τ} → v₁ ≈ⱽ v₂ → v₂ ≈ⱽ v₁
  sym-≈ⱽ (Valueᴸ ℓ⊑A r≈) = Valueᴸ ℓ⊑A (sym-≈ᴿ r≈)
  sym-≈ⱽ (Valueᴴ ℓ₁⋤A ℓ₂⋤A) = Valueᴴ ℓ₂⋤A ℓ₁⋤A

  sym-≈ᴿ : ∀ {τ} {r₁ r₂ : Raw τ} → r₁ ≈ᴿ r₂ → r₂ ≈ᴿ r₁
  sym-≈ᴿ Unit = Unit
  sym-≈ᴿ (Lbl ℓ) = Lbl ℓ
  sym-≈ᴿ (Inl v₁≈v₂) = Inl (sym-≈ⱽ v₁≈v₂)
  sym-≈ᴿ (Inr v₁≈v₂) = Inr (sym-≈ⱽ v₁≈v₂)
  sym-≈ᴿ (Pair v₁≈v₂ v₁≈v₂') = Pair (sym-≈ⱽ v₁≈v₂) (sym-≈ⱽ v₁≈v₂')
  sym-≈ᴿ (Fun θ₁≈θ₂) = Fun (sym-≈ᴱ θ₁≈θ₂)
  sym-≈ᴿ (Ref-Iᴸ ℓ⊑A n) = Ref-Iᴸ ℓ⊑A n
  sym-≈ᴿ (Ref-Iᴴ ℓ₁⋤A ℓ₂⋤A) = Ref-Iᴴ ℓ₂⋤A ℓ₁⋤A
  sym-≈ᴿ (Id v₁≈v₂) = Id (sym-≈ⱽ v₁≈v₂)

  sym-≈ᴱ : ∀ {Γ} {θ₁ θ₂ : Env Γ} → θ₁ ≈ᴱ θ₂ → θ₂ ≈ᴱ θ₁
  sym-≈ᴱ [] = []
  sym-≈ᴱ (v₁≈v₂ ∷ θ₁≈θ₂) = sym-≈ⱽ v₁≈v₂ ∷ sym-≈ᴱ θ₁≈θ₂

  -- Transitive
  trans-≈ᴿ : ∀ {τ} {r₁ r₂ r₃ : Raw τ} → r₁ ≈ᴿ r₂ → r₂ ≈ᴿ r₃ → r₁ ≈ᴿ r₃
  trans-≈ᴿ Unit Unit = Unit
  trans-≈ᴿ (Lbl ℓ) (Lbl .ℓ) = Lbl ℓ
  trans-≈ᴿ (Inl v₁≈v₂) (Inl v₂≈v₃) = Inl (trans-≈ⱽ v₁≈v₂ v₂≈v₃)
  trans-≈ᴿ (Inr v₁≈v₂) (Inr v₂≈v₃) = Inr (trans-≈ⱽ v₁≈v₂ v₂≈v₃)
  trans-≈ᴿ (Pair v₁≈v₂ v₁≈v₃) (Pair v₂≈v₃ v₂≈v₄) = Pair (trans-≈ⱽ v₁≈v₂ v₂≈v₃) (trans-≈ⱽ v₁≈v₃ v₂≈v₄)
  trans-≈ᴿ (Fun θ₁≈θ₂) (Fun θ₂≈θ₃) = Fun (trans-≈ᴱ θ₁≈θ₂ θ₂≈θ₃)
  trans-≈ᴿ (Ref-Iᴸ ℓ⊑A n) (Ref-Iᴸ ℓ⊑A₁ .n) = Ref-Iᴸ ℓ⊑A₁ n
  trans-≈ᴿ (Ref-Iᴸ ℓ⊑A n) (Ref-Iᴴ ℓ₁⋤A ℓ₂⋤A) = ⊥-elim (ℓ₁⋤A ℓ⊑A)
  trans-≈ᴿ (Ref-Iᴴ ℓ₁⋤A ℓ₂⋤A) (Ref-Iᴸ ℓ⊑A n) = ⊥-elim (ℓ₂⋤A ℓ⊑A)
  trans-≈ᴿ (Ref-Iᴴ ℓ₁⋤A ℓ₂⋤A) (Ref-Iᴴ ℓ₁⋤A₁ ℓ₂⋤A₁) = Ref-Iᴴ ℓ₁⋤A ℓ₂⋤A₁
  trans-≈ᴿ (Id v₁≈v₂) (Id v₂≈v₃) = Id (trans-≈ⱽ v₁≈v₂ v₂≈v₃)

  trans-≈ⱽ : ∀ {τ} {v₁ v₂ v₃ : Value τ} → v₁ ≈ⱽ v₂ → v₂ ≈ⱽ v₃ → v₁ ≈ⱽ v₃
  trans-≈ⱽ (Valueᴸ ℓ⊑A r≈) (Valueᴸ ℓ⊑A₁ r≈₁) = Valueᴸ ℓ⊑A₁ (trans-≈ᴿ r≈ r≈₁)
  trans-≈ⱽ (Valueᴸ ℓ⊑A r≈) (Valueᴴ ℓ₁⋤A ℓ₂⋤A) = ⊥-elim (ℓ₁⋤A ℓ⊑A)
  trans-≈ⱽ (Valueᴴ ℓ₁⋤A ℓ₂⋤A) (Valueᴸ ℓ⊑A r≈) = ⊥-elim (ℓ₂⋤A ℓ⊑A)
  trans-≈ⱽ (Valueᴴ ℓ₁⋤A ℓ₂⋤A) (Valueᴴ ℓ₁⋤A₁ ℓ₂⋤A₁) = Valueᴴ ℓ₁⋤A ℓ₂⋤A₁

  trans-≈ᴱ : ∀ {Γ} {θ₁ θ₂ θ₃ : Env Γ} → θ₁ ≈ᴱ θ₂ → θ₂ ≈ᴱ θ₃ → θ₁ ≈ᴱ θ₃
  trans-≈ᴱ [] [] = []
  trans-≈ᴱ (v₁≈v₂ ∷ θ₁≈θ₂) (v₂≈v₃ ∷ θ₂≈θ₃) = trans-≈ⱽ v₁≈v₂ v₂≈v₃ ∷ trans-≈ᴱ θ₁≈θ₂ θ₂≈θ₃

instance
  ≈ᴿ-isEquivalence : ∀ {τ} → IsEquivalence (_≈ᴿ_ {τ})
  ≈ᴿ-isEquivalence = record { refl = refl-≈ᴿ ; sym = sym-≈ᴿ ; trans = trans-≈ᴿ }

  ≈ⱽ-isEquivalence : ∀ {τ} → IsEquivalence (_≈ⱽ_ {τ})
  ≈ⱽ-isEquivalence = record { refl = refl-≈ⱽ ; sym = sym-≈ⱽ ; trans = trans-≈ⱽ }

  ≈ᴱ-isEquivalence : ∀ {Γ} → IsEquivalence (_≈ᴱ_ {Γ})
  ≈ᴱ-isEquivalence = record { refl = refl-≈ᴱ ; sym = sym-≈ᴱ ; trans = trans-≈ᴱ }

  ≡-isEquivalence : ∀ {A : Set} → IsEquivalence (_≡_ {_} {A})
  ≡-isEquivalence = record { refl = refl ; sym = sym ; trans = trans }

open S.Props ≈ᴿ-isEquivalence public
open H.Props ≈ⱽ-isEquivalence public

refl-≈ᴬ : ∀ {A} {R : A → A → Set} {{𝑹 : IsEquivalence R}} {c} → c ≈⟨ R ⟩ᴬ c
refl-≈ᴬ {{𝑹}}  = ⟨ ι , refl-≈ˢ , refl-≈ᴴ , IsEquivalence.refl 𝑹 ⟩

sym-≈ᴬ : ∀ {A} {R : A → A → Set} {{𝑹 : IsEquivalence R}} {c₁ c₂} →
           c₁ ≈⟨ R ⟩ᴬ c₂ →
           c₂ ≈⟨ R ⟩ᴬ c₁
sym-≈ᴬ {{𝑹}} ⟨ β , Σ≈ , μ≈ , t≈ ⟩ = ⟨ β ⁻¹ , sym-≈ˢ Σ≈ , sym-≈ᴴ {β = β} μ≈ , IsEquivalence.sym 𝑹 t≈  ⟩

trans-≈ᴬ : ∀ {A} {R : A → A → Set} {{𝑹 : IsEquivalence R}} {c₁ c₂ c₃} →
             c₁ ≈⟨ R ⟩ᴬ c₂ →
             c₂ ≈⟨ R ⟩ᴬ c₃ →
             c₁ ≈⟨ R ⟩ᴬ c₃
trans-≈ᴬ {{𝑹 = 𝑹}} ⟨ β₁ , Σ≈₁ , μ≈₁ , t≈₁ ⟩ ⟨ β₂ , Σ≈₂ , μ≈₂ , t≈₂ ⟩
  = ⟨ β₂ ∘ᴮ β₁ , trans-≈ˢ Σ≈₁ Σ≈₂ , trans-≈ᴴ {β₁ = β₁} {β₂ = β₂} μ≈₁ μ≈₂ , IsEquivalence.trans 𝑹 t≈₁ t≈₂ ⟩

instance
  ≈ᴬ-IsEquivalence : ∀ {A} {R : A → A → Set} {{𝑹 : IsEquivalence R}}  → IsEquivalence _≈⟨ R ⟩ᴬ_
  ≈ᴬ-IsEquivalence {{𝑹}} = record { refl = refl-≈ᴬ ; sym = sym-≈ᴬ ; trans = trans-≈ᴬ }
