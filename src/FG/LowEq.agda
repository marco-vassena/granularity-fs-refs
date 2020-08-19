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
    Ref-Iᴸ : ∀ {β} {ℓ τ n} →
               (ℓ⊑A : ℓ ⊑ A) → -- ⟨ n , m ⟩ ∈ᵗ β → -- We should not need the bijection anymore
               Refᴵ {τ = τ} ℓ n ≈⟨ β ⟩ᴿ Refᴵ ℓ n

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
Ref-Iᴸ′ : ∀ {τ ℓ n₁ n₂} {β : Bij} → ℓ ⊑ A → n₁ ≡ n₂ → Refᴵ {τ = τ} ℓ n₁ ≈⟨ β ⟩ᴿ Refᴵ ℓ n₂
Ref-Iᴸ′ ℓ⊑A refl = Ref-Iᴸ ℓ⊑A

-- Ref-I′ : ∀ {τ n₁ n₂} {β : Bij} {v₁ v₂ : Value τ} → ⟨ n₁ , n₂ ⟩ ∈ᵗ β →
--             let _ ^ ℓ₁ = v₁
--                 _ ^ ℓ₂ = v₂ in
--          v₁ ≈⟨ β ⟩ⱽ v₂ →
--          Refᴵ {τ = τ} ℓ₁ n₁ ≈⟨ β ⟩ᴿ Refᴵ ℓ₂ n₂
-- Ref-I′ ∈₁ (Valueᴸ ℓ⊑A r≈) = Ref-Iᴸ ℓ⊑A ∈₁
-- Ref-I′ ∈₁ (Valueᴴ ℓ₁⋤A ℓ₂⋤A) = Ref-Iᴴ ℓ₁⋤A ℓ₂⋤A

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
open import Generic.Value.HLowEq {Ty} {Value} _≈⟨_⟩ⱽ_ public

-- TODO: these hint that cells and values are isomorphic
-- and then we might as well put values in the store
-- ≈ⱽ-≈ᶜ : ∀ {τ β} {v₁ v₂ : Value τ} → v₁ ≈⟨ β ⟩ⱽ v₂ →
--         let r₁ ^ ℓ₁ = v₁
--             r₂ ^ ℓ₂ = v₂ in
--             ⟨ r₁ , ℓ₁ ⟩ S.≈⟨ β ⟩ᶜ ⟨ r₂ , ℓ₂ ⟩
-- ≈ⱽ-≈ᶜ (Valueᴸ ℓ⊑A r≈) = cellᴸ ℓ⊑A r≈
-- ≈ⱽ-≈ᶜ (Valueᴴ ℓ₁⋤A ℓ₂⋤A) = cellᴴ ℓ₁⋤A ℓ₂⋤A

-- lemma-≈ᶜ : ∀ {τ β} {c₁ c₂ : Cell τ} → c₁ S.≈⟨ β ⟩ᶜ c₂ →
--                 let ⟨ r₁ , ℓ₁ ⟩ = c₁
--                     ⟨ r₂ , ℓ₂ ⟩ = c₂ in
--                 ℓ₁ ⊑ A → ℓ₂ ⊑ A → (r₁ ≈⟨ β ⟩ᴿ r₂) P.× (ℓ₁ ≡ ℓ₂)
-- lemma-≈ᶜ (cellᴸ x ≈ᴿ) ℓ₁⊑A ℓ₂⊑A = ⟨ ≈ᴿ , refl ⟩
-- lemma-≈ᶜ (cellᴴ ℓ₁⋤A _) ℓ₁⊑A ℓ₂⊑A = ⊥-elim (ℓ₁⋤A ℓ₁⊑A)

-- ≈ᶜ-≈ᴿ : ∀ {τ β} {c₁ c₂ : Cell τ} → c₁ S.≈⟨ β ⟩ᶜ c₂ →
--                 let ⟨ r₁ , ℓ₁ ⟩ = c₁
--                     ⟨ r₂ , ℓ₂ ⟩ = c₂ in
--                 ℓ₁ ⊑ A → ℓ₂ ⊑ A → r₁ ≈⟨ β ⟩ᴿ r₂
-- ≈ᶜ-≈ᴿ ≈ᶜ ℓ₁⊑A ℓ₂⊑A = proj₁ (lemma-≈ᶜ ≈ᶜ ℓ₁⊑A ℓ₂⊑A)

-- ≈ᶜ-≡  :  ∀ {τ β} {c₁ c₂ : Cell τ} → c₁ S.≈⟨ β ⟩ᶜ c₂ →
--                 let ⟨ r₁ , ℓ₁ ⟩ = c₁
--                     ⟨ r₂ , ℓ₂ ⟩ = c₂ in
--                 ℓ₁ ⊑ A → ℓ₂ ⊑ A → ℓ₁ ≡ ℓ₂
-- ≈ᶜ-≡ ≈ᶜ ℓ₁⊑A ℓ₂⊑A = proj₂ (lemma-≈ᶜ ≈ᶜ ℓ₁⊑A ℓ₂⊑A)

-- ≈ᶜ-≈ⱽ : ∀ {τ β} {c₁ c₂ : Cell τ} → c₁ S.≈⟨ β ⟩ᶜ c₂ →
--                 let ⟨ r₁ , ℓ₁ ⟩ = c₁
--                     ⟨ r₂ , ℓ₂ ⟩ = c₂ in (r₁ ^ ℓ₁) ≈⟨ β ⟩ⱽ (r₂ ^ ℓ₂)
-- ≈ᶜ-≈ⱽ (cellᴸ x x₁) = Valueᴸ x x₁
-- ≈ᶜ-≈ⱽ (cellᴴ x x₁) = Valueᴴ x x₁

-- taint-update-≈ᶜ :  ∀ {τ β} {c₁ c₂ : Cell τ} {v₁ v₂ : Value τ} →
--                      c₁ S.≈⟨ β ⟩ᶜ c₂ →  v₁ ≈⟨ β ⟩ⱽ v₂ →
--                 let ⟨ r₁ , ℓ₁ ⟩ = c₁
--                     ⟨ r₂ , ℓ₂ ⟩ = c₂
--                     r₁' ^ ℓ₁' = v₁
--                     r₂' ^ ℓ₂' = v₂ in
--                     ⟨ r₁' , ℓ₁' ⟩  S.≈⟨ β ⟩ᶜ ⟨ r₂' , ℓ₂' ⟩
-- taint-update-≈ᶜ (cellᴸ ⊑₁ r≈) (Valueᴸ ℓ⊑A r≈₁) = cellᴸ ℓ⊑A r≈₁
-- taint-update-≈ᶜ (cellᴸ ⊑₁ r≈) (Valueᴴ ℓ₁⋤A ℓ₂⋤A) = cellᴴ ℓ₁⋤A ℓ₂⋤A
-- taint-update-≈ᶜ (cellᴴ ⋤₁ ⋤₂) (Valueᴸ ℓ⊑A r≈₁) = cellᴸ ℓ⊑A r≈₁ -- This gives more expressivity
-- taint-update-≈ᶜ (cellᴴ ⋤₁ ⋤₂) (Valueᴴ ℓ₁⋤A ℓ₂⋤A) = cellᴴ ℓ₁⋤A ℓ₂⋤A

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

-- open import Generic.Bijection as B

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
-- Properties: L-equivalence is an equivalence relation.

open import Generic.Bijection

private module R = IProps Ty Raw
private module V = IProps Ty Value
private module E = IProps Ctx Env

mutual

  -- TODO: update description
  -- Weaken the identity bijection to progressively construct a bijection
  -- large enough for all the references in a value.
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
  refl-≈ᴿ {x = ⟨ v₁ , v₂ ⟩} = Pair ≈₁′ ≈₂′
    where ≈₁′ = wken-≈ⱽ (ι-⊆ (m≤m⊔n ∥ v₁ ∥ⱽ ∥ v₂ ∥ⱽ)) refl-≈ⱽ
          ≈₂′ = wken-≈ⱽ (ι-⊆ (n≤m⊔n ∥ v₁ ∥ⱽ ∥ v₂ ∥ⱽ)) refl-≈ⱽ
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
  sym-≈ᴿ {β = β} (Ref-Iᴸ ℓ⊑A) = Ref-Iᴸ ℓ⊑A
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
  trans-≈ᴿ {β₁ = β₁} {β₂} (Ref-Iᴸ ℓ⊑A) (Ref-Iᴸ ℓ⊑A₁)
    = Ref-Iᴸ ℓ⊑A₁
  trans-≈ᴿ (Ref-Iᴸ ℓ⊑A) (Ref-Iᴴ ℓ₁⋤A ℓ₂⋤A) = ⊥-elim (ℓ₁⋤A ℓ⊑A)
  trans-≈ᴿ (Ref-Iᴴ ℓ₁⋤A ℓ₂⋤A) (Ref-Iᴸ ℓ⊑A) = ⊥-elim (ℓ₂⋤A ℓ⊑A)
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

import Generic.ValidEquivalence as G
open G Ty

𝑹 : IsValidEquivalence Raw _≈⟨_⟩ᴿ_
𝑹 = record { ∥_∥ = ∥_∥ᴿ ; isValid = isValidᴿ ; isEquiv = isEquivᴿ }

𝑽 : IsValidEquivalence Value _≈⟨_⟩ⱽ_
𝑽 = record { ∥_∥ = ∥_∥ⱽ ; isValid = isValidⱽ ; isEquiv = isEquivⱽ }

𝑬 : G.IsValidEquivalence Ctx Env _≈⟨_⟩ᴱ_
𝑬 = record { ∥_∥ = ∥_∥ᴱ ; isValid = isValidᴱ ; isEquiv = isEquivᴱ }

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
-- refl-≈ᴬ : ∀ {A} {R : Relᴮ A} {{isEquivᴿ : IsEquivalenceᴮ R}} {c} → c ≈⟨ R ⟩ᴬ c
-- refl-≈ᴬ {{isEquivᴿ}} {c = ⟨ _ , μ , _ ⟩} = ⟨ ι , {!!} , {!!} , {!refl-≈ᴬ!} ⟩ -- refl-≈ˢ , refl-≈ᴴ
--   where _≈ᴿ_ : ∀ {τ} → Raw τ → Raw τ → Set
--         _≈ᴿ_ = _≈⟨ ι′ ∥ μ ∥ᴴ ⟩ᴿ_

--         open IsEquivalenceᴮ isEquivᴿ
--         open import Generic.Store.LowEq {Ty} {Raw} _≈ᴿ_ A
--         open Props {!!}

-- sym-≈ᴬ : ∀ {A} {R : A → A → Set} {{isEquivᴿ : IsEquivalence R}} {c₁ c₂} →
--            c₁ ≈⟨ R ⟩ᴬ c₂ →
--            c₂ ≈⟨ R ⟩ᴬ c₁
-- sym-≈ᴬ {{isEquivᴿ}} ⟨ β , Σ≈ , μ≈ , t≈ ⟩ = ⟨ β ⁻¹ , sym-≈ˢ Σ≈ , sym-≈ᴴ {β = β} μ≈ , IsEquivalence.sym isEquivᴿ t≈  ⟩

-- trans-≈ᴬ : ∀ {A} {R : A → A → Set} {{isEquivᴿ : IsEquivalence R}} {c₁ c₂ c₃} →
--              c₁ ≈⟨ R ⟩ᴬ c₂ →
--              c₂ ≈⟨ R ⟩ᴬ c₃ →
--              c₁ ≈⟨ R ⟩ᴬ c₃
-- trans-≈ᴬ {{isEquivᴿ = isEquivᴿ}} ⟨ β₁ , Σ≈₁ , μ≈₁ , t≈₁ ⟩ ⟨ β₂ , Σ≈₂ , μ≈₂ , t≈₂ ⟩
--   = ⟨ β₂ ∘ᴮ β₁ , trans-≈ˢ Σ≈₁ Σ≈₂ , trans-≈ᴴ {β₁ = β₁} {β₂ = β₂} μ≈₁ μ≈₂ , IsEquivalence.trans isEquivᴿ t≈₁ t≈₂ ⟩

-- instance
--   ≈ᴬ-IsEquivalence : ∀ {A} {R : A → A → Set} {{isEquivᴿ : IsEquivalence R}}  → IsEquivalence _≈⟨ R ⟩ᴬ_
--   ≈ᴬ-IsEquivalence {{isEquivᴿ}} = record { refl = refl-≈ᴬ ; sym = sym-≈ᴬ ; trans = trans-≈ᴬ }

-- TODO: we probably need to make the bijection explicit in the relation.
-- Define the "Equivalence up to bijection" class.

-- TODO: fix the export here ...
-- Move this to Security where they are needed

--------------------------------------------------------------------------------
-- Subsumed by Generic.LowEq
-- open ≈ᴴ-Props isEquivⱽ public
-- -- (square-≈ᴴ ; ∣_∣ᴴ ; refl-≈ᴴ ; trans-≈ᴴ ; trans-≈ᴴ-ι ; snoc-≈ᴴ ; writeᴴ-≈ᴴ ; square-≈ᴴ-ι ; sym-≈ᴴ ; newᴴ-≈ᴴ ; newᴸ-≈ᴴ ; ≈-# ; readᴸ-≈ᶜ ; writeᴸ-≈ᴴ ) public

-- open ≈ˢ-Props isEquivᴿ public

open ≈ᴾ-Props 𝑹 𝑽 public
