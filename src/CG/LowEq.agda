-- This module defines a L-equivalence relation for all the categoris
-- of the calculus.  L-equivalence relates terms that are
-- indistinguishabile to an attacker at security level L.
--
-- This module is parametric in the security lattice 𝑳 = (𝓛, ⊑) and in
-- the attacker's security A ∈ 𝓛.

open import Lattice

module CG.LowEq {{𝑳 : Lattice}} (A : Label) where

open import CG.Types
open import CG.Syntax
open import Data.Product renaming (_×_ to _∧_ ; _,_ to _&_)
open import Data.Nat
open import Data.Empty
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

mutual

  -- Values
  data _≈ⱽ_ : ∀ {τ} → Value τ → Value τ → Set where

    Unit : （） ≈ⱽ （）

    Lbl : ∀ ℓ → ⌞ ℓ ⌟ ≈ⱽ ⌞ ℓ ⌟

    Inl : ∀ {τ₁ τ₂} {v₁ v₂ : Value τ₁} →
            v₁ ≈ⱽ v₂ →
            inl {τ₂ = τ₂} v₁ ≈ⱽ inl v₂

    Inr : ∀ {τ₁ τ₂} {v₁ v₂ : Value τ₂} →
            v₁ ≈ⱽ v₂ →
            inr {τ₁ = τ₁} v₁ ≈ⱽ inr v₂

    Pair : ∀ {τ₁ τ₂} {v₁ v₁' : Value τ₁} {v₂ v₂' : Value τ₂} →
             v₁ ≈ⱽ v₁' →
             v₂ ≈ⱽ v₂' →
             ⟨ v₁ , v₂ ⟩  ≈ⱽ ⟨ v₁' , v₂' ⟩

    Fun : ∀ {τ' τ Γ} {e : Expr (τ' ∷ Γ) τ} {θ₁ θ₂ : Env Γ} →
                θ₁ ≈ᴱ θ₂ →
                ⟨ e , θ₁ ⟩ᶜ ≈ⱽ ⟨ e , θ₂ ⟩ᶜ

    Thunk′ : ∀ {τ Γ} {t : Thunk Γ (LIO τ)} {θ₁ θ₂ : Env Γ} →
               θ₁ ≈ᴱ θ₂ →
               ⟨ t , θ₁ ⟩ᵀ ≈ⱽ ⟨ t , θ₂ ⟩ᵀ

    Labeledᴸ : ∀ {τ ℓ} {v₁ v₂ : Value τ} →
                 ℓ ⊑ A →
                 v₁ ≈ⱽ v₂ →
                 Labeled ℓ v₁ ≈ⱽ Labeled ℓ v₂

    Labeledᴴ : ∀ {τ ℓ₁ ℓ₂} {v₁ v₂ : Value τ} →
                 ℓ₁ ⋤ A →
                 ℓ₂ ⋤ A →
                 Labeled ℓ₁ v₁ ≈ⱽ Labeled ℓ₂ v₂

    Refᴸ : ∀ {ℓ τ} → (ℓ⊑A : ℓ ⊑ A) (n : ℕ) →
             Ref {τ = τ} ℓ n ≈ⱽ Ref ℓ n

    Refᴴ : ∀ {ℓ₁ ℓ₂ n₁ n₂ τ} →
             (ℓ₁⋤A : ℓ₁ ⋤ A) (ℓ₂⋤A : ℓ₂ ⋤ A) →
             Ref {τ = τ} ℓ₁ n₁ ≈ⱽ Ref ℓ₂ n₂

  -- Environment
  data _≈ᴱ_  : ∀ {Γ} → Env Γ → Env Γ → Set where
    [] : [] ≈ᴱ []
    _∷_ : ∀ {τ Γ} {v₁ v₂ : Value τ} {θ₁ : Env Γ} {θ₂ : Env Γ} →
            (v₁ ≈ⱽ v₂) →
            (θ₁ ≈ᴱ θ₂) →
            (v₁ ∷ θ₁) ≈ᴱ (v₂ ∷ θ₂)

-- Shorthand
Refᴸ′ : ∀ {τ ℓ n₁ n₂} → ℓ ⊑ A → n₁ ≡ n₂ → Ref {τ = τ} ℓ n₁ ≈ⱽ Ref ℓ n₂
Refᴸ′ ℓ⊑A refl = Refᴸ ℓ⊑A _

-- Derive low-equivalence for stores and memories.
open import Generic.Store.LowEq {Ty} {Value} _≈ⱽ_  A as S public

open Conf

-- Generic
record _≈ᴬ_ {A : Set} (c₁ c₂ : Conf A) : Set where
  constructor ⟨_,_,_⟩
  field
    ≈ˢ : store c₁ ≈ˢ store c₂
    pc-≡ : pc c₁ ≡ pc c₂
    term-≡ : term c₁ ≡ term c₂

-- Initial Configuration (Expr)
_≈ᴵ_ : ∀ {Γ τ} → (c₁ c₂ : EConf Γ τ) → Set
c₁ ≈ᴵ c₂ = c₁ ≈ᴬ c₂

-- Initial Configuration (Thunk)
_≈ᵀ_ : ∀ {Γ τ} → (c₁ c₂ : TConf Γ τ) → Set
c₁ ≈ᵀ c₂ = c₁ ≈ᴬ c₂

-- Final Configuration
data _≈ᶜ_ {τ} : FConf τ → FConf τ → Set where

  pcᴸ : ∀ {Σ₁ Σ₂ v₁ v₂ pc} →
          (Σ≈ : Σ₁ ≈ˢ Σ₂) (pc⊑A : pc ⊑ A) (v≈ : v₁ ≈ⱽ v₂) →
          ⟨ Σ₁ , pc , v₁ ⟩ ≈ᶜ ⟨ Σ₂ , pc , v₂ ⟩

  pcᴴ : ∀ {Σ₁ Σ₂ v₁ v₂ pc₁ pc₂} →
          (Σ≈ : Σ₁ ≈ˢ Σ₂) (pc₁⋤A : pc₁ ⋤ A) (pc₂⋤A : pc₂ ⋤ A) →
          ⟨ Σ₁ , pc₁ , v₁ ⟩ ≈ᶜ ⟨ Σ₂ , pc₂ , v₂ ⟩

--------------------------------------------------------------------------------
-- Properties: L-equivalence is an equivalence relation.

mutual

  -- Reflexive
  refl-≈ⱽ : ∀ {τ} {v : Value τ} → v ≈ⱽ v
  refl-≈ⱽ {v = （）} = Unit
  refl-≈ⱽ {v = ⟨ e , θ ⟩ᶜ} = Fun refl-≈ᴱ
  refl-≈ⱽ {v = ⟨ t , θ ⟩ᵀ} = Thunk′ refl-≈ᴱ
  refl-≈ⱽ {v = inl v} = Inl refl-≈ⱽ
  refl-≈ⱽ {v = inr v} = Inr refl-≈ⱽ
  refl-≈ⱽ {v = ⟨ v , v₁ ⟩} = Pair refl-≈ⱽ refl-≈ⱽ
  refl-≈ⱽ {v = Labeled ℓ v} with ℓ ⊑? A
  ... | yes p = Labeledᴸ p refl-≈ⱽ
  ... | no ¬p = Labeledᴴ ¬p ¬p
  refl-≈ⱽ {v = Ref ℓ n} with ℓ ⊑? A
  ... | yes p = Refᴸ p n
  ... | no ¬p = Refᴴ ¬p ¬p
  refl-≈ⱽ {v = ⌞ ℓ ⌟} = Lbl ℓ

  refl-≈ᴱ : ∀ {Γ} {θ : Env Γ} → θ ≈ᴱ θ
  refl-≈ᴱ {θ = []} = []
  refl-≈ᴱ {θ = v ∷ θ} = refl-≈ⱽ ∷ refl-≈ᴱ

  -- Symmetric
  sym-≈ⱽ : ∀ {τ} {v₁ v₂ : Value τ} → v₁ ≈ⱽ v₂ → v₂ ≈ⱽ v₁
  sym-≈ⱽ Unit = Unit
  sym-≈ⱽ (Lbl ℓ) = Lbl ℓ
  sym-≈ⱽ (Inl v₁≈v₂) = Inl (sym-≈ⱽ v₁≈v₂)
  sym-≈ⱽ (Inr v₁≈v₂) = Inr (sym-≈ⱽ v₁≈v₂)
  sym-≈ⱽ (Pair v₁≈v₂ v₁≈v₂') = Pair (sym-≈ⱽ v₁≈v₂) (sym-≈ⱽ v₁≈v₂')
  sym-≈ⱽ (Fun θ₁≈θ₂) = Fun (sym-≈ᴱ θ₁≈θ₂)
  sym-≈ⱽ (Thunk′ θ₁≈θ₂) = Thunk′ (sym-≈ᴱ θ₁≈θ₂)
  sym-≈ⱽ (Labeledᴸ x v₁≈v₂) = Labeledᴸ x (sym-≈ⱽ v₁≈v₂)
  sym-≈ⱽ (Labeledᴴ x x₁) = Labeledᴴ x₁ x
  sym-≈ⱽ (Refᴸ ℓ⊑A n) = Refᴸ ℓ⊑A n
  sym-≈ⱽ (Refᴴ ℓ₁⋤A ℓ₂⋤A) = Refᴴ ℓ₂⋤A ℓ₁⋤A

  sym-≈ᴱ : ∀ {Γ} {θ₁ θ₂ : Env Γ} → θ₁ ≈ᴱ θ₂ → θ₂ ≈ᴱ θ₁
  sym-≈ᴱ [] = []
  sym-≈ᴱ (v₁≈v₂ ∷ θ₁≈θ₂) = sym-≈ⱽ v₁≈v₂ ∷ sym-≈ᴱ θ₁≈θ₂

  -- Transitive
  trans-≈ⱽ : ∀ {τ} {v₁ v₂ v₃ : Value τ} → v₁ ≈ⱽ v₂ → v₂ ≈ⱽ v₃ → v₁ ≈ⱽ v₃
  trans-≈ⱽ Unit Unit = Unit
  trans-≈ⱽ (Lbl ℓ) (Lbl .ℓ) = Lbl ℓ
  trans-≈ⱽ (Inl v₁≈v₂) (Inl v₂≈v₃) = Inl (trans-≈ⱽ v₁≈v₂ v₂≈v₃)
  trans-≈ⱽ (Inr v₁≈v₂) (Inr v₂≈v₃) = Inr (trans-≈ⱽ v₁≈v₂ v₂≈v₃)
  trans-≈ⱽ (Pair v₁≈v₂ v₁≈v₃) (Pair v₂≈v₃ v₂≈v₄) = Pair (trans-≈ⱽ v₁≈v₂ v₂≈v₃) (trans-≈ⱽ v₁≈v₃ v₂≈v₄)
  trans-≈ⱽ (Fun θ₁≈θ₂) (Fun θ₂≈θ₃) = Fun (trans-≈ᴱ θ₁≈θ₂ θ₂≈θ₃)
  trans-≈ⱽ (Thunk′ θ₁≈θ₂) (Thunk′ θ₂≈θ₃) = Thunk′ (trans-≈ᴱ θ₁≈θ₂ θ₂≈θ₃)
  trans-≈ⱽ (Labeledᴸ x v₁≈v₂) (Labeledᴸ x₁ v₂≈v₃) = Labeledᴸ x (trans-≈ⱽ v₁≈v₂ v₂≈v₃)
  trans-≈ⱽ (Labeledᴸ x v₁≈v₂) (Labeledᴴ x₁ x₂) = ⊥-elim (x₁ x)
  trans-≈ⱽ (Labeledᴴ x x₁) (Labeledᴸ x₂ v₂≈v₃) = ⊥-elim (x₁ x₂)
  trans-≈ⱽ (Labeledᴴ x x₁) (Labeledᴴ x₂ x₃) = Labeledᴴ x x₃
  trans-≈ⱽ (Refᴸ ℓ⊑A n) (Refᴸ ℓ⊑A₁ .n) = Refᴸ ℓ⊑A₁ n
  trans-≈ⱽ (Refᴸ ℓ⊑A n) (Refᴴ ℓ₁⋤A ℓ₂⋤A) = ⊥-elim (ℓ₁⋤A ℓ⊑A)
  trans-≈ⱽ (Refᴴ ℓ₁⋤A ℓ₂⋤A) (Refᴸ ℓ⊑A n) = ⊥-elim (ℓ₂⋤A ℓ⊑A)
  trans-≈ⱽ (Refᴴ ℓ₁⋤A ℓ₂⋤A) (Refᴴ ℓ₁⋤A₁ ℓ₂⋤A₁) = Refᴴ ℓ₁⋤A ℓ₂⋤A₁

  trans-≈ᴱ : ∀ {Γ} {θ₁ θ₂ θ₃ : Env Γ} → θ₁ ≈ᴱ θ₂ → θ₂ ≈ᴱ θ₃ → θ₁ ≈ᴱ θ₃
  trans-≈ᴱ [] [] = []
  trans-≈ᴱ (v₁≈v₂ ∷ θ₁≈θ₂) (v₂≈v₃ ∷ θ₂≈θ₃) = trans-≈ⱽ v₁≈v₂ v₂≈v₃ ∷ trans-≈ᴱ θ₁≈θ₂ θ₂≈θ₃

≈ⱽ-isEquivalence : ∀ {τ} → IsEquivalence (_≈ⱽ_ {τ})
≈ⱽ-isEquivalence = record { refl = refl-≈ⱽ ; sym = sym-≈ⱽ ; trans = trans-≈ⱽ }

≈ᴱ-isEquivalence : ∀ {Γ} → IsEquivalence (_≈ᴱ_ {Γ})
≈ᴱ-isEquivalence = record { refl = refl-≈ᴱ ; sym = sym-≈ᴱ ; trans = trans-≈ᴱ }

open S.Props ≈ⱽ-isEquivalence public

≈ᴬ-isEquivalence : ∀ {A : Set} → IsEquivalence (_≈ᴬ_ {A})
≈ᴬ-isEquivalence =
  record { refl = ⟨ refl-≈ˢ , refl , refl ⟩
         ; sym = λ { ⟨ Σ₁≈Σ₂ , pc₁≡pc₂ , e₁≡e₂ ⟩ → ⟨ sym-≈ˢ Σ₁≈Σ₂ , sym pc₁≡pc₂ , sym e₁≡e₂ ⟩ }
         ; trans = λ {⟨ Σ₁≈Σ₂ , pc₁≡pc₂ , e₁≡e₂ ⟩ ⟨ Σ₂≈Σ₃ , pc₂≡pc₃ , e₂≡e₃ ⟩ →
                     ⟨ trans-≈ˢ Σ₁≈Σ₂ Σ₂≈Σ₃ , trans pc₁≡pc₂ pc₂≡pc₃ , trans e₁≡e₂ e₂≡e₃ ⟩ }
         }

refl-≈ᶜ : ∀ {τ} {c : FConf τ} → c ≈ᶜ c
refl-≈ᶜ {c = ⟨ Σ , pc , v ⟩} with pc ⊑? A
... | yes pc⊑A = pcᴸ refl-≈ˢ  pc⊑A refl-≈ⱽ
... | no pc⋤A = pcᴴ refl-≈ˢ pc⋤A pc⋤A

sym-≈ᶜ : ∀ {τ} {c₁ c₂ : FConf τ} → c₁ ≈ᶜ c₂ → c₂ ≈ᶜ c₁
sym-≈ᶜ (pcᴸ Σ≈ pc⊑A v≈) = pcᴸ (sym-≈ˢ Σ≈) pc⊑A (sym-≈ⱽ v≈)
sym-≈ᶜ (pcᴴ Σ≈ pc₁⋤A pc₂⋤A) = pcᴴ (sym-≈ˢ Σ≈) pc₂⋤A pc₁⋤A

trans-≈ᶜ : ∀ {τ} {c₁ c₂ c₃ : FConf τ} → c₁ ≈ᶜ c₂ → c₂ ≈ᶜ c₃ → c₁ ≈ᶜ c₃
trans-≈ᶜ (pcᴸ Σ≈ pc⊑A v≈) (pcᴸ Σ≈₁ pc⊑A₁ v≈₁) = pcᴸ (trans-≈ˢ Σ≈ Σ≈₁) pc⊑A (trans-≈ⱽ v≈ v≈₁)
trans-≈ᶜ (pcᴸ Σ≈ pc⊑A v≈) (pcᴴ Σ≈₁ pc₁⋤A pc₂⋤A) = ⊥-elim (pc₁⋤A pc⊑A)
trans-≈ᶜ (pcᴴ Σ≈ pc₁⋤A pc₂⋤A) (pcᴸ Σ≈₁ pc⊑A v≈) = ⊥-elim (pc₂⋤A pc⊑A)
trans-≈ᶜ (pcᴴ Σ≈ pc₁⋤A pc₂⋤A) (pcᴴ Σ≈₁ pc₁⋤A₁ pc₂⋤A₁) = pcᴴ (trans-≈ˢ Σ≈ Σ≈₁) pc₁⋤A pc₂⋤A₁

-- Projects low-equivalence for stores
≈ᶜ-≈ˢ : ∀ {τ} {c₁ c₂ : FConf τ} → c₁ ≈ᶜ c₂ → store c₁ ≈ˢ store c₂
≈ᶜ-≈ˢ (pcᴸ x x₁ x₂) = x
≈ᶜ-≈ˢ (pcᴴ x x₁ x₂) = x

≈ᶜ-isEquivalence : ∀ {τ} → IsEquivalence (_≈ᶜ_ {τ})
≈ᶜ-isEquivalence = record { refl = refl-≈ᶜ ; sym = sym-≈ᶜ ; trans = trans-≈ᶜ }
