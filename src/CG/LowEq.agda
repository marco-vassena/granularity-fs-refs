-- This module defines a L-equivalence relation for all the categoris
-- of the calculus.  L-equivalence relates terms that are
-- indistinguishabile to an attacker at security level L.
--
-- This module is parametric in the security lattice 𝑳 = (𝓛, ⊑) and in
-- the attacker's security A ∈ 𝓛.

open import Lattice

module CG.LowEq {{𝑳 : Lattice}} (A : Label) where

open import CG.Types renaming (_∈_ to _∈ᵀ_ ; _⊆_ to _⊆ᵀ_)
open import CG.Syntax
open import Data.Nat renaming (_⊔_ to _⊔ᴺ_)
open import Data.Nat.Properties
open import Data.Empty
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Generic.Bijection
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import CG.Valid

mutual

  -- Values
  data _≈⟨_⟩ⱽ_ : ∀ {τ} → Value τ → Bij → Value τ → Set where

    Unit : ∀ {β} → （） ≈⟨ β ⟩ⱽ （）

    Lbl : ∀ {β} ℓ → ⌞ ℓ ⌟ ≈⟨ β ⟩ⱽ ⌞ ℓ ⌟

    Inl : ∀ {τ₁ τ₂ β} {v₁ v₂ : Value τ₁} →
            v₁ ≈⟨ β ⟩ⱽ v₂ →
            inl {τ₂ = τ₂} v₁ ≈⟨ β ⟩ⱽ inl v₂

    Inr : ∀ {τ₁ τ₂ β} {v₁ v₂ : Value τ₂} →
            v₁ ≈⟨ β ⟩ⱽ v₂ →
            inr {τ₁ = τ₁} v₁ ≈⟨ β ⟩ⱽ inr v₂

    Pair : ∀ {τ₁ τ₂ β} {v₁ v₁' : Value τ₁} {v₂ v₂' : Value τ₂} →
             v₁ ≈⟨ β ⟩ⱽ v₁' →
             v₂ ≈⟨ β ⟩ⱽ v₂' →
             ⟨ v₁ , v₂ ⟩  ≈⟨ β ⟩ⱽ ⟨ v₁' , v₂' ⟩

    Fun : ∀ {τ' τ Γ β} {e : Expr (τ' ∷ Γ) τ} {θ₁ θ₂ : Env Γ} →
                θ₁ ≈⟨ β ⟩ᴱ θ₂ →
                ⟨ e , θ₁ ⟩ᶜ ≈⟨ β ⟩ⱽ ⟨ e , θ₂ ⟩ᶜ

    Thunk′ : ∀ {τ Γ β} {t : Thunk Γ (LIO τ)} {θ₁ θ₂ : Env Γ} →
               θ₁ ≈⟨ β ⟩ᴱ θ₂ →
               ⟨ t , θ₁ ⟩ᵀ ≈⟨ β ⟩ⱽ ⟨ t , θ₂ ⟩ᵀ

    Labeledᴸ : ∀ {τ ℓ β} {v₁ v₂ : Value τ} →
                 ℓ ⊑ A →
                 v₁ ≈⟨ β ⟩ⱽ v₂ →
                 Labeled ℓ v₁ ≈⟨ β ⟩ⱽ Labeled ℓ v₂

    Labeledᴴ : ∀ {τ ℓ₁ ℓ₂ β} {v₁ v₂ : Value τ} →
                 ℓ₁ ⋤ A →
                 ℓ₂ ⋤ A →
                 Labeled ℓ₁ v₁ ≈⟨ β ⟩ⱽ Labeled ℓ₂ v₂

    Ref-Iᴸ : ∀ {ℓ τ β} → (ℓ⊑A : ℓ ⊑ A) (n : ℕ) →
             Refᴵ {τ = τ} ℓ n ≈⟨ β ⟩ⱽ Refᴵ ℓ n

    Ref-Iᴴ : ∀ {ℓ₁ ℓ₂ n₁ n₂ τ β} →
             (ℓ₁⋤A : ℓ₁ ⋤ A) (ℓ₂⋤A : ℓ₂ ⋤ A) →
             Refᴵ {τ = τ} ℓ₁ n₁ ≈⟨ β ⟩ⱽ Refᴵ ℓ₂ n₂

    Ref-S : ∀ {n m τ β} → ⟨ n , m ⟩ ∈ᵗ β →
              Refˢ {τ = τ} n ≈⟨ β ⟩ⱽ Refˢ m

  -- Environment
  data _≈⟨_⟩ᴱ_  : ∀ {Γ} → Env Γ → Bij → Env Γ → Set where
    [] : ∀ {β} → [] ≈⟨ β ⟩ᴱ []
    _∷_ : ∀ {τ Γ β} {v₁ v₂ : Value τ} {θ₁ : Env Γ} {θ₂ : Env Γ} →
            (v₁ ≈⟨ β ⟩ⱽ v₂) →
            (θ₁ ≈⟨ β ⟩ᴱ θ₂) →
            (v₁ ∷ θ₁) ≈⟨ β ⟩ᴱ (v₂ ∷ θ₂)

-- Shorthand
Refᴸ′ : ∀ {τ ℓ n₁ n₂ β} → ℓ ⊑ A → n₁ ≡ n₂ → Refᴵ {τ = τ} ℓ n₁ ≈⟨ β ⟩ⱽ Refᴵ ℓ n₂
Refᴸ′ ℓ⊑A refl = Ref-Iᴸ ℓ⊑A _

--------------------------------------------------------------------------------

-- Heap labeled value
_≈⟨_⟩ᴸ_ : ∀ {τ} → LValue τ → Bij → LValue τ → Set
⟨ v₁ , ℓ₁ ⟩ ≈⟨ β ⟩ᴸ ⟨ v₂ , ℓ₂ ⟩ = Labeled ℓ₁ v₁ ≈⟨ β ⟩ⱽ Labeled ℓ₂ v₂

-- label-of-≈ⱽ : ∀ {τ β} {v₁ v₂ : LValue τ} → v₁ ≈⟨ β ⟩ᴸ v₂ →
--                 let ⟨ r₁ , ℓ₁ ⟩ = v₁
--                     ⟨ r₂ , ℓ₂ ⟩ = v₂ in (⌞ ℓ₁ ⌟ ^ ℓ₁) ≈⟨ β ⟩ⱽ (⌞ ℓ₂ ⌟ ^ ℓ₂)
-- label-of-≈ⱽ (Labeledᴸ x x₁) = Labeledᴸ x (Lbl _)
-- label-of-≈ⱽ (Labeledᴴ x x₁) = Labeledᴴ x x₁


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

-- Derive low-equivalence for stores and memories.
-- open import Generic.Store.LowEq {Ty} {Value} _≈⟨_⟩ⱽ_  A as S public
-- open import Generic.Heap.LowEq {Ty} {LValue} _≈⟨_⟩ᴸ_  A as H public
open import Generic.PState.LowEq {Ty} {Ty} {Value} {LValue} _≈⟨_⟩ⱽ_ _≈⟨_⟩ᴸ_ A public

open Conf

-- Generic
record _≈⟨_⟩ᴬ_ {F : Ctx → Ty → Set} {Γ} {τ} (c₁ : Conf F Γ τ ) (β : Bij) (c₂ : Conf F Γ τ) : Set where
  constructor ⟨_,_,_⟩
  field
    pstate-≈ᴾ : ⟨ store c₁ , heap c₁ ⟩ ≈⟨ β ⟩ᴾ ⟨ store c₂ , heap c₂ ⟩
    pc-≡ : pc c₁ ≡ pc c₂
    term-≡ : term c₁ ≡ term c₂

  open _≈⟨_⟩ᴾ_ pstate-≈ᴾ public

-- Initial Configuration (Expr)
_≈⟨_⟩ᴵ_ : ∀ {Γ τ} → EConf Γ τ → Bij → EConf Γ τ → Set
c₁ ≈⟨ β ⟩ᴵ c₂ = c₁ ≈⟨ β ⟩ᴬ c₂

-- Initial Configuration (Thunk)
_≈⟨_⟩ᵀ_ : ∀ {Γ τ} → TConf Γ τ → Bij → TConf Γ τ → Set
c₁ ≈⟨ β ⟩ᵀ c₂ = c₁ ≈⟨ β ⟩ᴬ c₂

-- Final Configuration
data _≈⟨_⟩ᶜ_ {τ} : FConf τ → Bij → FConf τ → Set where

  pcᴸ : ∀ {Σ₁ Σ₂ μ₁ μ₂ v₁ v₂ pc β} →
          (≈ᴾ : ⟨ Σ₁ , μ₁ ⟩ ≈⟨ β ⟩ᴾ ⟨ Σ₂ , μ₂ ⟩) (pc⊑A : pc ⊑ A) (v≈ : v₁ ≈⟨ β ⟩ⱽ v₂) →
          ⟨ Σ₁ , μ₁ , pc , v₁ ⟩ ≈⟨ β ⟩ᶜ ⟨ Σ₂ , μ₂ , pc , v₂ ⟩

  pcᴴ : ∀ {Σ₁ Σ₂ μ₁ μ₂ v₁ v₂ pc₁ pc₂ β} →
          (≈ᴾ : ⟨ Σ₁ , μ₁ ⟩ ≈⟨ β ⟩ᴾ ⟨ Σ₂ , μ₂ ⟩) (pc₁⋤A : pc₁ ⋤ A) (pc₂⋤A : pc₂ ⋤ A) →
          ⟨ Σ₁ , μ₁ , pc₁ , v₁ ⟩ ≈⟨ β ⟩ᶜ ⟨ Σ₂ , μ₂ , pc₂ , v₂ ⟩


postulate ≈ᴸ-⊔ : ∀ {τ β} {v₁ v₂ : LValue τ} (ℓ : Label) →
                   let ⟨ v₁′ , ℓ₁ ⟩ = v₁
                       ⟨ v₂′ , ℓ₂ ⟩ = v₂ in
                       v₁ ≈⟨ β ⟩ᴸ v₂ →
                       ⟨ v₁′ , ℓ ⊔ ℓ₁ ⟩ ≈⟨ β ⟩ᴸ ⟨ v₂′ , ℓ ⊔ ℓ₂ ⟩
-- ≈ᴸ-⊑ ℓ c = {!!}

label-of-≈ᶜ : ∀ {τ β Σ₁ Σ₂ μ₁ μ₂ pc} {v₁ v₂ : LValue τ} → pc ⊑ A →
         let ⟨ _ , ℓ₁ ⟩ = v₁
             ⟨ _ , ℓ₂ ⟩ = v₂ in
             ⟨ Σ₁ , μ₁ ⟩ ≈⟨ β ⟩ᴾ ⟨ Σ₂ , μ₂ ⟩ →
             v₁ ≈⟨ β ⟩ᴸ v₂ →
             ⟨ Σ₁ , μ₁ , pc ⊔ ℓ₁ , ⌞ ℓ₁ ⌟ ⟩ ≈⟨ β ⟩ᶜ ⟨ Σ₂ , μ₂ , pc ⊔ ℓ₂ , ⌞ ℓ₂ ⌟ ⟩
label-of-≈ᶜ pc⊑A ≈ᴾ (Labeledᴸ ℓ⊑A _) = pcᴸ ≈ᴾ (join-⊑' pc⊑A ℓ⊑A) (Lbl _)
label-of-≈ᶜ pc⊑A ≈ᴾ (Labeledᴴ ⋤₁ ⋤₂) = pcᴴ ≈ᴾ (join-⋤₂ ⋤₁) (join-⋤₂ ⋤₂)

read-≈ᶜ : ∀ {τ β Σ₁ Σ₂ μ₁ μ₂ pc} {v₁ v₂ : LValue τ} → pc ⊑ A →
         let ⟨ v₁′ , ℓ₁ ⟩ = v₁
             ⟨ v₂′ , ℓ₂ ⟩ = v₂ in
             ⟨ Σ₁ , μ₁ ⟩ ≈⟨ β ⟩ᴾ ⟨ Σ₂ , μ₂ ⟩ →
             v₁ ≈⟨ β ⟩ᴸ v₂ →
             ⟨ Σ₁ , μ₁ , pc ⊔ ℓ₁ , v₁′ ⟩ ≈⟨ β ⟩ᶜ ⟨ Σ₂ , μ₂ , pc ⊔ ℓ₂ , v₂′ ⟩
read-≈ᶜ pc⊑A ≈ᴾ (Labeledᴸ ℓ⊑A ≈ⱽ) = pcᴸ ≈ᴾ (join-⊑' pc⊑A ℓ⊑A) ≈ⱽ
read-≈ᶜ pc⊑A ≈ᴾ (Labeledᴴ ⋤₁ ⋤₂) = pcᴴ ≈ᴾ (join-⋤₂ ⋤₁) (join-⋤₂ ⋤₂)

--------------------------------------------------------------------------------
-- Properties: L-equivalence is an equivalence relation.

private module V = IProps Ty Value
private module L = IProps Ty LValue
private module E = IProps Ctx Env


mutual

  wken-≈ⱽ : V.Wkenᴮ _≈⟨_⟩ⱽ_
  wken-≈ⱽ ⊆₁ Unit = Unit
  wken-≈ⱽ ⊆₁ (Lbl ℓ) = Lbl ℓ
  wken-≈ⱽ ⊆₁ (Inl ≈ⱽ) = Inl (wken-≈ⱽ ⊆₁ ≈ⱽ)
  wken-≈ⱽ ⊆₁ (Inr ≈ⱽ) = Inr (wken-≈ⱽ ⊆₁ ≈ⱽ)
  wken-≈ⱽ ⊆₁ (Pair ≈ⱽ ≈ⱽ₁) = Pair (wken-≈ⱽ ⊆₁ ≈ⱽ) (wken-≈ⱽ ⊆₁ ≈ⱽ₁)
  wken-≈ⱽ ⊆₁ (Fun ≈ᴱ) = Fun (wken-≈ᴱ ⊆₁ ≈ᴱ)
  wken-≈ⱽ ⊆₁ (Thunk′ ≈ᴱ) = Thunk′ (wken-≈ᴱ ⊆₁ ≈ᴱ)
  wken-≈ⱽ ⊆₁ (Labeledᴸ x ≈ⱽ) = Labeledᴸ x (wken-≈ⱽ ⊆₁ ≈ⱽ)
  wken-≈ⱽ ⊆₁ (Labeledᴴ x x₁) = Labeledᴴ x x₁
  wken-≈ⱽ ⊆₁ (Ref-Iᴸ ℓ⊑A n) = Ref-Iᴸ ℓ⊑A n
  wken-≈ⱽ ⊆₁ (Ref-Iᴴ ℓ₁⋤A ℓ₂⋤A) = Ref-Iᴴ ℓ₁⋤A ℓ₂⋤A
  wken-≈ⱽ ⊆₁ (Ref-S ∈ᴮ) = Ref-S (bij-⊆ ⊆₁ ∈ᴮ)

  wken-≈ᴱ : E.Wkenᴮ _≈⟨_⟩ᴱ_
  wken-≈ᴱ ⊆₁ [] = []
  wken-≈ᴱ ⊆₁ (≈ⱽ ∷ ≈ᴱ) = wken-≈ⱽ ⊆₁ ≈ⱽ ∷ wken-≈ᴱ ⊆₁ ≈ᴱ

mutual

  -- Reflexive
  refl-≈ⱽ : V.Reflexiveᴮ _≈⟨_⟩ⱽ_ ∥_∥ⱽ
  refl-≈ⱽ {x = （）} = Unit
  refl-≈ⱽ {x = ⟨ e , θ ⟩ᶜ} = Fun refl-≈ᴱ
  refl-≈ⱽ {x = ⟨ t , θ ⟩ᵀ} = Thunk′ refl-≈ᴱ
  refl-≈ⱽ {x = inl v} = Inl refl-≈ⱽ
  refl-≈ⱽ {x = inr v} = Inr refl-≈ⱽ
  refl-≈ⱽ {x = ⟨ v₁ , v₂ ⟩} = Pair ≈₁ ≈₂
    where ≈₁ = wken-≈ⱽ (ι-⊆ (m≤m⊔n ∥ v₁ ∥ⱽ ∥ v₂ ∥ⱽ)) refl-≈ⱽ
          ≈₂ = wken-≈ⱽ (ι-⊆ (n≤m⊔n ∥ v₁ ∥ⱽ ∥ v₂ ∥ⱽ)) refl-≈ⱽ
  refl-≈ⱽ {x = Labeled ℓ v} with ℓ ⊑? A
  ... | yes p = Labeledᴸ p refl-≈ⱽ
  ... | no ¬p = Labeledᴴ ¬p ¬p
  refl-≈ⱽ {x = Refᴵ ℓ n} with ℓ ⊑? A
  ... | yes p = Ref-Iᴸ p n
  ... | no ¬p = Ref-Iᴴ ¬p ¬p
  refl-≈ⱽ {x = ⌞ ℓ ⌟} = Lbl ℓ
  refl-≈ⱽ {x = Refˢ x} = Ref-S (ι-∈ (s≤s ≤-refl))

  refl-≈ᴱ : E.Reflexiveᴮ _≈⟨_⟩ᴱ_ ∥_∥ᴱ
  refl-≈ᴱ {x = []} = []
  refl-≈ᴱ {x = v ∷ θ} = ≈₁ ∷ ≈₂
    where ≈₁ = wken-≈ⱽ (ι-⊆ (m≤m⊔n ∥ v ∥ⱽ ∥ θ ∥ᴱ)) refl-≈ⱽ
          ≈₂ = wken-≈ᴱ (ι-⊆ (n≤m⊔n ∥ v ∥ⱽ ∥ θ ∥ᴱ)) refl-≈ᴱ

  -- Symmetric
  sym-≈ⱽ : V.Symmetricᴮ _≈⟨_⟩ⱽ_
  sym-≈ⱽ Unit = Unit
  sym-≈ⱽ (Lbl ℓ) = Lbl ℓ
  sym-≈ⱽ (Inl v₁≈v₂) = Inl (sym-≈ⱽ v₁≈v₂)
  sym-≈ⱽ (Inr v₁≈v₂) = Inr (sym-≈ⱽ v₁≈v₂)
  sym-≈ⱽ (Pair v₁≈v₂ v₁≈v₂') = Pair (sym-≈ⱽ v₁≈v₂) (sym-≈ⱽ v₁≈v₂')
  sym-≈ⱽ (Fun θ₁≈θ₂) = Fun (sym-≈ᴱ θ₁≈θ₂)
  sym-≈ⱽ (Thunk′ θ₁≈θ₂) = Thunk′ (sym-≈ᴱ θ₁≈θ₂)
  sym-≈ⱽ (Labeledᴸ x v₁≈v₂) = Labeledᴸ x (sym-≈ⱽ v₁≈v₂)
  sym-≈ⱽ (Labeledᴴ x x₁) = Labeledᴴ x₁ x
  sym-≈ⱽ (Ref-Iᴸ ℓ⊑A n) = Ref-Iᴸ ℓ⊑A n
  sym-≈ⱽ (Ref-Iᴴ ℓ₁⋤A ℓ₂⋤A) = Ref-Iᴴ ℓ₂⋤A ℓ₁⋤A
  sym-≈ⱽ (Ref-S {β = β} x) = Ref-S (Bijectionᴾ.right-inverse-of β x)

  sym-≈ᴱ :  E.Symmetricᴮ _≈⟨_⟩ᴱ_
  sym-≈ᴱ [] = []
  sym-≈ᴱ (v₁≈v₂ ∷ θ₁≈θ₂) = sym-≈ⱽ v₁≈v₂ ∷ sym-≈ᴱ θ₁≈θ₂

  -- Transitive
  trans-≈ⱽ : V.Transitiveᴮ _≈⟨_⟩ⱽ_
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
  trans-≈ⱽ (Ref-Iᴸ ℓ⊑A n) (Ref-Iᴸ ℓ⊑A₁ .n) = Ref-Iᴸ ℓ⊑A₁ n
  trans-≈ⱽ (Ref-Iᴸ ℓ⊑A n) (Ref-Iᴴ ℓ₁⋤A ℓ₂⋤A) = ⊥-elim (ℓ₁⋤A ℓ⊑A)
  trans-≈ⱽ (Ref-Iᴴ ℓ₁⋤A ℓ₂⋤A) (Ref-Iᴸ ℓ⊑A n) = ⊥-elim (ℓ₂⋤A ℓ⊑A)
  trans-≈ⱽ (Ref-Iᴴ ℓ₁⋤A ℓ₂⋤A) (Ref-Iᴴ ℓ₁⋤A₁ ℓ₂⋤A₁) = Ref-Iᴴ ℓ₁⋤A ℓ₂⋤A₁
  trans-≈ⱽ (Ref-S {β = β₁} x) (Ref-S {β = β₂} y) = Ref-S (join-∈ᵗ {β₁ = β₁} {β₂} x y)

  trans-≈ᴱ : E.Transitiveᴮ _≈⟨_⟩ᴱ_
  trans-≈ᴱ [] [] = []
  trans-≈ᴱ (v₁≈v₂ ∷ θ₁≈θ₂) (v₂≈v₃ ∷ θ₂≈θ₃) = trans-≈ⱽ v₁≈v₂ v₂≈v₃ ∷ trans-≈ᴱ θ₁≈θ₂ θ₂≈θ₃

isEquivⱽ : V.IsEquivalenceᴮ _≈⟨_⟩ⱽ_ ∥_∥ⱽ
isEquivⱽ = record
           { reflᴮ = refl-≈ⱽ
           ; wkenᴮ = wken-≈ⱽ
           ; symᴮ = sym-≈ⱽ
           ; transᴮ = trans-≈ⱽ }

isEquivᴱ : E.IsEquivalenceᴮ _≈⟨_⟩ᴱ_  ∥_∥ᴱ
isEquivᴱ = record
           { reflᴮ = refl-≈ᴱ
           ; wkenᴮ = wken-≈ᴱ
           ; symᴮ = sym-≈ᴱ
           ; transᴮ = trans-≈ᴱ }

isEquivᴸ : L.IsEquivalenceᴮ _≈⟨_⟩ᴸ_  ∥_∥ᴸ
isEquivᴸ = record
         { reflᴮ = refl-≈ⱽ
         ; wkenᴮ = wken-≈ⱽ
         ; symᴮ = sym-≈ⱽ
         ; transᴮ = trans-≈ⱽ }

open import Generic.ValidEquivalence Ty

𝑽 : IsValidEquivalence Value _≈⟨_⟩ⱽ_
𝑽 = record { ∥_∥ = ∥_∥ⱽ ; isValid = isValidⱽ ; isEquiv = isEquivⱽ }

𝑳′ : IsValidEquivalence LValue _≈⟨_⟩ᴸ_
𝑳′ = record { ∥_∥ = ∥_∥ᴸ ; isValid = isValidᴸ ; isEquiv = isEquivᴸ }

open ≈ᴾ-Props 𝑽 𝑳′ public

-- ≈ⱽ-isEquivalence : ∀ {τ} → IsEquivalence (_≈ⱽ_ {τ})
-- ≈ⱽ-isEquivalence = record { refl = refl-≈ⱽ ; sym = sym-≈ⱽ ; trans = trans-≈ⱽ }

-- ≈ᴱ-isEquivalence : ∀ {Γ} → IsEquivalence (_≈ᴱ_ {Γ})
-- ≈ᴱ-isEquivalence = record { refl = refl-≈ᴱ ; sym = sym-≈ᴱ ; trans = trans-≈ᴱ }

-- open S.Props ≈ⱽ-isEquivalence public

-- ≈ᴬ-isEquivalence : ∀ {A : Set} → IsEquivalence (_≈ᴬ_ {A})
-- ≈ᴬ-isEquivalence =
--   record { refl = ⟨ refl-≈ˢ , refl , refl ⟩
--          ; sym = λ { ⟨ Σ₁≈Σ₂ , pc₁≡pc₂ , e₁≡e₂ ⟩ → ⟨ sym-≈ˢ Σ₁≈Σ₂ , sym pc₁≡pc₂ , sym e₁≡e₂ ⟩ }
--          ; trans = λ {⟨ Σ₁≈Σ₂ , pc₁≡pc₂ , e₁≡e₂ ⟩ ⟨ Σ₂≈Σ₃ , pc₂≡pc₃ , e₂≡e₃ ⟩ →
--                      ⟨ trans-≈ˢ Σ₁≈Σ₂ Σ₂≈Σ₃ , trans pc₁≡pc₂ pc₂≡pc₃ , trans e₁≡e₂ e₂≡e₃ ⟩ }
--          }

-- refl-≈ᶜ : ∀ {τ} {c : FConf τ} → c ≈ᶜ c
-- refl-≈ᶜ {c = ⟨ Σ , pc , v ⟩} with pc ⊑? A
-- ... | yes pc⊑A = pcᴸ refl-≈ˢ  pc⊑A refl-≈ⱽ
-- ... | no pc⋤A = pcᴴ refl-≈ˢ pc⋤A pc⋤A

-- sym-≈ᶜ : ∀ {τ} {c₁ c₂ : FConf τ} → c₁ ≈ᶜ c₂ → c₂ ≈ᶜ c₁
-- sym-≈ᶜ (pcᴸ Σ≈ pc⊑A v≈) = pcᴸ (sym-≈ˢ Σ≈) pc⊑A (sym-≈ⱽ v≈)
-- sym-≈ᶜ (pcᴴ Σ≈ pc₁⋤A pc₂⋤A) = pcᴴ (sym-≈ˢ Σ≈) pc₂⋤A pc₁⋤A

-- trans-≈ᶜ : ∀ {τ} {c₁ c₂ c₃ : FConf τ} → c₁ ≈ᶜ c₂ → c₂ ≈ᶜ c₃ → c₁ ≈ᶜ c₃
-- trans-≈ᶜ (pcᴸ Σ≈ pc⊑A v≈) (pcᴸ Σ≈₁ pc⊑A₁ v≈₁) = pcᴸ (trans-≈ˢ Σ≈ Σ≈₁) pc⊑A (trans-≈ⱽ v≈ v≈₁)
-- trans-≈ᶜ (pcᴸ Σ≈ pc⊑A v≈) (pcᴴ Σ≈₁ pc₁⋤A pc₂⋤A) = ⊥-elim (pc₁⋤A pc⊑A)
-- trans-≈ᶜ (pcᴴ Σ≈ pc₁⋤A pc₂⋤A) (pcᴸ Σ≈₁ pc⊑A v≈) = ⊥-elim (pc₂⋤A pc⊑A)
-- trans-≈ᶜ (pcᴴ Σ≈ pc₁⋤A pc₂⋤A) (pcᴴ Σ≈₁ pc₁⋤A₁ pc₂⋤A₁) = pcᴴ (trans-≈ˢ Σ≈ Σ≈₁) pc₁⋤A pc₂⋤A₁

-- -- Projects low-equivalence for stores
-- ≈ᶜ-≈ˢ : ∀ {τ} {c₁ c₂ : FConf τ} → c₁ ≈ᶜ c₂ → store c₁ ≈ˢ store c₂
-- ≈ᶜ-≈ˢ (pcᴸ x x₁ x₂) = x
-- ≈ᶜ-≈ˢ (pcᴴ x x₁ x₂) = x

-- ≈ᶜ-isEquivalence : ∀ {τ} → IsEquivalence (_≈ᶜ_ {τ})
-- ≈ᶜ-isEquivalence = record { refl = refl-≈ᶜ ; sym = sym-≈ᶜ ; trans = trans-≈ᶜ }
