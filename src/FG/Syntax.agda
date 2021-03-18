-- Well-typed syntax

open import Lattice

module FG.Syntax {{𝑳 : Lattice}} where

open import FG.Types

open import Data.Nat using (ℕ)


-- (e : Expr Γ τ) represents a term t of type τ in the context Γ,
-- i.e., Γ ⊢ t ∷ τ. Note that this definition merges syntax and tpying
-- judgment: only well-typed terms can be constructed with it.
data Expr (Γ : Ctx) : Ty → Set where

  -- Unit
  （） : Expr Γ unit

  --------------------------------------------------------------------------------
  -- Basic λ-calculus

  -- Variables with De Bruijn indexes
  var : ∀ {τ} →  (τ∈Γ : τ ∈ Γ) → Expr Γ τ

  -- Functions
  Λ : ∀ {τ₁ τ₂} → Expr (τ₁ ∷ Γ) τ₂ → Expr Γ (τ₁ ➔ τ₂)

  -- Function application
  _∘_ : ∀ {τ₁ τ₂} → Expr Γ (τ₁ ➔ τ₂) → Expr Γ τ₁ → Expr Γ τ₂

  --------------------------------------------------------------------------------
  -- Explicit Weakening

  wken : ∀ {τ Γ'} → Expr Γ' τ → Γ' ⊆ Γ → Expr Γ τ

  --------------------------------------------------------------------------------
  -- Pairs

  ⟨_,_⟩ : ∀ {τ₁ τ₂} → Expr Γ τ₁ → Expr Γ τ₂ → Expr Γ (τ₁ × τ₂)

  fst : ∀ {τ₁ τ₂} → Expr Γ (τ₁ × τ₂) → Expr Γ τ₁

  snd : ∀ {τ₁ τ₂} → Expr Γ (τ₁ × τ₂) → Expr Γ τ₂

  --------------------------------------------------------------------------------
  -- Sum

  inl : ∀ {τ₁ τ₂} → Expr Γ τ₁ → Expr Γ (τ₁ + τ₂)

  inr : ∀ {τ₁ τ₂} → Expr Γ τ₂ → Expr Γ (τ₁ + τ₂)

  case : ∀ {τ₁ τ₂ τ₃} → Expr Γ (τ₁ + τ₂) → Expr (τ₁ ∷ Γ) τ₃ → Expr (τ₂ ∷ Γ) τ₃ → Expr Γ τ₃

  --------------------------------------------------------------------------------
  -- Labels are first class citizens

  ⌞_⌟ : (ℓ : Label)  → Expr Γ 𝓛

  -- ℓ₁ ⊑-? ℓ₂ tests if ℓ₁ can flow to ℓ₂
  _⊑-?_ : Expr Γ 𝓛 → Expr Γ 𝓛 → Expr Γ Bool

  -- Retrieve the label of the context (program counter).
  getLabel : Expr Γ 𝓛

  --------------------------------------------------------------------------------

  -- Retrieve the label of a labeled value
  labelOf : ∀ {τ} → Expr Γ τ → Expr Γ 𝓛

  -- taint(ℓ,e) evaluates e in a context tainted with ℓ.
  taint : ∀ {τ} → Expr Γ 𝓛 → Expr Γ τ → Expr Γ τ


  --------------------------------------------------------------------------------
  -- Memory

  -- Retrieve the label of a labeled reference
  labelOfRef : ∀ {τ s} → Expr Γ (Ref s τ) → Expr Γ 𝓛

  -- Creates a new mutable reference
  new : ∀ {τ s} → Expr Γ τ → Expr Γ (Ref s τ)

  -- Reads the content of a mutable reference
  !_ : ∀ {τ s} → Expr Γ (Ref s τ) → Expr Γ τ

  -- Overvwrites the content of a mutable reference
  _≔_ : ∀ {τ s} → Expr Γ (Ref s τ) → Expr Γ τ → Expr Γ unit

  --------------------------------------------------------------------------------
  -- Identity type

  -- Constructor
  Id : ∀ {τ} → Expr Γ τ → Expr Γ (Id τ)

  -- Deconstructor
  unId : ∀ {τ} → Expr Γ (Id τ) → Expr Γ τ

mutual

  -- Raw values
  data Raw : Ty → Set where

    （） : Raw unit

    -- Closure
    ⟨_,_⟩ᶜ : ∀ {Γ τ₁ τ₂} → Expr (τ₁ ∷ Γ) τ₂ → (θ : Env Γ) → Raw (τ₁ ➔ τ₂)

    inl : ∀ {τ₁ τ₂} → Value τ₁ → Raw (τ₁ + τ₂)

    inr : ∀ {τ₁ τ₂} → Value τ₂ → Raw (τ₁ + τ₂)

    ⟨_,_⟩ : ∀ {τ₁ τ₂} → Value τ₁ → Value τ₂ → Raw (τ₁ × τ₂)

    Refᴵ : ∀ {τ} → Label → ℕ → Raw (Ref I τ)

    Refˢ : ∀ {τ} → ℕ → Raw (Ref S τ)

    ⌞_⌟ : Label → Raw 𝓛

    Id : ∀ {τ} → Value τ → Raw (Id τ)

  -- Labeled values, i.e., a raw value paired with a label.
  record Value (τ : Ty) : Set where
    inductive
    constructor _^_
    field raw : Raw τ
          lbl : Label

  -- A typed environment Env Γ contains values of type given by Γ.
  data Env : (Γ : Ctx) → Set where
    [] : Env []
    _∷_  : ∀ {Γ τ} → (v : Value τ) (θ : Env Γ) → Env (τ ∷ Γ)

open Value public

true : ∀ ℓ → Raw Bool
true ℓ = inl (（） ^ ℓ) -- TODO: Not sure if I should use bottom here?

false : ∀ ℓ → Raw Bool
false ℓ = inr ((（） ^ ℓ))

if_then_else_ : ∀ {Γ τ} → Expr Γ Bool → Expr Γ τ → Expr Γ τ → Expr Γ τ
if_then_else_ c t e = case c (wken t (drop refl-⊆)) (wken e (drop refl-⊆))

--------------------------------------------------------------------------------
-- Configurations

-- Generic store and flow-sensitive heap
open import Generic.PState Ty Ty Raw Value public

-- Generic configuration container.
record Conf (A : Set) : Set where
  constructor ⟨_,_,_⟩
  field store : Store
        heap : Heap
        term : A

-- Initial configuration.
IConf : Ctx → Ty → Set
IConf Γ τ = Conf (Expr Γ τ)

-- Final configuration
FConf : Ty → Set
FConf τ = Conf (Value τ)

--------------------------------------------------------------------------------
-- Weakening once and twice.

_↑¹ : ∀ {Γ τ τ₁} → Expr Γ τ → Expr (τ₁ ∷ Γ) τ
e ↑¹ = wken e (drop refl-⊆)

_↑² : ∀ {Γ τ τ₁ τ₂} → Expr Γ τ → Expr (τ₁ ∷ τ₂ ∷ Γ) τ
e ↑² = wken e (drop (drop refl-⊆))

--------------------------------------------------------------------------------

-- Lookup a variable in the environment.
_!!_ : ∀ {Γ τ} → Env Γ → τ ∈ Γ → Value τ
(v ∷ θ) !! here = v
(v ∷ θ) !! (there x) = θ !! x

-- Shrink enviroment.
slice : ∀ {Γ₁ Γ₂} → Env Γ₂ → Γ₁ ⊆ Γ₂ → Env Γ₁
slice [] base = []
slice (v ∷ θ) (cons p) = v ∷ slice θ p
slice (v ∷ θ) (drop p) = slice θ p

-- Merge environemnt.
_++ᴱ_ : ∀ {Γ₁ Γ₂} → Env Γ₁ → Env Γ₂ → Env (Γ₁ ++ Γ₂)
[] ++ᴱ θ₂ = θ₂
(v ∷ θ₁) ++ᴱ θ₂ = v ∷ (θ₁ ++ᴱ θ₂)

--------------------------------------------------------------------------------
-- Basic proofs and rewriting.

open import Relation.Binary.PropositionalEquality

slice-refl-⊆-≡ : ∀ {Γ} {θ : Env Γ} → slice θ refl-⊆ ≡ θ
slice-refl-⊆-≡ {θ = []} = refl
slice-refl-⊆-≡ {θ = v ∷ θ} rewrite slice-refl-⊆-≡ {_} {θ} = refl

{-# REWRITE slice-refl-⊆-≡ #-}

slice-drop-⊆-≡ : ∀ {Γ₁ Γ₂} (θ₁ : Env Γ₁) (θ₂ : Env Γ₂) → slice (θ₂ ++ᴱ θ₁) (drop-⊆₂ Γ₁ Γ₂) ≡ θ₁
slice-drop-⊆-≡ θ₁ [] = refl
slice-drop-⊆-≡ θ₁ (v ∷ θ₂) = slice-drop-⊆-≡ θ₁ θ₂

{-# REWRITE slice-drop-⊆-≡ #-}

--------------------------------------------------------------------------------
