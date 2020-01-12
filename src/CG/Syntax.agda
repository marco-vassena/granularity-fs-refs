-- Well-typed syntax

open import Lattice

module CG.Syntax {{𝑳 : Lattice}} where

open import CG.Types
open import Data.Nat using (ℕ)

mutual

  -- (e : Expr Γ τ) represents a term t of type τ in the context Γ,
  -- i.e., Γ ⊢ t ∷ τ. Note that this definition merges syntax and tpying
  -- judgment: only well-typed terms can be constructed with it.
  data Expr (Γ : Ctx) : Ty → Set where

    -- Unit
    （） : Expr Γ unit

    -- First class labels.
    ⌞_⌟ : (ℓ : Label) → Expr Γ 𝓛

    -- ℓ₁ ⊑-? ℓ₂ tests if ℓ₁ can flow to ℓ₂
    _⊑-?_ : Expr Γ 𝓛 → Expr Γ 𝓛 → Expr Γ Bool

    --------------------------------------------------------------------------------
    -- Basic λ-calculus

    -- Variables with De Bruijn indexes
    var : ∀ {τ} →  (τ∈Γ : τ ∈ Γ) → Expr Γ τ

    -- Functions
    Λ : ∀ {τ₁ τ₂} → Expr (τ₁ ∷ Γ) τ₂ → Expr Γ (τ₁ ➔ τ₂)

    -- Function application
    _∘_ : ∀ {τ₁ τ₂} → Expr Γ (τ₁ ➔ τ₂) → Expr Γ τ₁ → Expr Γ τ₂

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
    -- Lifts a Thunk (LIO computation) to Expr.

    ⌞_⌟ᵀ : ∀ {τ} → (t : Thunk Γ (LIO τ)) → Expr Γ (LIO τ)

    --------------------------------------------------------------------------------
    -- Explicit weakening

    wken : ∀ {τ Γ'} → Expr Γ' τ → Γ' ⊆ Γ → Expr Γ τ

  -- LIO monad
  data Thunk (Γ : Ctx) : Ty → Set where

    -- Encapsulates a value in the monad
    return : ∀ {τ} → Expr Γ τ → Thunk Γ (LIO τ)

    -- Monadic bind
    bind : ∀ {τ₁ τ₂} → Expr Γ (LIO τ₁) → Expr (τ₁ ∷ Γ) (LIO τ₂) → Thunk Γ (LIO τ₂)

    --------------------------------------------------------------------------------
    -- Basic labeled values

    -- Unlabel a labeled value
    unlabel : ∀ {τ} → Expr Γ (Labeled τ) → Thunk Γ (LIO τ)

    -- toLabeled creates a labeled value out of an LIO computation
    toLabeled : ∀ {τ} → Expr Γ (LIO τ) → Thunk Γ (LIO (Labeled τ))

   --------------------------------------------------------------------------------
   -- Label introspection.

    -- Retrieve the label of a labeled value
    labelOf : ∀ {τ} → Expr Γ (Labeled τ) → Thunk Γ (LIO 𝓛)

    -- Retrieve the current label of the context, i.e., the program counter
    getLabel : Thunk Γ (LIO 𝓛)

    -- taint(ℓ) raises the program counter to ℓ
    taint : Expr Γ 𝓛 → Thunk Γ (LIO unit)

   --------------------------------------------------------------------------------
   -- Memory operations.

    -- Creates a new mutable reference at a given security level
    new : ∀ {τ} → Expr Γ (Labeled τ) → Thunk Γ (LIO (Ref τ))

    -- Reads the content of a mutable reference
    !_ : ∀ {τ} → Expr Γ (Ref τ) → Thunk Γ (LIO τ)

    -- Overvwrites the content of a mutable reference
    _≔_ : ∀ {τ} → Expr Γ (Ref τ) → Expr Γ (Labeled τ) → Thunk Γ (LIO unit)

    -- Retrieve the label of a labeled reference
    labelOfRef : ∀ {τ} → Expr Γ (Ref τ) → Thunk Γ (LIO 𝓛)

  -- Value enviroment
  data Env : (Γ : Ctx) → Set where
    [] : Env []
    _∷_  : ∀ {Γ τ} → (v : Value τ) (θ : Env Γ) → Env (τ ∷ Γ)

  -- Value.
  data Value : Ty → Set where

    （） : Value unit

    -- Function closure
    ⟨_,_⟩ᶜ : ∀ {Γ τ₁ τ₂} → (e : Expr (τ₁ ∷ Γ) τ₂) (θ : Env Γ) → Value (τ₁ ➔ τ₂)

    -- Thunk closure
    ⟨_,_⟩ᵀ : ∀ {Γ τ} → (t : Thunk Γ (LIO τ)) (θ : Env Γ) → Value (LIO τ)

    inl : ∀ {τ₁ τ₂} → Value τ₁ → Value (τ₁ + τ₂)

    inr : ∀ {τ₁ τ₂} → Value τ₂ → Value (τ₁ + τ₂)

    ⟨_,_⟩ : ∀ {τ₁ τ₂} → Value τ₁ → Value τ₂ → Value (τ₁ × τ₂)

    -- Labeled value
    Labeled : ∀ {τ} (ℓ : Label) → Value τ → Value (Labeled τ)

    -- Labeled reference
    Ref : ∀ {τ} (ℓ : Label) (n : ℕ) → Value (Ref τ)

    -- First class labels
    ⌞_⌟ : (ℓ : Label) → Value 𝓛


infixr 5 _∷_

-- Shorthands for Booleans

true : Value Bool
true = inl （）

false : Value Bool
false = inr （）

if_then_else_ : ∀ {Γ τ} → Expr Γ Bool → Expr Γ τ → Expr Γ τ → Expr Γ τ
if_then_else_ c t e = case c (wken t (drop refl-⊆)) (wken e (drop refl-⊆))

--------------------------------------------------------------------------------
-- Implementation of the HasLabel generic interface for Labeled values

open import Generic.LValue

𝑯 : HasLabel Ty Value
𝑯 = record { F = Labeled ;
             value = λ { (Labeled ℓ v) → v } ;
             label = λ { (Labeled ℓ v) → ℓ } }
  where open import Function

--------------------------------------------------------------------------------
-- Configurations

-- Generic store.
open import Generic.Store Ty Value public

-- Generic configuration container.
record Conf (A : Set) : Set where
  constructor ⟨_,_,_⟩
  field store : Store
        pc : Label
        term : A

-- Initial Configuration (Expr)
EConf : Ctx → Ty → Set
EConf Γ τ = Conf (Expr Γ τ)

-- Initial Configuration (Thunk)
TConf : Ctx → Ty → Set
TConf Γ τ = Conf (Thunk Γ τ)

-- Final configuration (Value)
FConf : Ty → Set
FConf τ = Conf (Value τ)

-- Projections

expr : ∀ {Γ τ} → EConf Γ τ → Expr Γ τ
expr = Conf.term

thunk :  ∀ {Γ τ} → TConf Γ τ → Thunk Γ τ
thunk = Conf.term

val : ∀ {τ} → FConf τ → Value τ
val = Conf.term

--------------------------------------------------------------------------------
-- Weakening once and twice.

_↑¹ : ∀ {Γ τ τ₁} → Expr Γ τ → Expr (τ₁ ∷ Γ) τ
e ↑¹ = wken e (drop refl-⊆)

_↑² : ∀ {Γ τ τ₁ τ₂} → Expr Γ τ → Expr (τ₂ ∷ τ₁ ∷ Γ) τ
e ↑² = wken e (drop (drop refl-⊆))

--------------------------------------------------------------------------------
-- Environment operations and proofs

-- Merge environments.
_++ᴱ_ : ∀ {Γ₁ Γ₂} → Env Γ₁ → Env Γ₂ → Env (Γ₁ ++ Γ₂)
[] ++ᴱ θ₂ = θ₂
(v ∷ θ₁) ++ᴱ θ₂ = v ∷ (θ₁ ++ᴱ θ₂)

-- Lookup a variable in the environment.
_!!_ : ∀ {τ Γ} → Env Γ → τ ∈ Γ → Value τ
(v ∷ θ) !! here = v
(v ∷ θ) !! (there τ∈Γ) = θ !! τ∈Γ

-- Shrink enviroment.
slice : ∀ {Γ₁ Γ₂} → Env Γ₂ → Γ₁ ⊆ Γ₂ → Env Γ₁
slice [] base = []
slice (v ∷ θ) (cons p) = v ∷ slice θ p
slice (v ∷ θ) (drop p) = slice θ p

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
