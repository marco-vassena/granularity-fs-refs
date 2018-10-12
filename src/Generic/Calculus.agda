module Generic.Calculus where

open import Data.List
open import Generic.Context
open import Relation.Binary
open import Level
open import Lattice

-- A generic record for security calculi with well-typed syntax and
-- big-step semantics.
record Calculus {{𝑳 : Lattice}} : Set₁ where
  field Ty : Set
        Input : Ctx Ty → Set
        IConf : Ctx Ty → Ty → Set
        FConf : Ty → Set
        I : Ty → Ty -- Generic type preservation in the semantics
        _⇓⟨_⟩_ : ∀ {Γ τ} → IConf Γ (I τ) → Input Γ → FConf τ → Set

        -- Low-equivalence
        _≈ᴱ⟨_⟩_ : ∀ {Γ} → Input Γ → Label → Input Γ → Set
        _≈ᴵ⟨_⟩_ : ∀ {Γ τ} → IConf Γ τ → Label → IConf Γ τ → Set
        _≈ᶠ⟨_⟩_ : ∀ {τ} → FConf τ → Label → FConf τ → Set

-- Generic Termination-Insensitive Non-Interferencee property (TINI).
TINI : ∀ {{𝑳 : Lattice}} → Calculus → Set
TINI 𝑪 = ∀ {τ Γ θ₁ θ₂ A} {c₁ c₂ : IConf Γ (I τ)} {c₁' c₂' : FConf τ} →
              c₁ ⇓⟨ θ₁ ⟩ c₁' →
              c₂ ⇓⟨ θ₂ ⟩ c₂' →
              c₁ ≈ᴵ⟨ A ⟩ c₂ →
              θ₁ ≈ᴱ⟨ A ⟩ θ₂ →
              c₁' ≈ᶠ⟨ A ⟩ c₂'
     where open Calculus 𝑪
