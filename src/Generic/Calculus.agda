module Generic.Calculus where

open import Data.List
open import Generic.Context using (Ctx)
open import Relation.Binary
open import Level
open import Lattice
open import Generic.Bijection

-- TODO: why is this here?
-- A simple flag to distinguish flow-insensitive (I) and
-- flow-sensitive (S) references
data Flow : Set where
  I S : Flow

-- A generic record for security calculi with well-typed syntax and
-- big-step semantics.
record Calculus {{𝑳 : Lattice}} : Set₁ where
  field Ty : Set
        Input : Ctx Ty → Set
        IConf : Ctx Ty → Ty → Set
        FConf : Ty → Set
        I⟨_⟩ : Ty → Ty -- Generic type preservation in the semantics
        _⇓⟨_⟩_ : ∀ {Γ τ} → IConf Γ I⟨ τ ⟩ → Input Γ → FConf τ → Set
        Valid-Inputs : ∀ {Γ} {τ} → IConf Γ τ → Input Γ →  Set

        -- Low-equivalence
        _≈ᴱ⟨_,_⟩_ : ∀ {Γ} → Input Γ → Label → Bij → Input Γ → Set
        _≈ᴵ⟨_,_⟩_ : ∀ {Γ τ} → IConf Γ τ → Label → Bij → IConf Γ τ → Set
        _≈ᶠ⟨_,_⟩_ : ∀ {τ} → FConf τ → Label → Bij → FConf τ → Set

-- TODO: here we could make the statement simpler (e.g., empty
-- memory/store, only boolean inputs, no assumptions about validity)
-- but this seems just more boring work.

-- Generic Termination-Insensitive Non-Interferencee property (TINI).
TINI : ∀ {{𝑳 : Lattice}} → Calculus → Set
TINI 𝑪 = ∀ {τ Γ θ₁ θ₂ A β} {c₁ c₂ : IConf Γ I⟨ τ ⟩} {c₁' c₂' : FConf τ} →
              Valid-Inputs c₁ θ₁ →
              Valid-Inputs c₂ θ₂ →
              c₁ ⇓⟨ θ₁ ⟩ c₁' →
              c₂ ⇓⟨ θ₂ ⟩ c₂' →
              c₁ ≈ᴵ⟨ A , β ⟩ c₂ →
              θ₁ ≈ᴱ⟨ A , β ⟩ θ₂ →
              ∃ (λ β' → β ⊆ β' × c₁' ≈ᶠ⟨ A , β' ⟩ c₂')
     where open Calculus 𝑪
           open import Data.Product using (_×_ ; ∃)
