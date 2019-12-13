open import Lattice

module FG {{𝑳 : Lattice}} where

-- Types and context
open import FG.Types public

-- Well-typed Syntax
open import FG.Syntax public

-- Big-step semantics
open import FG.Semantics public

--------------------------------------------------------------------------------
-- Top-level low-equivalence bindings that explicitly take the
-- adversary security level

_≈ᴵ⟨_⟩_ : ∀ {τ Γ} → IConf Γ τ → Label → IConf Γ τ → Set
c₁ ≈ᴵ⟨ A ⟩ c₂ = c₁ ≈ᴵ c₂
  where open import FG.LowEq A

_≈ᶜ⟨_⟩_ : ∀ {τ} → FConf τ → Label → FConf τ → Set
c₁ ≈ᶜ⟨ A ⟩ c₂ = c₁ ≈ᶜ c₂
  where open import FG.LowEq A

_≈ⱽ⟨_⟩_ : ∀ {τ} → Value τ → Label → Value τ → Set
v₁ ≈ⱽ⟨ A ⟩ v₂ = v₁ ≈ⱽ v₂
  where open import FG.LowEq A

_≈ᴿ⟨_⟩_ : ∀ {τ} → Raw τ → Label → Raw τ → Set
r₁ ≈ᴿ⟨ A ⟩ r₂ = r₁ ≈ᴿ r₂
  where open import FG.LowEq A

_≈ᴱ⟨_⟩_ : ∀ {Γ} → Env Γ → Label → Env Γ → Set
r₁ ≈ᴱ⟨ A ⟩ r₂ = r₁ ≈ᴱ r₂
  where open import FG.LowEq A

_≈ᴹ⟨_⟩_ : ∀ {ℓ} → Memory ℓ → Label → Memory ℓ → Set
M₁ ≈ᴹ⟨ A ⟩ M₂ = M₁ ≈⟨ _ ⊑? A  ⟩ᴹ M₂
  where open import FG.LowEq A

_≈ˢ⟨_⟩_ : Store → Label → Store → Set
Σ₁ ≈ˢ⟨ A ⟩ Σ₂ = Σ₁ ≈ˢ Σ₂
  where open import FG.LowEq A

--------------------------------------------------------------------------------
-- Calculus record

open import Generic.Calculus
open import Function
open import Data.Product renaming (_×_ to _∧_)
open import Relation.Binary.PropositionalEquality

λ^FG : Calculus
λ^FG = record
         { Ty = Ty
         ; Input = λ Γ → (Env Γ) ∧ Label
         ; IConf = IConf
         ; FConf = FConf
         ; I⟨_⟩ = id
         ; _⇓⟨_⟩_ = λ { c (θ , pc) c' → c ⇓⟨ θ , pc ⟩ c' }
         ; _≈ᴱ⟨_⟩_ = λ { (θ₁ , pc₁) A (θ₂ , pc₂) → θ₁ ≈ᴱ⟨ A ⟩ θ₂ ∧ pc₁ ≡ pc₂}
         ; _≈ᴵ⟨_⟩_ = _≈ᴵ⟨_⟩_
         ; _≈ᶠ⟨_⟩_ = _≈ᶜ⟨_⟩_
         }

λ^FG-TINI : TINI λ^FG
λ^FG-TINI {A = A} c₁⇓ c₂⇓ c₁≈c₂ (θ₁≈θ₂ , refl) = tini c₁⇓ c₂⇓ c₁≈c₂ θ₁≈θ₂
  where open import FG.Security A
        open Calculus λ^FG
