open import Lattice

module FG {{𝑳 : Lattice}} where

-- Types and context
open import FG.Types public

-- Well-typed Syntax
open import FG.Syntax public

-- Big-step semantics
open import FG.Semantics public

-- References are valid
open import FG.Valid public

-- Bijections
open import Generic.Bijection hiding (id)

--------------------------------------------------------------------------------
-- Top-level low-equivalence bindings that explicitly take the
-- adversary security level

_≈ᴵ⟨_,_⟩_ : ∀ {τ Γ} → IConf Γ τ → Label → Bij → IConf Γ τ → Set
c₁ ≈ᴵ⟨ A , β ⟩ c₂ = c₁ ≈⟨ β ⟩ᴵ c₂
  where open import FG.LowEq A

_≈ᶜ⟨_,_⟩_ : ∀ {τ} → FConf τ → Label → Bij → FConf τ → Set
c₁ ≈ᶜ⟨ A , β ⟩ c₂ = c₁ ≈⟨ β ⟩ᶜ c₂
  where open import FG.LowEq A

_≈ⱽ⟨_,_⟩_ : ∀ {τ} → Value τ → Label → Bij → Value τ → Set
v₁ ≈ⱽ⟨ A , β ⟩ v₂ = v₁ ≈⟨ β ⟩ⱽ v₂
  where open import FG.LowEq A

_≈ᴿ⟨_,_⟩_ : ∀ {τ} → Raw τ → Label → Bij → Raw τ → Set
r₁ ≈ᴿ⟨ A , β ⟩ r₂ = r₁ ≈⟨ β ⟩ᴿ r₂
  where open import FG.LowEq A

_≈ᴱ⟨_,_⟩_ : ∀ {Γ} → Env Γ → Label → Bij → Env Γ → Set
r₁ ≈ᴱ⟨ A , β ⟩ r₂ = r₁ ≈⟨ β ⟩ᴱ r₂
  where open import FG.LowEq A

_≈ᴹ⟨_,_⟩_ : ∀ {ℓ} → Memory ℓ → Label → Bij → Memory ℓ → Set
M₁ ≈ᴹ⟨ A , β ⟩ M₂ = M₁ ≈⟨ β , _ ⊑? A ⟩ᴹ M₂
  where open import FG.LowEq A

_≈ˢ⟨_,_⟩_ : Store → Label → Bij → Store → Set
Σ₁ ≈ˢ⟨ A , β ⟩ Σ₂ = Σ₁ ≈⟨ β ⟩ˢ Σ₂
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
         ; Valid-Inputs = λ { c (θ , ℓ) → Valid-Inputs c θ }
         ; I⟨_⟩ = id
         ; _⇓⟨_⟩_ = λ { c (θ , pc) c' → c ⇓⟨ θ , pc ⟩ c' }
         ; _≈ᴱ⟨_,_⟩_ = λ { (θ₁ , pc₁) A β (θ₂ , pc₂) → θ₁ ≈ᴱ⟨ A , β ⟩ θ₂ ∧ pc₁ ≡ pc₂}
         ; _≈ᴵ⟨_,_⟩_ = _≈ᴵ⟨_,_⟩_
         ; _≈ᶠ⟨_,_⟩_ = _≈ᶜ⟨_,_⟩_
         }

λ^FG-TINI : TINI λ^FG
λ^FG-TINI {A = A} isV₁ isV₂ c₁⇓ c₂⇓ c₁≈c₂ (θ₁≈θ₂ , refl)
  = tini {{ isV₁ }} {{ isV₂ }} c₁⇓ c₂⇓ c₁≈c₂ θ₁≈θ₂
  where open import FG.Security A
        open Calculus λ^FG
