open import Lattice

module CG {{𝑳 : Lattice}} where

-- Types and context
open import CG.Types public

-- Well-typed Syntax
open import CG.Syntax public

-- Big-step semantics
open import CG.Semantics public

-- References are valid
open import CG.Valid public

-- Bijections
open import Generic.Bijection

--------------------------------------------------------------------------------
-- Top-level L-equivalence bindings that explicitly take the attacker
-- security level.

_≈ᴵ⟨_,_⟩_ : ∀ {τ Γ} → EConf Γ τ → Label → Bij → EConf Γ τ → Set
c₁ ≈ᴵ⟨ A , β ⟩ c₂ = c₁ ≈⟨ β ⟩ᴵ c₂
  where open import CG.LowEq A

_≈ⱽ⟨_,_⟩_ : ∀ {τ} → Value τ → Label → Bij → Value τ → Set
v₁ ≈ⱽ⟨ A , β ⟩ v₂ = v₁ ≈⟨ β ⟩ⱽ v₂
  where open import CG.LowEq A

_≈ᴱ⟨_,_⟩_ : ∀ {Γ} → Env Γ → Label → Bij → Env Γ → Set
r₁ ≈ᴱ⟨ A , β ⟩ r₂ = r₁ ≈⟨ β ⟩ᴱ r₂
  where open import CG.LowEq A

_≈ᶜ⟨_,_⟩_ : ∀ {τ} → FConf τ → Label → Bij → FConf τ → Set
c₁ ≈ᶜ⟨ A , β ⟩ c₂ = c₁ ≈⟨ β ⟩ᶜ c₂
  where open import CG.LowEq A

_≈ᴹ⟨_,_⟩_ : ∀ {ℓ} → Memory ℓ → Label → Bij → Memory ℓ → Set
M₁ ≈ᴹ⟨ A , β ⟩ M₂ = M₁ ≈⟨ β , _ ⊑? A ⟩ᴹ M₂
  where open import CG.LowEq A

_≈ˢ⟨_,_⟩_ : Store → Label → Bij → Store → Set
Σ₁ ≈ˢ⟨ A , β ⟩ Σ₂ = Σ₁ ≈⟨ β ⟩ˢ Σ₂
  where open import CG.LowEq A

--------------------------------------------------------------------------------
-- Calculus record

open import Generic.Calculus
open import CG.Valid

λ^CG : Calculus
λ^CG = record
         { Ty = Ty
         ; Input = Env
         ; IConf = EConf
         ; FConf = FConf
         ; Valid-Inputs = Valid-Inputs
         ; I⟨_⟩ = LIO
         ; _⇓⟨_⟩_ = _⇓ᶠ⟨_⟩_
         ; _≈ᴱ⟨_,_⟩_ = _≈ᴱ⟨_,_⟩_
         ; _≈ᴵ⟨_,_⟩_ = _≈ᴵ⟨_,_⟩_
         ; _≈ᶠ⟨_,_⟩_ = _≈ᶜ⟨_,_⟩_
         }

CG-TINI : TINI λ^CG
CG-TINI {A = A} isV₁ isV₂ = tiniᶠ {{isV₁}} {{isV₂}}
  where open import CG.Security A
