open import Lattice

module CG {{𝑳 : Lattice}} where

-- Types and context
open import CG.Types public

-- Well-typed Syntax
open import CG.Syntax public

-- Big-step semantics
open import CG.Semantics public

--------------------------------------------------------------------------------
-- Top-level L-equivalence bindings that explicitly take the attacker
-- security level.

_≈ᴵ⟨_⟩_ : ∀ {τ Γ} → EConf Γ τ → Label → EConf Γ τ → Set
c₁ ≈ᴵ⟨ A ⟩ c₂ = c₁ ≈ᴵ c₂
  where open import CG.LowEq A

_≈ⱽ⟨_⟩_ : ∀ {τ} → Value τ → Label → Value τ → Set
v₁ ≈ⱽ⟨ A ⟩ v₂ = v₁ ≈ⱽ v₂
  where open import CG.LowEq A

_≈ᴱ⟨_⟩_ : ∀ {Γ} → Env Γ → Label → Env Γ → Set
r₁ ≈ᴱ⟨ A ⟩ r₂ = r₁ ≈ᴱ r₂
  where open import CG.LowEq A

_≈ᶜ⟨_⟩_ : ∀ {τ} → FConf τ → Label → FConf τ → Set
c₁ ≈ᶜ⟨ A ⟩ c₂ = c₁ ≈ᶜ c₂
  where open import CG.LowEq A

--------------------------------------------------------------------------------
-- Calculus record

open import Generic.Calculus

λ^CG : Calculus
λ^CG = record
         { Ty = Ty
         ; Input = Env
         ; IConf = EConf
         ; FConf = FConf
         ; I = LIO
         ; _⇓⟨_⟩_ = _⇓ᶠ⟨_⟩_
         ; _≈ᴱ⟨_⟩_ = _≈ᴱ⟨_⟩_
         ; _≈ᴵ⟨_⟩_ = _≈ᴵ⟨_⟩_
         ; _≈ᶠ⟨_⟩_ = _≈ᶜ⟨_⟩_
         }


CG-TINI : TINI λ^CG
CG-TINI {A = A} = tiniᶠ
  where open import CG.Security A
