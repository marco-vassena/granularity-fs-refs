module Generic.Bijection where

open import Function as F hiding (flip)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality as P
open import Function.Bijection renaming (_∘_ to _∘ᴮ_) public   -- rexport composition
open import Function.Bijection as B
open import Data.Empty
open import Data.Nat
open import Data.Maybe

--------------------------------------------------------------------------------
-- (From a more recent version of Agda lib)
-- The set of all bijections between two sets (i.e. bijections with
-- propositional equality)

infix 3 _⤖_

_⤖_ : ∀ {f t} → Set f → Set t → Set _
From ⤖ To = Bijection (P.setoid From) (P.setoid To)

bijection : ∀ {f t} {From : Set f} {To : Set t} →
            (to : From → To) (from : To → From) →
            (∀ {x y} → to x ≡ to y → x ≡ y) →
            (∀ x → to (from x) ≡ x) →
            From ⤖ To
bijection to from inj invʳ = record
  { to        = P.→-to-⟶ to
  ; bijective = record
    { injective  = inj
    ; surjective = record
      { from             = P.→-to-⟶ from
      ; right-inverse-of = invʳ
      }
    }
  }

--------------------------------------------------------------------------------
open import Function.Equality

-- Invert a bijection

_⁻¹ : ∀ {f t} {A : Set f} {B : Set t} → A ⤖ B → B ⤖ A
β ⁻¹ = Inverse.bijection (I.sym (fromBijection β))
  where open Bijection β
        open import Function.Inverse as I

--------------------------------------------------------------------------------

open import Data.Fin
open import Data.Product

-- Bijection for heap addresses.  It restricts the domain and codomain
-- using the Fin type (Fin n contains addresses from 0 to n - 1).
-- This is useful to avoid partial bijections (for which the agda
-- library provides no support) and carrying extra assumptions about
-- domain and codomain.
Bij : ℕ → ℕ → Set
Bij n m = Fin n ⤖ Fin m

-- Identity bijection.
ι : ∀ {n} → Bij n n
ι = B.id

_↦_∈ᴮ_ : ∀ {n m} → Fin n → Fin m → Bij n m → Set
x ↦ y ∈ᴮ β = to ⟨$⟩ x ≡ y
  where open Bijection β
