{-# OPTIONS --allow-unsolved-metas #-}

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

-- TODO: rename ι′ n
ι⟨_⟩ : ∀ n → Bij n n
ι⟨ n ⟩ = B.id


_↦_∈ᴮ_ : ∀ {n m} → Fin n → Fin m → Bij n m → Set
x ↦ y ∈ᴮ β = to ⟨$⟩ x ≡ y
  where open Bijection β

_≟ᶠ_ : ∀ {n} → (x y : Fin n) → Dec (x ≡ y)
zero ≟ᶠ zero = yes refl
zero ≟ᶠ suc y = no (λ ())
suc x ≟ᶠ zero = no (λ ())
suc x ≟ᶠ suc y with x  ≟ᶠ y
suc x ≟ᶠ suc .x | yes refl = yes refl
suc x ≟ᶠ suc y | no ¬p = no λ { refl → ¬p refl }

-- Singleton bijection
-- _↔_ : ∀ (n m : ℕ) → Bij (suc n) (suc m)
-- n ↔ m  = bijection to {!!} {!!} {!!}
--   where to : Fin (suc n) → Fin (suc m)
--         to x with x ≟ᶠ (fromℕ n)
--         to .(fromℕ _) | yes refl = fromℕ m
--         to x | no ¬p = {!!} -- what should I return here?
-- I guess I should just use composition, but there will be secret entries
-- that have no counterpart and that are just "not defined"

-- wken the codomain (modeling adding a secret entry to the
-- bijection).  It doens't work because in the invert function I need
-- to map back one extra value. With an (explicitly) partial function
-- I could restrict the inverse to consider only the parts where it is
-- defined.
_↑¹ : ∀ {n m} → Bij n m → Bij n (suc m)
β ↑¹ = bijection (λ x → inject₁ (to ⟨$⟩ x)) (λ y → from ⟨$⟩ {!!}) {!!} {!!}
  where open Bijection β
