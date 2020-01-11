{-# OPTIONS --allow-unsolved-metas #-}

module Generic.Bijection where

open import Function as F hiding (flip)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality as P
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
        open Inverse (fromBijection β)

--------------------------------------------------------------------------------

open import Data.Fin
open import Data.Product

Bij : ℕ → ℕ → Set
Bij n m = Fin n ⤖ Fin m

-- Address is in domain
-- _∈ᴰ_ : ℕ → Bij → Set
-- n ∈ᴰ β = ∃ (λ n' → (to ⟨$⟩ n) ≡ just n')
--   where open Bijection β

-- -- Address is in range
-- _∈ᴿ_ : ℕ → Bij → Set
-- n ∈ᴿ β = ∃ (λ n' → (to ⟨$⟩ n') ≡ just n)
--   where open Bijection β

ι : ∀ {n} → Bij n n
ι = B.id

-- Special case of identity, probably not needed.
∅ : Bij 0 0
∅ = bijection F.id F.id F.id (λ ())


-- ⊥-≤² : ∀ {n} → ¬ (suc (suc n) ≤ n)
-- ⊥-≤² {zero} ()
-- ⊥-≤² {suc n} (s≤s x) = ⊥-≤² x

-- -- Empty bijection
-- ∅ : Bij
-- ∅ = bijection (F.const nothing) (F.const 1) {!!} {!!}
--   where right-inverse : (x : Maybe ℕ) → F.const nothing (F.const 1 x) ≡ x
--         right-inverse (just x) = {!!}
--         right-inverse nothing = refl

-- -- Identity bijection for n addresses
-- ι : ℕ → Bij
-- ι n = bijection idⁿ id⁻¹ {!!} right-inv
--   where idⁿ : ℕ → Maybe ℕ
--         idⁿ m with suc m ≤? n  -- suc m because if n ≡ 0, the bijection should be empty
--         idⁿ m | yes p = just m
--         idⁿ m | no ¬p = nothing

--         id⁻¹ : Maybe ℕ → ℕ
--         id⁻¹ (just m) with suc m ≤? n
--         ... | yes p = m
--         ... | no ¬p = suc n
--         id⁻¹ nothing = suc n

--         right-inv : (x : Maybe ℕ) → idⁿ (id⁻¹ x) ≡ x
--         right-inv x with id⁻¹ x | inspect id⁻¹ x
--         right-inv (just x) | a | [ eq ] with suc a ≤? n | suc x ≤? n
--         right-inv (just x) | .x | [ refl ] | yes p | yes p₁ = refl
--         right-inv (just x) | .(suc _) | [ refl ] | yes p | no ¬p = ⊥-elim (⊥-≤² p)
--         right-inv (just x) | .x | [ refl ] | no ¬p | yes p = ⊥-elim (¬p p)
--         right-inv (just x) | .(suc _) | [ refl ] | no ¬p | no ¬p₁ = {!!}  -- don't understand what goes wrong here.
-- -- with suc a ≤? n | suc x ≤? n
-- --         right-inv (just x) | a | b | yes p | c = {!b!}
-- --         right-inv (just x) | a | b | no ¬p | c = {!!}
--         right-inv nothing | a | b with suc a ≤? n
--         right-inv nothing | .(suc _) | [ refl ] | yes p = ⊥-elim (⊥-≤² p)
--         right-inv nothing | a | b | no ¬p = refl

--  --        right-inv (just m) with suc m ≤? n
--  --        right-inv (just m) | yes p = {!!}
--  --        right-inv (just m) | no ¬p = {!!}
--  --  -- with suc m ≤? n
--  --  --       right-inv (just m) | yes p with suc m ≤? n
--  --  --       right-inv (just m) | yes p | yes p₁ = {!!} -- refl
--  --  --       right-inv (just m) | yes p | no ¬p = {!!} -- ⊥-elim (¬p p)
--  --  --       right-inv (just m) | no ¬p = {!!}
--  -- -- with suc (suc n) ≤? n | inspect idⁿ (suc n)
--  -- --        right-inv (just m) | no ¬p | yes p  | _ = ⊥-elim (⊥-≤² p)
--  -- --        right-inv (just m) | no ¬p | no ¬p₁ | [ eq ] = {!!}


--  --        right-inv nothing with suc (suc n) ≤? n
--  --        right-inv nothing | yes p = ⊥-elim (⊥-≤² p)
 --        right-inv nothing | no ¬p = refl
