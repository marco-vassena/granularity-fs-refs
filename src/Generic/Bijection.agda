{-# OPTIONS --allow-unsolved-metas #-}

module Generic.Bijection where

import Function as F
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
import Level as L
open import Category.Monad

-- open import Function.Bijection renaming (_∘_ to _∘ᴮ_) public   -- rexport composition
-- open import Function.Bijection as B
open import Data.Empty
open import Data.Nat
open import Data.Maybe
-- open import Generic.Injection as I hiding (id ; _∘_)
-- open import Generic.Surjection as S hiding (id ; _∘_)
open import Generic.PMap as P hiding (∅ ) -- using (_⇀_)

-- -- A partial bijection with restricted injectivity and surjectivity
-- -- properties only where the codomain is defined.
-- record Bijectiveᴾ {A B : Set} (to : A ⇀ B) : Set where
--   field injectiveᴾ : Injectiveᴾ to
--         surjectiveᴾ : Surjectiveᴾ to

-- -- The set of partial bijections.
-- record Bijectionᴾ (A B : Set) : Set where
--   field to : A ⇀ B
--         bijectiveᴾ : Bijectiveᴾ to

--   open Bijectiveᴾ bijectiveᴾ public

--   injectionᴾ : Injectionᴾ A B
--   injectionᴾ = record { to = to ; injectiveᴾ = injectiveᴾ }

--   surjectionᴾ : Surjectionᴾ A B
--   surjectionᴾ = record { to = to ; surjectiveᴾ = surjectiveᴾ }

--   open Surjectionᴾ surjectionᴾ public using ( right-inverse )

--   left-inverse : LeftInverse From To
--   left-inverse = record
--     { to              = to
--     ; from            = from
--     ; left-inverse-of = left-inverse-of
--     }

--   open LeftInverse left-inverse public using (to-from)




-- bijectionᴾ : {A B : Set} (to : A ⇀ B) (from : B ⇀ A) →
--              Injectiveᴾ to → from RightInverseOfᴾ to →
--              Bijectionᴾ A B
-- bijectionᴾ to from inj inv
--   = record { to = to
--            ; bijectiveᴾ = record
--              { injectiveᴾ = inj
--              ; surjectiveᴾ = record
--                { from = from
--                ; right-inverse-of = inv
--                }
--              }
--            }

open import Data.Product

_LeftInverseOfᴾ_ : ∀ {A B} → A ⇀ B → B ⇀ A → Set
_LeftInverseOfᴾ_ f g = ∀ {x y} → (x , y) ∈ f → (y , x) ∈ g

-- Partial bijection
record Bij (A B : Set) : Set where
  field to : A ⇀ B
        from : B ⇀ A
        left-inverse-of : from LeftInverseOfᴾ to

--        inverse-∉ :

infix 3 _⤖ᴾ_

_⤖ᴾ_ : Set → Set → Set
From ⤖ᴾ To = Bij From To

bijᴾ : ∀ {A B} (to : A ⇀ B) (from : B ⇀ A) → from LeftInverseOfᴾ to →
         A ⤖ᴾ B
bijᴾ to from p = record { to = to ; from = from ; left-inverse-of = p }

-- Empty partial bijection
∅ : ∀ {A B} → A ⤖ᴾ B
∅ = bijᴾ (F.const nothing) (F.const nothing) (λ {x} {y} → λ ())

-- Identity partial bijection
id : ∀ {A} → A ⤖ᴾ A
id = bijᴾ just just (λ { refl → refl })


-- Composition
_∘_ : ∀ {A B C} → B ⤖ᴾ C → A ⤖ᴾ B → A ⤖ᴾ C
_∘_ {A} {B} {C} f g = record { to = to g >=> to f ; from = from f >=> from g ; left-inverse-of = inv }
  where open Bij
        open RawMonad {L.zero} monad

        -- Not the prettiest proof, but still a proof :-)
        inv : (from f >=> from g) LeftInverseOfᴾ (to g >=> to f)
        inv {c} {a} x
          with   to g a | inspect (to g) a
               | from f c | inspect (from f) c
        inv {c} {a} x | just b₁ | [ ab∈g₁ ] | just b₂ | [ eq' ] =
          let bc∈f₂ = left-inverse-of f eq'
              ab∈g₂ = left-inverse-of g x in
              trans (cong (to f) (just-injective (trans (sym ab∈g₁) ab∈g₂))) bc∈f₂
        inv {x} {y} () | just x₁ | [ eq ] | nothing | [ eq' ]
        inv {c} {a} x | nothing | [ eq ] | just b | [ eq' ] =
          let ab∈g = left-inverse-of g x
              a∉g = ≡-∉ a (to g) eq in
              ⊥-elim (just-or-nothing {B} {A} (to g a) (∈-just a b (to g) ab∈g) a∉g)
        inv {x} {y} () | nothing | [ eq ] | nothing | [ eq' ]

-- --------------------------------------------------------------------------------
-- -- open import Function.Equality

-- It doesn't seem we can prove this with what we have.
foo : ∀ {A B : Set} {f : A ⇀ B} {g : B ⇀ A} → f LeftInverseOfᴾ g → g LeftInverseOfᴾ f
foo {f = f} {g} p {b} {a} ba∈g with f a | inspect f a
foo {f = f} {g} p {b} {a} ba∈g | just b' | [ ab∈f' ] =
  let ba∈g' = p ab∈f' in {!!}
--    trans (sym ab∈f') {!!}
foo {f = f} {g} p {b} {a} ba∈g | nothing | [ eq ] = {!p !}

-- Invert a bijection
-- Inverse.bijection (I.sym (fromBijection β))
_⁻¹ : ∀ {A : Set} {B : Set} → A ⤖ᴾ B → B ⤖ᴾ A
β ⁻¹ = record { to = from ; from = to ; left-inverse-of = foo left-inverse-of }
  where open Bij β
--        open import Function.Inverse as I



-- --------------------------------------------------------------------------------

-- open import Data.Fin
-- open import Data.Product

-- -- Bijection for heap addresses.  It restricts the domain and codomain
-- -- using the Fin type (Fin n contains addresses from 0 to n - 1).
-- -- This is useful to avoid partial bijections (for which the agda
-- -- library provides no support) and carrying extra assumptions about
-- -- domain and codomain.
-- Bij : ℕ → ℕ → Set
-- Bij n m = Fin n ⤖ᴾ Fin m

-- -- Identity bijection.
-- ι : ∀ {n} → Bij n n
-- ι = {!!}
-- -- B.id

-- -- TODO: rename ι′ n
-- ι⟨_⟩ : ∀ n → Bij n n
-- ι⟨ n ⟩ = {!!}
-- -- B.id


-- _↦_∈ᴮ_ : ∀ {n m} → Fin n → Fin m → Bij n m → Set
-- x ↦ y ∈ᴮ β = {!!}
-- -- to ⟨$⟩ x ≡ y
-- --   where open Bijection β

-- instance
--   _≟ᶠ_ : ∀ {n} → (x y : Fin n) → Dec (x ≡ y)
--   zero ≟ᶠ zero = yes refl
--   zero ≟ᶠ suc y = no (λ ())
--   suc x ≟ᶠ zero = no (λ ())
--   suc x ≟ᶠ suc y with x  ≟ᶠ y
--   suc x ≟ᶠ suc .x | yes refl = yes refl
--   suc x ≟ᶠ suc y | no ¬p = no λ { refl → ¬p refl }

-- -- Singleton bijection
-- _↔_ : ∀ {n m} (x : Fin n) (y : Fin m) → Bij n m
-- _↔_ {n} {m} x y  = bijectionᴾ (x ↦ y) (y ↦ x) inj inv
--   where
--         inj : Injectiveᴾ (x ↦ y)
--         inj {x'} {y'} p q eq = trans (back↦ x' x y p) (sym (back↦ y' x y q))

--         inv : (y ↦ x) RightInverseOfᴾ (x ↦ y)
--         inv y' p with to-witness p | inspect to-witness p
--         ... | r | [ eq ] with x ≟ᶠ r | y ≟ᶠ y'
--         inv _ p | _ | [ eq ] | yes refl | yes refl = refl
--         inv y' () | _ | [ eq ] | yes refl | no ¬p
--         inv _ (just px) | r | [ eq ] | no ¬p | yes refl = ⊥-elim (¬p eq)
--         inv y' () | r | [ eq ] | no ¬p | no ¬p₁

-- -- This weakening is used to match domain and codomain for composition.
-- _↑¹ : ∀ {n m} → Bij n m → Bij (suc n) (suc m)
-- β ↑¹ = {!!} -- bijection (λ x → inject₁ (to ⟨$⟩ x)) (λ y → from ⟨$⟩ {!!}) {!!} {!!}
--   -- where open Bijection β

-- -- The domain and the codomain should have the same size! n ≡ m
-- -- add one entry to a bijection
-- _▻_ : ∀ {n m} → Bij n m → (Fin (suc n)) × (Fin (suc m)) → Bij (suc n) (suc m)
-- _▻_ {n} {m} β (x , y) = record { to = B₁.to ∣′ B₂.to ; bijectiveᴾ = bij }
--   where module B₁ = Bijectionᴾ (β ↑¹)
--         module B₂ = Bijectionᴾ (x ↔ y)

--         inj : Injectiveᴾ (B₁.to ∣′ B₂.to)
--         inj = {!!}

--         sur : Surjectiveᴾ (B₁.to ∣′ B₂.to)
--         sur = record { from = {!B₁.from ∣′ B₂.from!} ; right-inverse-of = {!!} }

--         bij : Bijectiveᴾ (B₁.to ∣′ B₂.to)
--         bij = record { injectiveᴾ = inj ; surjectiveᴾ = sur }


-- -- Composition does not give me the type that i expect. Why?
-- -- should I write this as a primitive op?

--  -- {!β₁!} ∘ᴮ β'
--  --  where β₁ β' : Bij (suc n) (suc m)
--  --        β' = β ↑¹

--  --        β₁ = bijection {!!} {!!} {!!} {!!}

--         -- to₁ :
-- -- record { to = {!to ⟨$⟩ !} ; bijective = {!!} }
-- --   where open Bijection β
