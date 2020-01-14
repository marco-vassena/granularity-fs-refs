{-# OPTIONS --allow-unsolved-metas #-}

module Generic.Bijection where

import Function as F
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality as E
import Level as L
open import Category.Monad

-- open import Function.Bijection renaming (_∘_ to _∘ᴮ_) public   -- rexport composition
-- open import Function.Bijection as B
open import Data.Empty
open import Data.Nat renaming (_+_ to _+ᴺ_)
open import Data.Nat.Properties hiding (suc-injective)
open import Lattice

open import Data.Maybe as M
-- open import Generic.Injection as I hiding (id ; _∘_)
-- open import Generic.Surjection as S hiding (id ; _∘_)
open import Generic.PMap as P renaming (∅ to ∅ᴾ) -- using (_⇀_)

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

_RightInverseOfᴾ_ : ∀ {A B} → A ⇀ B → B ⇀ A → Set
_RightInverseOfᴾ_ f g = g LeftInverseOfᴾ f

_InverseOfᴾ_ : ∀ {A B} → A ⇀ B → B ⇀ A → Set
_InverseOfᴾ_ f g = ∀ {x y} → (x , y) ∈ f ⇔ (y , x) ∈ g

-- Partial bijection
record Bijectionᴾ (A B : Set) : Set where
  field to : A ⇀ B
        from : B ⇀ A
        inverse-of : from InverseOfᴾ to

  left-inverse-of : from LeftInverseOfᴾ to
  left-inverse-of = proj₁ inverse-of

  right-inverse-of : from RightInverseOfᴾ to
  right-inverse-of = proj₂ inverse-of

  from′ : (b : B) → b ∈ᴰ from → A
  from′ b x with from b
  from′ b (just px) | (just x) = x

infix 3 _⤖ᴾ_

_⤖ᴾ_ : Set → Set → Set
From ⤖ᴾ To = Bijectionᴾ From To

bijᴾ : ∀ {A B} (to : A ⇀ B) (from : B ⇀ A) → from InverseOfᴾ to →
         A ⤖ᴾ B
bijᴾ to from inv = record { to = to ; from = from ; inverse-of = inv }

-- Empty partial bijection
∅ : ∀ {A B} → A ⤖ᴾ B
∅ = bijᴾ ∅ᴾ ∅ᴾ ((λ ()) , (λ ()))

-- Identity partial bijection
id : ∀ {A} → A ⤖ᴾ A
id = bijᴾ just just ((λ { refl → refl }) , (λ { refl → refl }))

_∈ᵗ_ : ∀ {A B} → A × B → A ⤖ᴾ B → Set
x ∈ᵗ β = x ∈ to
  where open Bijectionᴾ β

-- TODO: would it be more readable to have A × B and then swap the pair in the def?
_∈ᶠ_ : ∀ {A B} → B × A → A ⤖ᴾ B → Set
x ∈ᶠ β = x ∈ from
  where open Bijectionᴾ β

-- Composition
_∘_ : ∀ {A B C} → B ⤖ᴾ C → A ⤖ᴾ B → A ⤖ᴾ C
_∘_ {A} {B} {C} f g =
  record { to = to g >=> to f
         ; from = from f >=> from g
         ; inverse-of = inv
         }
  where open Bijectionᴾ
        open RawMonad {L.zero} monad

        -- Not the prettiest proof, but still a proof :-)
        inv : (from f >=> from g) InverseOfᴾ (to g >=> to f)
        inv {c} {a} with to g a | inspect (to g) a | from f c | inspect (from f) c
        inv {c} {a} | just b₁ | [ ab∈g₁ ] | just b₂ | [ cb∈f₂ ] = left , right
          where left : (b₂ , a) ∈ (from g) → (b₁ , c) ∈ (to f)
                left ba∈g₂ =
                  let bc∈f₂ = left-inverse-of f cb∈f₂
                      ab∈g₂ = left-inverse-of g ba∈g₂ in
                      trans (cong (to f) (just-injective (trans (sym ab∈g₁) ab∈g₂))) bc∈f₂

                right : (b₁ , c) ∈ᵗ f → (b₂ , a) ∈ᶠ g
                right bc∈f =
                  let cb∈f = right-inverse-of f bc∈f
                      ab∈g = right-inverse-of g ab∈g₁ in
                      trans (cong (from g) (just-injective (trans (sym cb∈f₂) cb∈f))) ab∈g


        inv {c} {a} | just b | [ eq ] | nothing | [ eq' ] = (λ ()) ,  ⊥-elim F.∘ ⊥-right-inverse
          where ⊥-right-inverse : (b , c) ∈ (to f) → ⊥
                ⊥-right-inverse bc∈f =
                  let cb∈f = right-inverse-of f bc∈f
                      c∉f = ≡-∉ c (from f) eq' in
                        ⊥-elim (∈-or-∉ {p = from f} cb∈f c∉f)

        inv {c} {a} | nothing | [ eq ] | just b | [ eq' ] = ⊥-elim F.∘ ⊥-left-inverse , (λ ())
          where ⊥-left-inverse : (b , a) ∈ from g → ⊥
                ⊥-left-inverse ba∈g =
                  let ab∈g = left-inverse-of g ba∈g
                      a∉g = ≡-∉ a (to g) eq in
                      ⊥-elim (∈-or-∉ {p = to g} ab∈g a∉g)

        inv {x} {y} | nothing | [ eq ] | nothing | [ eq' ] = (λ ()) , (λ ())

-- Invert a bijection
_⁻¹ : ∀ {A : Set} {B : Set} → A ⤖ᴾ B → B ⤖ᴾ A
β ⁻¹ = record { to = from ; from = to ; inverse-of = right-inverse-of , left-inverse-of }
  where open Bijectionᴾ β



--------------------------------------------------------------------------------

open import Data.Fin hiding (_≤?_ ; _≤_ ; _<_)
open import Data.Product

suc-injective : ∀ {n} {x y : Fin n} → _≡_ {A = Fin (suc n)} (suc x) (suc y) → x ≡ y
suc-injective refl = refl

-- Bijection for heap addresses.  It restricts the domain and codomain
-- using the Fin type (Fin n contains addresses from 0 to n - 1).
-- This is useful to avoid partial bijections (for which the agda
-- library provides no support) and carrying extra assumptions about
-- domain and codomain.
Bij : ℕ → ℕ → Set
Bij n m = Fin n ⤖ᴾ Fin m

-- Identity bijection.
ι : ∀ {n} → Bij n n
ι = id

-- Explicit size
ι′ : ∀ n → Bij n n
ι′ _ = ι

-- TODO: do we need to lif the other memberships type?

instance
  _≟ᶠ_ : ∀ {n} → (x y : Fin n) → Dec (x ≡ y)
  zero ≟ᶠ zero = yes refl
  zero ≟ᶠ suc y = no (λ ())
  suc x ≟ᶠ zero = no (λ ())
  suc x ≟ᶠ suc y with x  ≟ᶠ y
  suc x ≟ᶠ suc .x | yes refl = yes refl
  suc x ≟ᶠ suc y | no ¬p = no λ { refl → ¬p refl }

-- Singleton bijection
_↔_ : ∀ {n m} (x : Fin n) (y : Fin m) → Bij n m
_↔_ {n} {m} x y  = bijᴾ (x ↦ y) (y ↦ x) inv
  where

  inv : (y ↦ x) InverseOfᴾ (x ↦ y)
  inv {y'} {x'} with x ≟ᶠ x' | inspect (x ≟ᶠ_) x'
  inv {y'} {_} | yes p | [ eq ] with y ≟ᶠ y' | inspect (y ≟ᶠ_) y'
  inv {_} {_} | yes refl | [ eq ] | yes refl | [ eq' ] = (λ _ → refl) , (λ _ → refl)
  inv {y'} {x'} | yes refl | [ eq ] | no y≠y' | [ eq' ] = (λ ()) , (λ jy≡jy' → ⊥-elim (y≠y' (just-injective jy≡jy')))
  inv {y'} {x} | no ¬p | [ eq ] with y ≟ᶠ y' | inspect (y ≟ᶠ_) y'
  inv {_} {y} | no x≠x' | [ eq ] | yes refl | [ eq' ] = (λ jx≡jy' → ⊥-elim (x≠x' (just-injective jx≡jy'))) , (λ ())
  inv {x} {y} | no ¬p | [ eq ] | no ¬p₁ | [ eq' ] = (λ ()) , (λ ())

reduce¹ : ∀ {n} (x : Fin (suc n)) → toℕ x < n → Fin n
reduce¹ zero (s≤s x<n) = zero
reduce¹ (suc x) (s≤s x<n) = suc (reduce¹ x x<n)

inj∘red-≡-id : ∀ {n} (x : Fin (suc n)) (x<n : toℕ x < n) → inject₁ (reduce¹ x x<n) ≡ x
inj∘red-≡-id zero (s≤s x<n) = refl
inj∘red-≡-id (suc x) (s≤s x<n) = cong suc (inj∘red-≡-id x x<n)

toℕ-inject₁-≡ : ∀ {n} (x : Fin n) → toℕ x ≡ toℕ (inject₁ x)
toℕ-inject₁-≡ zero = refl
toℕ-inject₁-≡ (suc x) = cong suc (toℕ-inject₁-≡ x)

red∘inj-≡-id : ∀ {n} (x : Fin n) (x<n : toℕ (inject₁ x) < n) → reduce¹ (inject₁ x) x<n ≡ x
red∘inj-≡-id zero (s≤s z≤n) = refl
red∘inj-≡-id (suc x) (s≤s x<n) = cong suc (red∘inj-≡-id x x<n)

fin-< : ∀ {n} (x : Fin n) → toℕ x < n
fin-< zero = s≤s z≤n
fin-< (suc x) = s≤s (fin-< x)

equal-< : ∀ {n m} → (p q : n < m) → p ≡ q
equal-< (s≤s z≤n) (s≤s z≤n) = refl
equal-< (s≤s (s≤s p)) (s≤s (s≤s q)) = cong s≤s (equal-< (s≤s p) (s≤s q))



-- This weakening is used to match domain and codomain for composition.
_↑¹ : ∀ {n m} → Bij n m → Bij (suc n) (suc m)
_↑¹ {n} {m} β = record { to = to¹ ; from = from¹ ; inverse-of = inv }
  where open Bijectionᴾ β

        to¹ : Fin (suc n) ⇀ Fin (suc m)
        to¹ x with (toℕ x) <? n
        to¹ x | yes p = M.map inject₁ (to (reduce¹ x p))
        to¹ x | no ¬p = nothing

        from¹ : Fin (suc m) ⇀ Fin (suc n)
        from¹ y with (toℕ y) <? m
        from¹ y | yes p = M.map inject₁ (from (reduce¹ y p))
        from¹ y | no ¬p = nothing

        -- Fact about the domain (D) of from
        from-<ᴰ : ∀ {y x} → (y , x) ∈ from¹ → toℕ y < m
        from-<ᴰ {y} yx∈f with toℕ y <? m
        from-<ᴰ {y} yx∈f | yes p = p
        from-<ᴰ {y} () | no ¬p

        -- Fact about the range (R) of from
        from-<ᴿ : ∀ {y x} → (y , x) ∈ from¹ → toℕ x < n
        from-<ᴿ {y} {x} yx∈f with toℕ y <? m
        from-<ᴿ {y} {x} yx∈f | yes y<m with from (reduce¹ y y<m)
        from-<ᴿ {y} {x} yx∈f | _ | just x' with fin-< x'
        ... | x<n rewrite sym (just-injective yx∈f) | toℕ-inject₁-≡ x' = x<n
        from-<ᴿ {y} {x} () | _ | nothing
        from-<ᴿ {y} {x} () | no ¬p

        -- Fact about the domain (D) of to
        to-<ᴰ : ∀ {x y} → (x , y) ∈ to¹ → toℕ x < n
        to-<ᴰ {x} xy∈t with toℕ x <? n
        to-<ᴰ {x} xy∈t | yes p = p
        to-<ᴰ {x} () | no ¬p

        -- Fact about the range (R) of to
        to-<ᴿ : ∀ {x y} → (x , y) ∈ to¹ → toℕ y < m
        to-<ᴿ {x} {y} xy∈t with toℕ x <? n
        to-<ᴿ {x} {y} xy∈t | yes x<n with to (reduce¹ x x<n)
        to-<ᴿ {x} {y} xy∈t | _ | just y' with fin-< y'
        ... | y<m rewrite sym (just-injective xy∈t) | toℕ-inject₁-≡ y' = y<m
        to-<ᴿ {x} {y} () | _ | nothing
        to-<ᴿ {x} {y} () | no ¬p

        -- Definition of to¹ after the bounds test.
        def-to¹ : ∀ {x} (x<n : toℕ x < n) → to¹ x ≡ M.map inject₁ (to (reduce¹ x x<n))
        def-to¹ {x} x<n with toℕ x <? n
        def-to¹ {x} x<n | yes x<n' rewrite equal-< x<n x<n' = refl
        def-to¹ {x} x<n | no x≮n = ⊥-elim (x≮n x<n)

        -- Definition of from¹ after the bounds test.
        def-from¹ : ∀ {y} (y<m : toℕ y < m) → from¹ y ≡ M.map inject₁ (from (reduce¹ y y<m))
        def-from¹ {y} y<m with toℕ y <? m
        def-from¹ {y} y<m | yes y<m' rewrite equal-< y<m y<m' = refl
        def-from¹ {y} y<m | no y≮m = ⊥-elim (y≮m y<m)

        -- If (y , x) are within the range before the extension, then they are defined in the original bijection (direction "from")
        ∈¹-∈-from : ∀ {y x} (y<m : toℕ y < m) (x<n : toℕ x < n) → (y , x) ∈ from¹ → (reduce¹ y y<m , reduce¹ x x<n ) ∈ from
        ∈¹-∈-from {y} {x} y<m x<n yx∈f¹ with toℕ y <? m
        ∈¹-∈-from {y} {x} y<m x<n yx∈f¹ | no y≮m = ⊥-elim (y≮m y<m)
        ∈¹-∈-from {y} {x} y<m x<n yx∈f¹ | yes y<m' rewrite sym (equal-< y<m y<m') with from (reduce¹ y y<m)
        ∈¹-∈-from {y} {x} y<m x<n ()    | _ | nothing
        ∈¹-∈-from {y} {x} y<m x<n yx∈f¹ | _ | just x'
          rewrite sym (just-injective yx∈f¹) | toℕ-inject₁-≡ x' | red∘inj-≡-id x' x<n = refl

        -- If (x , y) are within the range before the extension, then they are defined in the original bijection (direction "to").
        ∈¹-∈-to : ∀ {x y} (x<n : toℕ x < n) (y<m : toℕ y < m) → (x , y) ∈ to¹ → (reduce¹ x x<n , reduce¹ y y<m) ∈ to
        ∈¹-∈-to {x} {y} x<n y<m xy∈t¹ with toℕ x <? n
        ∈¹-∈-to {x} {y} x<n y<m xy∈t¹ | no x≮n = ⊥-elim (x≮n x<n)
        ∈¹-∈-to {x} {y} x<n y<m xy∈t¹ | yes x<n' rewrite sym (equal-< x<n x<n') with to (reduce¹ x x<n)
        ∈¹-∈-to {x} {y} x<n y<m ()    | _ | nothing
        ∈¹-∈-to {x} {y} x<n y<m xy∈t¹ | _ | just y'
          rewrite sym (just-injective xy∈t¹) | toℕ-inject₁-≡ y' | red∘inj-≡-id y' y<m = refl


        inv : from¹ InverseOfᴾ to¹
        inv {y} {x} = left , right
          where open ≡-Reasoning
                left : (y , x) ∈ from¹ → (x , y) ∈ to¹
                left yx∈f =
                  let y<m = from-<ᴰ yx∈f
                      x<n = from-<ᴿ yx∈f
                      xy∈f = left-inverse-of (∈¹-∈-from y<m x<n yx∈f) in
                  begin
                    to¹ x ≡⟨ def-to¹ x<n ⟩
                    M.map inject₁ (to (reduce¹ x x<n)) ≡⟨ cong (M.map inject₁) xy∈f ⟩
                    just (inject₁ (reduce¹ y y<m )) ≡⟨ cong just (inj∘red-≡-id y y<m) ⟩
                    just y
                  ∎

                right : (x , y) ∈ to¹ → (y , x) ∈ from¹
                right xy∈t =
                  let x<n = to-<ᴰ xy∈t
                      y<m = to-<ᴿ xy∈t
                      xy∈f = right-inverse-of (∈¹-∈-to x<n y<m xy∈t) in
                  begin
                    from¹ y ≡⟨ def-from¹ y<m ⟩
                    M.map inject₁ (from (reduce¹ y y<m)) ≡⟨ cong (M.map inject₁) xy∈f ⟩
                    just (inject₁ (reduce¹ x x<n )) ≡⟨ cong just (inj∘red-≡-id x x<n) ⟩
                    just x
                  ∎

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
