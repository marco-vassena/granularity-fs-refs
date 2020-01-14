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

reduce∘inject-≡-id : ∀ {n} (x : Fin (suc n)) (x<n : toℕ x < n) → inject₁ (reduce¹ x x<n) ≡ x
reduce∘inject-≡-id zero (s≤s x<n) = refl
reduce∘inject-≡-id (suc x) (s≤s x<n) = cong suc (reduce∘inject-≡-id x x<n)

fin-< : ∀ {n} (x : Fin n) → toℕ x < n
fin-< zero = s≤s z≤n
fin-< (suc x) = s≤s (fin-< x)



-- _<?_ : ∀ (x y : ℕ) → Dec (x < y)
-- x <? y = suc x ≤? y

toℕ-inject₁-≡ : ∀ {n} (x : Fin n) → toℕ x ≡ toℕ (inject₁ x)
toℕ-inject₁-≡ zero = refl
toℕ-inject₁-≡ (suc x) = cong suc (toℕ-inject₁-≡ x)

equal-< : ∀ {n m} → (p q : n < m) → p ≡ q
equal-< (s≤s z≤n) (s≤s z≤n) = refl
equal-< (s≤s (s≤s p)) (s≤s (s≤s q)) = cong s≤s (equal-< (s≤s p) (s≤s q))



-- This weakening is used to match domain and codomain for composition.
_↑¹ : ∀ {n m} → Bij n m → Bij (suc n) (suc m)
_↑¹ {n} {m} β = record { to = to¹ ; from = from¹ ; inverse-of = inv' }
  where open Bijectionᴾ β

        to¹ : Fin (suc n) ⇀ Fin (suc m)
        to¹ x with (toℕ x) <? n
        to¹ x | yes p = M.map inject₁ (to (reduce¹ x p))
        to¹ x | no ¬p = nothing

        from¹ : Fin (suc m) ⇀ Fin (suc n)
        from¹ y with (toℕ y) <? m
        from¹ y | yes p = M.map inject₁ (from (reduce¹ y p))
        from¹ y | no ¬p = nothing

        from¹′ : (y : Fin (suc m)) → y ∈ᴰ from¹ → Fin (suc n)
        from¹′ y p with from¹ y
        from¹′ y (just px) | (just x) = x

        to¹′ : (y : Fin (suc n)) → y ∈ᴰ to¹ → Fin (suc m)
        to¹′ x p with to¹ x
        to¹′ x (just px) | (just y) = y


        -- lemma : ∀ (y : Fin (suc n)) (x : Fin m) (p₁ : toℕ y < n) →
        --         let y' = reduce¹ y p₁ in
        --           (to y') ≡ just x → (x , y') ∈ from
        -- lemma = {!!}

        foo : ∀ {x y} (x<n : toℕ x < n) (y<m : toℕ y < m) →  (x , y) ∈ to¹ → (reduce¹ x x<n , reduce¹ y y<m) ∈ to
        foo = {!!}

        -- bar' : ∀ {y x} → (y , x) ∈  from ⇔ (inject₁ y , inject₁ x) ∈ from¹
        -- bar' = {!!}

        -- open import Relation.Binary.HeterogeneousEquality hiding (inspect ; cong)

        -- egg : ∀ {x y} (y<m : toℕ y < m) (x<n : toℕ x < n) ->
        --         (reduce¹ x x<n , reduce¹ y y<m) ∈ to →
        --         (inject₁ (reduce¹ x x<n), y) ∈ to¹
        -- egg = {!!}

        -- aux' :  ∀ {A B : Set} {x} (f : A → B) y  → M.map f y ≡ just x → Σ (Is-just y) (λ p → f (to-witness p) ≡ x)
        -- aux' f (just x) refl = (just _) , refl
        -- aux' f nothing ()

        -- aux :  ∀ {A B : Set} {x} (f : A → B) y  → M.map f y ≡ just x → Σ (Is-just y) (λ p → f (to-witness p) ≡ x)
        -- aux f (just x) refl = (just _) , refl
        -- aux f nothing ()

        -- aux₁ : ∀ (y : Fin (suc m)) → toℕ y < m → y ∈ᴰ from¹
        -- aux₁ y y<m with (toℕ y) <? m
        -- aux₁ y y<m | yes p = {!!}
        -- aux₁ y y<m | no y≮m = ⊥-elim (y≮m y<m)

        -- aux₂ : ∀ (y : Fin (suc m)) (y∈f : y ∈ᴰ from¹) → from¹′ y y∈f  ∈ᴰ to¹
        -- aux₂ = {!!}

        aux₃ : ∀ {y x} → (y , x) ∈ from¹ → toℕ y < m
        aux₃ {y} yx∈f with toℕ y <? m
        aux₃ {y} yx∈f | yes p = p
        aux₃ {y} () | no ¬p

        aux : ∀ {n} (x : Fin (suc n)) (x' : Fin n) (x<n : toℕ x < n) → (inject₁ x') ≡ x → x' ≡ reduce¹ x x<n
        aux zero zero (s≤s x<n) eq = refl
        aux zero (suc x') x<n ()
        aux (suc x) zero (s≤s x<n) ()
        aux (suc x) (suc x') (s≤s x<n) eq = cong suc (aux x x' x<n (suc-injective eq))

        aux⁷ : ∀ x y → M.map inject₁ (from y) ≡ just x → (x<n : toℕ x < n) → (y , reduce¹ x x<n) ∈ from
        aux⁷ x y eq x<n with from y
        aux⁷ x y () x<n | nothing
        aux⁷ x y eq x<n | just x'
          let a = left-inverse-of eq' in
          begin
            just x' ≡⟨ cong just (aux x x' x<n (just-injective eq)) ⟩
            just (reduce¹ x x<n)
          ∎
          where open ≡-Reasoning

        -- (y , x') ∈ from
        aux₆ : ∀ x y → M.map inject₁ (from y) ≡ just x → ∃ (λ x' → inject₁ x' ≡  x)
        aux₆ x y eq with from y
        aux₆ x y eq | just x' = _ , just-injective eq
        aux₆ x y () | nothing

        aux₅ : ∀ y x → M.map inject₁ (from y) ≡ just x → toℕ x < n
        aux₅ y x yx∈f¹ with aux₆ x y yx∈f¹
        ... | (x' , eq) with fin-< x'
        ... | x<n' rewrite E.sym eq | toℕ-inject₁-≡ x' = x<n'

        aux₄ : ∀ {y x} → (y , x) ∈ from¹ → toℕ x < n
        aux₄ {y} {x} yx∈f with toℕ x <? n
        aux₄ {y} {x} yx∈f | yes x<n = x<n
        aux₄ {y} {x} yx∈f | no ¬p with toℕ y <? m
        aux₄ {y} {x} yx∈f | no ¬p | yes y<m = aux₅ (reduce¹ y y<m) x yx∈f
        aux₄ {y} {x} () | no ¬p | no ¬p₁

        def₁ : ∀ {x} (x<n : toℕ x < n) → to¹ x ≡ M.map inject₁ (to (reduce¹ x x<n))
        def₁ {x} x<n with toℕ x <? n
        def₁ {x} x<n | yes x<n' rewrite equal-< x<n x<n' = refl
        def₁ {x} x<n | no x≮n = ⊥-elim (x≮n x<n)

        def-from¹ : ∀ {y} (y<m : toℕ y < m) → from¹ y ≡ M.map inject₁ (from (reduce¹ y y<m))
        def-from¹ {y} y<m with toℕ y <? m
        def-from¹ {y} y<m | yes y<m' rewrite equal-< y<m y<m' = refl
        def-from¹ {y} y<m | no y≮m = ⊥-elim (y≮m y<m)


        bar : ∀ {y x} (y<m : toℕ y < m) (x<n : toℕ x < n) → (y , x) ∈ from¹ → (reduce¹ y y<m , reduce¹ x x<n ) ∈ from
        bar {y} {x} y<m x<n yx∈f¹ with toℕ y <? m
        bar {y} {x} y<m x<n yx∈f¹ | no y≮m = ⊥-elim (y≮m y<m)
        bar {y} {x} y<m x<n yx∈f¹ | yes y<m' rewrite sym (equal-< y<m y<m') =
-- rewrite sym (equal-< y<m y<m') with aux⁷ x (reduce¹ y y<m) yx∈f¹
--         ... | (x' , x≡x' , yx∈f') = {!!}
-- rewrite sym x≡x' | sym (reduce∘inject-≡-id (inject₁ x') x<n) = {!yx∈f'!}
--          let  (x' , x≡x' , yx∈f') = aux⁷ x (reduce¹ y y<m) yx∈f¹ in

          begin
            (from (reduce¹ y y<m)) ≡⟨ aux⁷ x (reduce¹ y y<m) yx∈f¹ x<n ⟩
            (just (reduce¹ x x<n))
          ∎
          where open ≡-Reasoning


        inv' : from¹ InverseOfᴾ to¹
        inv' {y} {x} = left , {!!}
          where open ≡-Reasoning
                left : (y , x) ∈ from¹ → (x , y) ∈ to¹
                left yx∈f =
                  let y<m = aux₃ yx∈f
                      x<n = aux₄ yx∈f
                      xy∈f = left-inverse-of (bar y<m x<n yx∈f) in
                  begin
                    to¹ x ≡⟨ def₁ x<n ⟩
                    M.map inject₁ (to (reduce¹ x x<n)) ≡⟨ cong (M.map inject₁) xy∈f ⟩
                    just (inject₁ (reduce¹ y y<m )) ≡⟨ cong just (reduce∘inject-≡-id y y<m) ⟩
                    just y
                  ∎


--         inv : from¹ InverseOfᴾ to¹
--         inv {y} {x} with (suc (toℕ x)) ≤? n | inspect ((suc (toℕ x)) ≤?_) n | (suc (toℕ y)) ≤? m |  inspect ((suc (toℕ y)) ≤?_) m
--         inv {y} {x} | yes x<n | [ eq₁ ] | yes y<m | [ eq₂ ] =
--           let f = proj₁ (bar y<m x<n)
--               f' = proj₂ (bar y<m x<n)
--               g = proj₁ (foo x<n y<m)
--               g' = proj₁ (foo x<n y<m)
--               x' = reduce¹ x x<n
--               y' = reduce¹ y y<m
--               eq₃ = left-inverse-of (f' (proj₁ bar' {!!} )) in
--               left , {!!}
--               -- (λ x₁ →         ) , {!le!}

--           where open ≡-Reasoning
--                 -- left : (inject₁ (reduce¹ y y<m) , x) ∈ from¹ → (inject₁ (reduce¹ x x<n) , y) ∈ to¹
--                 -- left eq = {!!}

--                 left : M.map inject₁ (from (reduce¹ y y<m)) ≡ just x → M.map inject₁ (to (reduce¹ x x<n)) ≡ just y
--                 left eq =
--                   let (p , eq') = aux inject₁ (from (reduce¹ y y<m)) eq
--                       y' = to-witness p
--                       y∈f = aux₁ y y<m
--                       y∈f' = ≡-∈ᴰ y {!!} {!!} {!eq!} in
--                   begin
--                     M.map inject₁ (to (reduce¹ x x<n)) ≡⟨ {! eq'!} ⟩
--                     {!to-witness p (to¹ (inject₁ (reduce¹ x x<n)))!} ≡⟨ {!!} ⟩
--                     just (to¹′ (from¹′ y {!!}) (aux₂ y y∈f)) ≡⟨ {!!} ⟩
--                     just (inject₁ (reduce¹ y y<m)) ≡⟨ cong just (reduce∘inject-≡-id y y<m) ⟩
--                     just y ∎
-- --      M.map inject₁ (to (reduce¹ x x<n)) ≡ just y

-- -- with left-inverse-of {reduce¹ y y<m} {reduce¹ x x<n} {!!} | right-inverse-of {{!!}} {reduce¹ y y<m} {!!}
-- --         ... | r | q = {!!}
--           -- where x' = reduce¹ x x<n
--           --     y' =  reduce¹ y y<m
--           --     in {!foo x<n y<m!}
--               -- {!!} , (λ x₁ → {!lemma ? ? ?!})
--         inv {y} {x} | yes p | [ eq₁ ] | no ¬p | [ eq₂ ] = (λ ()) , {!!}
--         inv {y} {x} | no ¬p | [ eq₁ ] | yes p | [ eq₂ ] = {!!} , (λ ())
--         inv {y} {x} | no ¬p | [ eq₁ ] | no ¬p₁ | [ eq₂ ] = (λ ()) , (λ ())

-- nothing for Fin (suc n). otherwise call to and then inject₁
-- Use reduce≥ to decide if it is Fin (suc n) or not.

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
