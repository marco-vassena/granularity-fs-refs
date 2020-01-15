{-# OPTIONS --allow-unsolved-metas #-}

module Generic.Bijection where

open import Data.Empty
open import Data.Fin hiding (_≤?_ ; _≤_ ; _<_)
open import Data.Maybe as M
open import Data.Nat renaming (_+_ to _+ᴺ_)
open import Data.Nat.Properties hiding (suc-injective)
open import Data.Product
open import Generic.Partial.Bijection
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

--------------------------------------------------------------------------------

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

-- Extend a bijection with another
-- _▻_ : ∀ {n m} → Bij n m → Bij n m → Bij n m
-- β₁ ▻ β₂ = ?

-- Disjoint bijections.
-- β₁ # β₂ denotes that β₂ is disjoint from β₁, i.e., the
-- maps of β₁ and β₂ are respectively disjoint.
_#_ : ∀ {A B} → (β₁ β₂ : Bijectionᴾ A B) → Set
_#_ {A} β₁ β₂ = (B₁.to #ᴾ B₂.to) × (B₁.from #ᴾ B₂.from)
  where module B₁ = Bijectionᴾ β₁
        module B₂ = Bijectionᴾ β₂

-- Property that denotes that the composition of two bijections is a
-- bijection.
IsB-∘ : ∀ {A B} (β₁ β₂ : Bijectionᴾ A B) → Set
IsB-∘ β₁ β₂ = (B₁.from ∣′ B₂.from) InverseOfᴾ (B₁.to ∣′ B₂.to)
  where module B₁ = Bijectionᴾ β₁
        module B₂ = Bijectionᴾ β₂

-- If two bijections are disjoint, then their composition is a
-- bijection.
isB-∘ : ∀ {A B} (β₁ β₂ : Bijectionᴾ A B) → β₁ # β₂ → IsB-∘ β₁ β₂
isB-∘ {A} β₁ β₂ (to-# , from-#)
  = inverse-compose B₁.left-inverse-of B₂.left-inverse-of from-# to-#
  , inverse-compose B₁.right-inverse-of B₂.right-inverse-of to-# from-#
  where module B₁ = Bijectionᴾ β₁
        module B₂ = Bijectionᴾ β₂
        module B₁′ = Bijectionᴾ (β₁ ⁻¹)
        module B₂′ = Bijectionᴾ (β₂ ⁻¹)

-- Composition of disjoint bijections
_▻_ : ∀ {A B} → (β₁ β₂ : Bijectionᴾ A B) {{β₁#β₂ : β₁ # β₂}} → Bijectionᴾ A B
_▻_ {A} {B} β₁ β₂ {{ to-# , from-# }} =
  record { to   = B₁.to ∣′ B₂.to ;
           from = B₁.from ∣′ B₂.from ;
           inverse-of = isB-∘ β₁ β₂ (to-# , from-#) }
  where module B₁ = Bijectionᴾ β₁
        module B₂ = Bijectionᴾ β₂

open import Relation.Binary

module Ops {A B : Set}
  {{ _≟ᴬ_ : Decidable (_≡_ {A = A}) }}
  {{ _≟ᴮ_ : Decidable (_≡_ {A = B}) }} where

  -- These declarations just make agda aware of the decidable instances.
  instance _ = _≟ᴬ_
  instance _ = _≟ᴮ_

  -- When agda cannot figure out what instancies to use, we use qualified bindings.
  module A = Util {A} {B} {{_≟ᴬ_}}
  module B = Util {B} {A} {{_≟ᴮ_}}

  -- Lemma defined with explicit instances so that we can reuse it for module A and B.
  aux : ∀ {A B} {{_≟ᴬ_ : DecEq A}}  {{_≟ᴮ_ : DecEq B}} a b {a' b'} →
           let f = a -⟨ _≟ᴬ_ ⟩→ b
               g = b -⟨ _≟ᴮ_ ⟩→ a in (a' , b') ∈ f → (b' , a') ∈ g
  aux {{_≟ᴬ_}} {{_≟ᴮ_}} a b {a'} {b'} x with a ≟ᴬ a' | b ≟ᴮ b'
  aux {{_≟ᴬ_ = _≟ᴬ_}} {{_≟ᴮ_}} a b {.a} {.b} x | yes refl | yes refl = refl
  aux {{_≟ᴬ_ = _≟ᴬ_}} {{_≟ᴮ_}} a b {.a} {.b} refl | yes refl | no ¬p = ⊥-elim (¬p refl)
  aux {{_≟ᴬ_ = _≟ᴬ_}} {{_≟ᴮ_}} a b {a'} {b'} () | no ¬p | c

  isB↔ : ∀ (a : A) (b : B) → {!!} -- (a ↦ b) ↔ (b ↦ a)
  isB↔ a b = {!!} -- {a'} {b'} = ? -- aux a b , aux b a

  -- Singleton bijection
  ⟨_↔_⟩ : A → B → Bijectionᴾ A B
  ⟨ a ↔ b ⟩ = record { to = a ↦ b ; from = b ↦ a ; inverse-of = {!!} } -- isB↔

  -- Add a single pair to the right of a bijection
  _▻′_ : (β : Bijectionᴾ A B) (x : A × B) →
         let (a , b) = x in
           {{∉ᴬ : a ∉ᴰ Bijectionᴾ.to β}}
           {{∉ᴮ : b ∉ᴰ Bijectionᴾ.from β}} → Bijectionᴾ A B
  _▻′_ β (a , b) {{ ∉ᴬ }} {{ ∉ᴮ }} = {!!} -- β ∘ ⟨ b ↔ a ⟩
    where instance _ : β # ⟨ a ↔ b ⟩
                   _ = ∉-# (Bijectionᴾ.to β) ∉ᴬ , ∉-# (Bijectionᴾ.from β) ∉ᴮ

  -- Add a single pair to the left of a bijection
  _◅_ : (x : A × B) (β : Bijectionᴾ A B) →
         let (a , b) = x in
           {{∉ᴬ : a ∉ᴰ Bijectionᴾ.to β}}
           {{∉ᴮ : b ∉ᴰ Bijectionᴾ.from β}} → Bijectionᴾ A B
  _◅_ (a , b) β {{ ∉ᴬ }} {{ ∉ᴮ }} = {!!} -- ⟨ a ↔ b ⟩ ∘ β
    where instance _ : ⟨ a ↔ b ⟩ # β
                   _ = sym-# (∉-# (Bijectionᴾ.to β) ∉ᴬ) , sym-# (∉-# (Bijectionᴾ.from β) ∉ᴮ)

  -- open import Data.Sum
  -- split↔ : ∀ {β₁ β₂ : Bijectionᴾ A B} {{β₁#β₂ : β₁ # β₂}} {a b} → a ↔ b ∈ (β₁ ∘ β₂) → a ↔ b ∈ β₁ ⊎ a ↔ b ∈ β₂
  -- split↔ = {!!}
