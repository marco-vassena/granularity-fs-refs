-- {-# OPTIONS --allow-unsolved-metas #-}

module Generic.Partial.Bijection where

import Function as F
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
import Level as L
open import Category.Monad
open import Data.Empty
open import Data.Maybe as M
open import Data.Product
open import Generic.Partial.Function renaming (
  ∅ to ∅ᴾ ; _#_ to _#ᴾ_ ; _∣′_ to _∣ᴾ_) hiding (
  _∈ᴰ_ ) public

-- Partial bijection
record Bijectionᴾ (A B : Set) : Set where
  field to : A ⇀ B
        from : B ⇀ A
        inverse-of : from InverseOfᴾ to

  left-inverse-of : from LeftInverseOfᴾ to
  left-inverse-of = proj₁ inverse-of

  right-inverse-of : from RightInverseOfᴾ to
  right-inverse-of = proj₂ inverse-of

  -- TODO: remove
  -- from′ : (b : B) → b ∈ᴰ from → A
  -- from′ b x with from b
  -- from′ b (just px) | (just x) = x

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

--------------------------------------------------------------------------------
-- TODO: So many variants ... need to clean up

_∈ᵗ_ : ∀ {A B} → A × B → A ⤖ᴾ B → Set
x ∈ᵗ β = x ∈ to
  where open Bijectionᴾ β

-- TODO: would it be more readable to have A × B and then swap the pair in the def?
_∈ᶠ_ : ∀ {A B} → A × B → A ⤖ᴾ B → Set
(a , b) ∈ᶠ β = (b , a) ∈ from
  where open Bijectionᴾ β

∈ᶠ-∈ᵗ : ∀ {A B} {x : A × B} {β : A ⤖ᴾ B} → x ∈ᶠ β → x ∈ᵗ β
∈ᶠ-∈ᵗ {β = β} x = left-inverse-of x
  where open Bijectionᴾ β

-- Don't think we have use ∈ᶠ maybe we can export ᵗ as just ∈ᴮ
_∈ᴮ_ : ∀ {A B} → A × B → A ⤖ᴾ B → Set
x ∈ᴮ β = (x ∈ᵗ β) × (x ∈ᶠ β)

_∈ᴰ_ : ∀ {A B} → A → A ⤖ᴾ B → Set
a ∈ᴰ β = ∃ (λ b → (a , b) ∈ᵗ β)

-- Not the best definition, ∈ᴿ′ seems better (more symmetric)
_∈ᴿ_ : ∀ {A B} → B → A ⤖ᴾ B → Set
b ∈ᴿ β = ∃ (λ a → (a , b) ∈ᵗ β)

_∈ᴿ′_ : ∀ {A B} → B → A ⤖ᴾ B → Set
b ∈ᴿ′ β = ∃ (λ a → (a , b) ∈ᶠ β)


-- TODO : remove
∈-∈ᴰ : ∀ {A B} {x : A × B} {β : A ⤖ᴾ B} → x ∈ᵗ β → (proj₁ x) ∈ᴰ β
∈-∈ᴰ p = _ , p

-- ∈-∈ᴿ : ∀ {A B} {x : A × B} {β : A ⤖ᴾ B} → x ∈ᵗ β → (proj₂ x) ∈ᴿ β
-- ∈-∈ᴿ p = _ , p

--------------------------------------------------------------------------------
-- Bijection extension

_Extends_ : ∀ {A B} (β₁ β₂ : A ⤖ᴾ B) → Set
β₂ Extends β₁ = ∀ {x} → x ∈ᵗ β₁ → x ∈ᵗ β₂

-- β₁ ⊆ β₂ iff β₂ is an extension of β₁
-- Defined as a record to ease inference of the bijections
record _⊆_ {A B} (β₁ β₂ : A ⤖ᴾ B) : Set where
  field bij-⊆ : β₂ Extends β₁

open _⊆_ public

infixr 3 _⊆_

refl-⊆ : ∀ {A B} {β : A ⤖ᴾ B} → β ⊆ β
refl-⊆ {β = β} = record { bij-⊆ = λ {x} z → z }

trans-⊆ : ∀ {A B} {β₁ β₂ β₃ : A ⤖ᴾ B} → β₁ ⊆ β₂ → β₂ ⊆ β₃ → β₁ ⊆ β₃
trans-⊆ ⊆₁ ⊆₂ = record { bij-⊆ = λ ∈₁ → M₂.bij-⊆ (M₁.bij-⊆ ∈₁) }
  where module M₁ = _⊆_ ⊆₁
        module M₂ = _⊆_ ⊆₂

--------------------------------------------------------------------------------

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
        -- TODO: improve proof
        inv : (from f >=> from g) InverseOfᴾ (to g >=> to f)
        inv {c} {a} with to g a | inspect (to g) a | from f c | inspect (from f) c
        inv {c} {a} | just b₁ | [ ab∈g₁ ] | just b₂ | [ cb∈f₂ ] = left , right
          where left : (b₂ , a) ∈ (from g) → (b₁ , c) ∈ (to f)
                left ba∈g₂ =
                  let bc∈f₂ = left-inverse-of f cb∈f₂
                      ab∈g₂ = left-inverse-of g ba∈g₂ in
                      trans (cong (to f) (just-injective (trans (sym ab∈g₁) ab∈g₂))) bc∈f₂

                right : (b₁ , c) ∈ᵗ f → (a , b₂) ∈ᶠ g
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

infixr 3 _∘_

-- Invert a bijection
_⁻¹ : ∀ {A : Set} {B : Set} → A ⤖ᴾ B → B ⤖ᴾ A
β ⁻¹ = record { to = from ; from = to ; inverse-of = right-inverse-of , left-inverse-of }
  where open Bijectionᴾ β

infixr 5 _⁻¹

module Singleton {A B} {{_≟ᴬ_ : DecEq A}} {{_≟ᴮ_ : DecEq B}} where
  instance _ = _≟ᴬ_
           _ = _≟ᴮ_

  -- Singleton bijection
  _↔_ : ∀ (x : A) (y : B) → A ⤖ᴾ B
  _↔_ x y  = bijᴾ (x ↦ y) (y ↦ x) inverse-of-↦

  ↔-∈ : ∀ x y → (x , y) ∈ᴮ (x ↔ y)
  ↔-∈ x y = trivial x y , trivial y x

open Singleton {{...}} public

--------------------------------------------------------------------------------
-- TODO: Are these ever used?

-- Disjoint bijections.
-- β₁ # β₂ denotes that β₂ is disjoint from β₁, i.e., the
-- maps of β₁ and β₂ are respectively disjoint.
_#_ : ∀ {A B} → (β₁ β₂ : Bijectionᴾ A B) → Set
_#_ {A} β₁ β₂ = (B₁.to #ᴾ B₂.to) × (B₁.from #ᴾ B₂.from)
  where module B₁ = Bijectionᴾ β₁
        module B₂ = Bijectionᴾ β₂

infixr 2 _#_


-- Parallel composition of from
_∣ᶠ_ : ∀ {A B} → (β₁ β₂ : Bijectionᴾ A B) → B ⇀ A
β₁ ∣ᶠ β₂ = from β₁ ∣ᴾ from β₂
  where open Bijectionᴾ

_∣ᵗ_ : ∀ {A B} → (β₁ β₂ : Bijectionᴾ A B) → A ⇀ B
β₁ ∣ᵗ β₂ = to β₁ ∣ᴾ to β₂
  where open Bijectionᴾ

-- Parallel composition of disjoint bijections
_∣ᴮ_ : ∀ {A B} → (β₁ β₂ : Bijectionᴾ A B) {{β₁#β₂ : β₁ # β₂}} → Bijectionᴾ A B
_∣ᴮ_ {A} {B} β₁ β₂ {{ to-# , from-# }} =
  record { to   = β₁ ∣ᵗ β₂
         ; from = β₁ ∣ᶠ β₂
         ; inverse-of = left , right
         } -- isB-∘ β₁ β₂ (to-# , from-#) }
  where module B₁ = Bijectionᴾ β₁
        module B₂ = Bijectionᴾ β₂
        module B₁′ = Bijectionᴾ (β₁ ⁻¹) -- TODO: are these used?
        module B₂′ = Bijectionᴾ (β₂ ⁻¹) -- TODO: are these used?
        left  = inverse-compose B₁.left-inverse-of B₂.left-inverse-of from-# to-#
        right = inverse-compose B₁.right-inverse-of B₂.right-inverse-of to-# from-#


-- TODO: probably it'd be nice to do the other one to
∣ᴮ-⊆₁  : ∀ {A B} → (β₁ β₂ : Bijectionᴾ A B) {{β₁#β₂ : β₁ # β₂}} → β₁ ⊆ (β₁ ∣ᴮ β₂)
∣ᴮ-⊆₁ β₁ β₂ = record { bij-⊆ = bij-⊆′ }
  where module B₁ = Bijectionᴾ β₁
        module B₂ = Bijectionᴾ β₂
        bij-⊆′ : (β₁ ∣ᴮ β₂) Extends β₁
        bij-⊆′ {x , y} ∈₁ with B₁.to x
        bij-⊆′ {x , y} ∈₁ | just x₁ = ∈₁
        bij-⊆′ {x , y} () | nothing

postulate ∣ᴮ-⊆₂  : ∀ {A B} → (β₁ β₂ : Bijectionᴾ A B) {{β₁#β₂ : β₁ # β₂}} → β₂ ⊆ (β₁ ∣ᴮ β₂)


-- _∣ᴮ_[_] : ∀ {A B} → (β₁ β₂ : Bijectionᴾ A B) (β₁#β₂ : β₁ # β₂) → Bijectionᴾ A B
-- β₁ ∣ᴮ β₂ [ β₁#β₂ ] = β₁ ∣ᴮ β₂
--   where instance _ = β₁#β₂

-- These seem too complicated to use in practice

-- Maybe module?

-- Add a single pair to the right of a bijection
-- _▻_ : ∀ {A B} (β : Bijectionᴾ A B) (x : A × B) →
--        let (a , b) = x in
--          {{∉ᴬ : a ∉ᴰ Bijectionᴾ.to β}} {{∉ᴮ : b ∉ᴰ Bijectionᴾ.from β}}
--          {{_≟ᴬ_ : DecEq A}} {{_≟ᴮ_ : DecEq B}} → Bijectionᴾ A B
-- _▻_ β (a , b) {{ ∉ᴬ }} {{ ∉ᴮ }} {{_≟ᴬ_}} {{_≟ᴮ_}} = β ∣ᴮ (a ↔ b)
--   where instance _ = _≟ᴬ_
--                  _ = _≟ᴮ_
--                  _ : β # a ↔ b
--                  _ = ∉-# (Bijectionᴾ.to β) ∉ᴬ , ∉-# (Bijectionᴾ.from β) ∉ᴮ

-- -- Add a single pair to the left of a bijection
-- _◅_ : ∀ {A B} (x : A × B) (β : Bijectionᴾ A B) →
--        let (a , b) = x in
--          {{∉ᴬ : a ∉ᴰ Bijectionᴾ.to β}} {{∉ᴮ : b ∉ᴰ Bijectionᴾ.from β}}
--          {{_≟ᴬ_ : DecEq A}} {{_≟ᴮ_ : DecEq B}} → Bijectionᴾ A B
-- _◅_ (a , b) β {{ ∉ᴬ }} {{ ∉ᴮ }} {{_≟ᴬ_}} {{_≟ᴮ_}} = (a ↔ b) ∣ᴮ β
--   where instance _ = _≟ᴬ_
--                  _ = _≟ᴮ_
--                  _ : (a ↔ b) # β
--                  _ = sym-# (∉-# (Bijectionᴾ.to β) ∉ᴬ) , sym-# (∉-# (Bijectionᴾ.from β) ∉ᴮ)

split-∈ᵗ : ∀ {A B C : Set} {a c} {β₁ : A ⤖ᴾ B} {β₂ : B ⤖ᴾ C} →
             (a , c) ∈ᵗ (β₂ ∘ β₁) →
             ∃ (λ b → (a , b) ∈ᵗ β₁ × (b , c) ∈ᵗ β₂)
split-∈ᵗ {a = a} {β₁ = β₁} {β₂} ac∈ with Bijectionᴾ.to β₁  a
split-∈ᵗ {a = a} {β₁ = β₁} {β₂} ac∈ | just b with Bijectionᴾ.to β₂ b | inspect (Bijectionᴾ.to β₂) b
... | just c' | [ eq ] rewrite just-injective ac∈ | eq = b , refl  , eq
split-∈ᵗ {a = a} {β₁ = β₁} {β₂} () | just b | nothing | _
split-∈ᵗ {a = a} {β₁ = β₁} {β₂} () | nothing
  where module B₁ = Bijectionᴾ β₁
        module B₂ = Bijectionᴾ β₂


join-∈ᵗ : ∀ {A B C : Set} {a b c} {β₁ : A ⤖ᴾ B} {β₂ : B ⤖ᴾ C} →
            (a , b) ∈ᵗ β₁ → (b , c) ∈ᵗ β₂ → (a , c) ∈ᵗ (β₂ ∘ β₁)
join-∈ᵗ {a = a} {b} {c} {β₁} {β₂} x y with Bijectionᴾ.to β₁ a
join-∈ᵗ {a = a} {b} {c} {β₁} {β₂} x y | just b' with just-injective x
join-∈ᵗ {a = a} {.b} {c} {β₁} {β₂} x y | just b | refl = y
join-∈ᵗ {a = a} {b} {c} {β₁} {β₂} () y | nothing

--------------------------------------------------------------------------------

open Bijectionᴾ


-- lemma : ∀ {A} {a a' : A} {β} → to β a ≡ just a' → to β a' ≡ just a → a ≡ a'
-- lemma {_} {a} {a'} {β} eq₁ eq₂ with right-inverse-of β eq₁ | right-inverse-of β eq₂ | to β a | to β a'
-- ... | eq₁' | eq₂' | x | y = {!left-inverse-of β eq₁'!}

-- TODO: needed? remove
-- ⊆⁻¹ : ∀ {A} (β₁ β₂ : A ⤖ᴾ A) → β₁ ⊆ β₂ → β₂ ⁻¹ ⊆ β₁
-- ⊆⁻¹ = {!!}

-- injective : ∀ {A B a a' b} {β : A ⤖ᴾ B} → to β a ≡ just b → to β a' ≡ just b → a ≡ a'
-- injective = {!!}


-- TODO: remove
-- Is this true?
-- Can this be generalized
-- ∘-⊆ : ∀ {A} {β β₁ β₂ : A ⤖ᴾ A} → β ⊆ β₁ → β ⊆ β₂ → β ⊆ β₁ ∘ β ∘ β₂
-- ∘-⊆ {β = β} {β₁} {β₂} ⊆₁ ⊆₂ {(a , a')} x∈β with ⊆₁ x∈β | ⊆₂ x∈β
-- ... | r | q rewrite q  = join-∈ᵗ {b = a} {β₁ = β} {β₁} {!x∈β!} r
-- with injective x∈β {!!}
-- ... | eq = {!!}
-- with to β a'
-- ... | just x rewrite x∈β = {!!}
-- ... | nothing = {!⊥-elim!}


-- with inspect (to β) a' | to β a'
-- ... | [ eq ] | just a'' = {!!}
-- ... | [ eq ] | nothing = {!trans (sym x∈β) ?!}


--  with right-inverse-of (β₂ ⁻¹) (⊆₂ x∈β)
-- ... | eq = {!eq!}
-- with ⊆₁ x∈β | ⊆⁻¹ β β₂ ⊆₂ (right-inverse-of β₂ (⊆₂ x∈β))
-- ... | r | q = {!!}

-- rewrite q with right-inverse-of β x∈β
-- ... | x rewrite x = {!!}

-- ∘-⊆ {β₁ = β₁} {β₂} (a , b) x∈β₁ with Bijectionᴾ.to β₁ a | Bijectionᴾ.to β₂ a
-- ∘-⊆ {β₁ = β₁} {β₂} (a , .x) refl | just x | just x₁ = {!!}
-- ∘-⊆ {β₁ = β₁} {β₂} (a , .x) refl | just x | nothing = {!!}
-- ∘-⊆ {β₁ = β₁} {β₂} (a , b) () | nothing | y

-- Do we need also this? I think so.
-- ∘-⊆′ : ∀ {A} {β₁ β₂ : A ⤖ᴾ A} → β₁ ⊆ β₂ ∘ β₁
-- ∘-⊆′ {β₁ = β₁} {β₂} (a , b) x∈β₁ with Bijectionᴾ.to β₁ a
-- ∘-⊆′ {β₁ = β₁} {β₂} (a , .x) refl | just x = {!!}
-- ∘-⊆′ {β₁ = β₁} {β₂} (a , b) () | nothing
