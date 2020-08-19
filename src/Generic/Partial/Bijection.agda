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
-- TODO: how do we call this properties?

_⊆ᴿ_ : ∀ {A B C} → (A ⤖ᴾ B) → (B ⤖ᴾ C) → Set
β₁ ⊆ᴿ β₂ = ∀ {y} → y ∈ᴿ′ β₁ → y ∈ᴰ β₂

infixl 3 _⊆ᴿ_

_⊆ᴰ_ : ∀ {A B} → A ⤖ᴾ B → A ⤖ᴾ B → Set
β₁ ⊆ᴰ β₂ = ∀ {x} → x ∈ᴰ β₁ → x ∈ᴰ β₂

infixr 3 _⊆ᴰ_

--------------------------------------------------------------------------------
-- Operations

-- Composition of bijections
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


split-∈ᵗ : ∀ {A B C : Set} {a c} {β₁ : A ⤖ᴾ B} {β₂ : B ⤖ᴾ C} →
             (a , c) ∈ᵗ (β₂ ∘ β₁) →
             ∃ (λ b → (a , b) ∈ᵗ β₁ × (b , c) ∈ᵗ β₂)
split-∈ᵗ {a = a} {β₁ = β₁} {β₂} ac∈ with Bijectionᴾ.to β₁  a
split-∈ᵗ {a = a} {β₁ = β₁} {β₂} ac∈ | just b with Bijectionᴾ.to β₂ b | inspect (Bijectionᴾ.to β₂) b
... | just c' | [ eq ] rewrite just-injective ac∈ | eq = b , refl  , eq
split-∈ᵗ {a = a} {β₁ = β₁} {β₂} () | just b | nothing | _
split-∈ᵗ {a = a} {β₁ = β₁} {β₂} () | nothing

split-∈ᶠ : ∀ {A B C : Set} {a c} {β₁ : A ⤖ᴾ B} {β₂ : B ⤖ᴾ C} →
             (a , c) ∈ᶠ (β₂ ∘ β₁) →
             ∃ (λ b → (a , b) ∈ᶠ β₁ × (b , c) ∈ᶠ β₂)
split-∈ᶠ {β₁ = β₁} {β₂} ∈∘ =
  let (b , ∈₁ , ∈₂) = split-∈ᵗ {β₁ = β₁} {β₂} (left-inverse-of (β₂ ∘ β₁) ∈∘)
  in b , right-inverse-of β₁ ∈₁ , right-inverse-of β₂ ∈₂
  where open Bijectionᴾ

join-∈ᵗ : ∀ {A B C : Set} {a b c} {β₁ : A ⤖ᴾ B} {β₂ : B ⤖ᴾ C} →
            (a , b) ∈ᵗ β₁ → (b , c) ∈ᵗ β₂ → (a , c) ∈ᵗ (β₂ ∘ β₁)
join-∈ᵗ {a = a} {b} {c} {β₁} {β₂} x y with Bijectionᴾ.to β₁ a
join-∈ᵗ {a = a} {b} {c} {β₁} {β₂} x y | just b' with just-injective x
join-∈ᵗ {a = a} {.b} {c} {β₁} {β₂} x y | just b | refl = y
join-∈ᵗ {a = a} {b} {c} {β₁} {β₂} () y | nothing


--------------------------------------------------------------------------------

-- Invert a bijection
_⁻¹ : ∀ {A : Set} {B : Set} → A ⤖ᴾ B → B ⤖ᴾ A
β ⁻¹ = record { to = from ; from = to ; inverse-of = right-inverse-of , left-inverse-of }
  where open Bijectionᴾ β

infixr 5 _⁻¹

-- Singleton Bijection (containing only 1 pair)
module Singleton {A B} {{_≟ᴬ_ : DecEq A}} {{_≟ᴮ_ : DecEq B}} where
  instance _ = _≟ᴬ_
           _ = _≟ᴮ_

  -- Singleton bijection
  _↔_ : ∀ (x : A) (y : B) → A ⤖ᴾ B
  _↔_ x y  = bijᴾ (x ↦ y) (y ↦ x) inverse-of-↦

  ↔-∈ : ∀ x y → (x , y) ∈ᴮ (x ↔ y)
  ↔-∈ x y = trivial x y , trivial y x

  ↔-∈ᵗ : ∀ x y → (x , y) ∈ᵗ (x ↔ y)
  ↔-∈ᵗ x y = proj₁ (↔-∈ x y)

open Singleton {{...}} public

--------------------------------------------------------------------------------

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


∣ᴮ-⊆₁  : ∀ {A B} → (β₁ β₂ : Bijectionᴾ A B) {{β₁#β₂ : β₁ # β₂}} → β₁ ⊆ (β₁ ∣ᴮ β₂)
∣ᴮ-⊆₁ β₁ β₂ = record { bij-⊆ = bij-⊆′ }
  where module B₁ = Bijectionᴾ β₁
        module B₂ = Bijectionᴾ β₂
        bij-⊆′ : (β₁ ∣ᴮ β₂) Extends β₁
        bij-⊆′ {x , y} ∈₁ with B₁.to x
        bij-⊆′ {x , y} ∈₁ | just x₁ = ∈₁
        bij-⊆′ {x , y} () | nothing

∣ᴮ-⊆₂  : ∀ {A B} → (β₁ β₂ : Bijectionᴾ A B) {{β₁#β₂ : β₁ # β₂}} → β₂ ⊆ (β₁ ∣ᴮ β₂)
∣ᴮ-⊆₂ β₁ β₂ {{ β₁#β₂ }} = record { bij-⊆ = bij-⊆′ }
  where module B₁ = Bijectionᴾ β₁
        module B₂ = Bijectionᴾ β₂
        open import Data.Maybe.Base
        bij-⊆′ : (β₁ ∣ᴮ β₂) Extends β₂
        bij-⊆′ {x , y} ∈₁ with B₁.to x | inspect B₁.to x
        bij-⊆′ {x , y} ∈₁ | just x₁ | [ eq ] with proj₁ β₁#β₂ x  (∈-just _ _ B₁.to eq) | B₂.to x | inspect B₂.to x
        bij-⊆′ {x , y} ∈₁ | just x₁ | [ eq ] | r | just x₂ | [ eq' ]
          rewrite eq' = ⊥-elim (⊥-is-nothing-just r)
        bij-⊆′ {x , y} () | just x₁ | [ eq ] | r | nothing | [ eq' ]
        bij-⊆′ {x , y} ∈₁ | nothing | _ = ∈₁

--------------------------------------------------------------------------------
-- Equality of bijections

-- Basic functional extensionality.
postulate funext : ∀ {A : Set} {B : Set} (f g : A → B) → (∀ x → f x ≡ g x) → f ≡ g

-- Function extensionality for dependently typed functions (with implicit arguments)
postulate funext₂ : ∀ {A B : Set} {F : A → B → Set} (f g : ∀ {x y} → F x y) →
                      (∀ x y → f {x} {y} ≡ g {x} {y}) →
                      (λ {x} {y} → f {x} {y}) ≡ (λ {x} {y} → g {x} {y})

-- Functions over equalities are equal
≡-equality-funs : ∀ {A B : Set} {a b : A} {c d : B} (f g : a ≡ b → c ≡ d) (eq : a ≡ b) → f eq ≡ g eq
≡-equality-funs f g eq rewrite ≡-irrelevance (f eq) (g eq) = refl

≡-inverse-of : ∀ {A : Set} {f g : A ⇀ A} → (p q : f InverseOfᴾ g) (x y : A) → p {x} {y} ≡ q {x} {y}
≡-inverse-of p q x y with p {x} {y} | q {x} {y}
... | a , b | c , d
  rewrite funext a c (≡-equality-funs a c) | funext b d (≡-equality-funs b d)
  = refl

bij-≡ : ∀ {A} → (β₁ β₂ : Bijectionᴾ A A) →
        let module B₁ = Bijectionᴾ
            module B₂ = Bijectionᴾ in
        B₁.to β₁ ≡ B₂.to β₂ → B₁.from β₁ ≡ B₂.from β₂ → β₁ ≡ β₂
bij-≡
  record { to = to₁ ; from = from₁ ; inverse-of = inverse-of₁ }
  record { to = to₂ ; from = from₂ ; inverse-of = inverse-of₂ } refl refl
  rewrite funext₂ (λ {x} {y} → inverse-of₁ {x} {y}) inverse-of₂ (≡-inverse-of inverse-of₁ inverse-of₂)
  = refl

--------------------------------------------------------------------------------
-- More lemmas

-- Only one pre-image
only-oneᶠ : ∀ {A B} {x₁ x₂ y} (β : Bijectionᴾ A B)  →
             (x₁ , y) ∈ᵗ β → (x₂ , y) ∈ᵗ β → x₁ ≡ x₂
only-oneᶠ {x₁ = x₁} {x₂} {y} β ∈₁ ∈₂ = just-injective proof
  where open Bijectionᴾ β
        open ≡-Reasoning
        proof : just x₁ ≡ (just x₂)
        proof =
          begin just x₁ ≡⟨ sym (right-inverse-of ∈₁) ⟩
          from y ≡⟨ right-inverse-of ∈₂ ⟩
          just x₂ ∎

-- Only one image
only-oneᵗ : ∀ {A B} {x y₁ y₂} (β : Bijectionᴾ A B) →
             (x , y₁) ∈ᵗ β → (x , y₂) ∈ᵗ β → y₁ ≡ y₂
only-oneᵗ β ∈₁ ∈₂ = only-oneᶠ (β ⁻¹) (left-inverse-of ∈₁) (left-inverse-of ∈₂)
  where open Bijectionᴾ (β ⁻¹)

-- TODO: maybe move lemmas in a separate module
