module Generic.Partial.Bijection where

import Function as F
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
import Level as L
open import Category.Monad
open import Data.Empty
open import Data.Maybe as M
open import Data.Product
open import Generic.Partial.Function renaming (∅ to ∅ᴾ ; _#_ to _#ᴾ_ ; _∣′_ to _∣ᴾ_) public

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
        -- TODO: improve proof
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

-- Singleton bijection
_↔_ : ∀ {A B} {{_≟ᴬ_ : DecEq A}} {{_≟ᴮ_ : DecEq B}} (x : A) (y : B) → A ⤖ᴾ B
_↔_ {A} {B} {{_≟ᴬ_}} {{_≟ᴮ_}} x y  = bijᴾ (x ↦ y) (y ↦ x) inverse-of-↦
  where instance _ = _≟ᴬ_
                 _ = _≟ᴮ_


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
        module B₁′ = Bijectionᴾ (β₁ ⁻¹)
        module B₂′ = Bijectionᴾ (β₂ ⁻¹)
        left  = inverse-compose B₁.left-inverse-of B₂.left-inverse-of from-# to-#
        right = inverse-compose B₁.right-inverse-of B₂.right-inverse-of to-# from-#

-- Add a single pair to the right of a bijection
_▻_ : ∀ {A B} (β : Bijectionᴾ A B) (x : A × B) →
       let (a , b) = x in
         {{∉ᴬ : a ∉ᴰ Bijectionᴾ.to β}} {{∉ᴮ : b ∉ᴰ Bijectionᴾ.from β}}
         {{_≟ᴬ_ : DecEq A}} {{_≟ᴮ_ : DecEq B}} → Bijectionᴾ A B
_▻_ β (a , b) {{ ∉ᴬ }} {{ ∉ᴮ }} {{_≟ᴬ_}} {{_≟ᴮ_}} = β ∣ᴮ (a ↔ b)
  where instance _ = _≟ᴬ_
                 _ = _≟ᴮ_
                 _ : β # a ↔ b
                 _ = ∉-# (Bijectionᴾ.to β) ∉ᴬ , ∉-# (Bijectionᴾ.from β) ∉ᴮ

-- Add a single pair to the left of a bijection
_◅_ : ∀ {A B} (x : A × B) (β : Bijectionᴾ A B) →
       let (a , b) = x in
         {{∉ᴬ : a ∉ᴰ Bijectionᴾ.to β}} {{∉ᴮ : b ∉ᴰ Bijectionᴾ.from β}}
         {{_≟ᴬ_ : DecEq A}} {{_≟ᴮ_ : DecEq B}} → Bijectionᴾ A B
_◅_ (a , b) β {{ ∉ᴬ }} {{ ∉ᴮ }} {{_≟ᴬ_}} {{_≟ᴮ_}} = (a ↔ b) ∣ᴮ β
  where instance _ = _≟ᴬ_
                 _ = _≟ᴮ_
                 _ : (a ↔ b) # β
                 _ = sym-# (∉-# (Bijectionᴾ.to β) ∉ᴬ) , sym-# (∉-# (Bijectionᴾ.from β) ∉ᴮ)
