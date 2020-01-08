
module Generic.PMap where

open import Data.Empty
open import Data.Unit
open import Data.Maybe
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

-- Partial Map
_⇀_ : Set → Set → Set
A ⇀ B = A → Maybe B

infix 1 _⇀_

-- Disjoint partial maps
_▻ᴾ_ : ∀ {A B} → A ⇀ B → A ⇀ B → Set
f ▻ᴾ g = ∀ a → Is-just (f a) → Is-nothing (g a)

-- Lemmas
⊥-is-nothing-just : ∀ {A : Set} {x : A} → ¬ Is-nothing (just x)
⊥-is-nothing-just (just ())

is-just-nothing : ∀ {A : Set} {y : A} (x : Maybe A) → (Is-just x → Is-nothing (just y)) → x ≡ nothing
is-just-nothing {y = y} (just x) f = ⊥-elim (⊥-is-nothing-just (f (just tt)))
is-just-nothing nothing f = refl

-- Proof that a maps to b in the partial map.
_↦_∈ᴾ_ : ∀ {A B} → A → B → A ⇀ B → Set
a ↦ b ∈ᴾ p = p a ≡ just b

infix 1 _↦_∈ᴾ_

-- TODO: remove
module PMapUtil (A B : Set) {{ _≟ᴬ_ : Decidable (_≡_ {A = A}) }}  where

  -- Update partial map
  _[_↦_]ᴾ : A ⇀ B → A → B → A ⇀ B
  _[_↦_]ᴾ f a b a' with a ≟ᴬ a'
  _[_↦_]ᴾ f a b .a | yes refl = just b
  _[_↦_]ᴾ f a b a' | no ¬p = f a
