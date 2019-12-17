
module Generic.PMap where

open import Data.Maybe
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

-- Partial Map
_⇀_ : Set → Set → Set
A ⇀ B = A → Maybe B

infix 1 _⇀_

-- Proof that a maps to b in the partial map.
_↦_∈ᴾ_ : ∀ {A B} → A → B → A ⇀ B → Set
a ↦ b ∈ᴾ p = p a ≡ just b

infix 1 _↦_∈ᴾ_

module PMapUtil (A B : Set) {{ _≟ᴬ_ : Decidable (_≡_ {A = A}) }}  where

  -- Update partial map
  _[_↦_]ᴾ : A ⇀ B → A → B → A ⇀ B
  _[_↦_]ᴾ f a b a' with a ≟ᴬ a'
  _[_↦_]ᴾ f a b .a | yes refl = just b
  _[_↦_]ᴾ f a b a' | no ¬p = f a
