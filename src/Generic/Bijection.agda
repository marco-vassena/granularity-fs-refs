open import Relation.Binary
open import Relation.Binary.PropositionalEquality

-- TODO reorganise. Definition Partial map before. The rest in nested module.

module Generic.Bijection
  (A B : Set)
  {{ _≟ᴬ_ : Decidable (_≡_ {A = A}) }}
  {{ _≟ᴮ_ : Decidable (_≡_ {A = B}) }}  where

open import Data.Product
open import Data.Maybe

-- Partial Map
_⇀_ : Set → Set → Set
A ⇀ B = A → Maybe B

infix 1 _⇀_

-- A bijection is a pair of partial maps between two sets.
record Bij (A B : Set) : Set where
  field  to : A ⇀ B
         back : B ⇀ A

-- A pair of values from A and B are in the bijection iff they are
-- mutually related under their respective mapping.
_↔_∈_ : ∀ {A B} → A → B → Bij A B → Set
a ↔ b ∈ 𝑩 = to a ≡ just b × back b ≡ just a
  where open Bij 𝑩

-- Empty bijection
∅ : ∀ {A B} → Bij A B
∅ = record { to = λ _ → nothing ; back = λ _ → nothing }

-- Add a new mapping to the bijection.
-- TODO: should we assume/require that they are not in the mapping already?
_⟨+⟩_ : ∀ {A B} → Bij A B → A × B → Bij A B
𝑩 ⟨+⟩ x = {!!}
