module Generic.Bijection where

open import Generic.PMap
open import Data.Product
open import Data.Maybe
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

-- A bijection is a pair of partial maps between two sets.
record Bij (A B : Set) : Set where
  field  to : A ⇀ B
         back : B ⇀ A

-- A pair of values from A and B are in the bijection iff they are
-- mutually related under their respective mapping.
_↔_∈_ : ∀ {A B} → A → B → Bij A B → Set
a ↔ b ∈ β =  (a ↦ b ∈ᴾ to) × (b ↦ a ∈ᴾ back)
  where open Bij β

-- Empty bijection
∅ : ∀ {A B} → Bij A B
∅ = record { to = λ _ → nothing ; back = λ _ → nothing }

module Ops {A B : Set}
  {{ _≟ᴬ_ : Decidable (_≡_ {A = A}) }}
  {{ _≟ᴮ_ : Decidable (_≡_ {A = B}) }} where

  module AB = PMapUtil A B {{_≟ᴬ_}}
  module BA = PMapUtil B A {{_≟ᴮ_}}

  -- Add a new mapping to the bijection.
  -- TODO: should we assume/require that they are not in the mapping already?
  -- I won't add it until it comes out in the proof
  _⋃_ : Bij A B → A × B → Bij A B
  β ⋃ (a , b) = record { to = to AB.[ a ↦ b ]ᴾ ; back = back BA.[ b ↦ a ]ᴾ }
    where open Bij β
