module Generic.Graph where

-- A generic graph of the function interface

-- Is this ever used?
open import Relation.Binary.PropositionalEquality
open import Data.Product

-- We cannot express simple graphs using an index graph becuase index
-- graphs are parametrized by simple graphs. We do not need more
-- general definitions at the moment so this distinction will do.

-- Graph for simple functions.
record Graph {A : Set} {B : Set} (⟪_⟫ : A → B) : Set₁ where
  field P : A → B → Set
        ⌜_⌝ : ∀ a → P a ⟪ a ⟫
        ⌞_⌟ : ∀ {a b} → P a b → b ≡ ⟪ a ⟫
