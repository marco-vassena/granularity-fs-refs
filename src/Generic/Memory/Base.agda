open import Lattice

module Generic.Memory.Base {{𝑳 : Lattice}} (Ty : Set) (Value : Ty → Set) where

open import Generic.Container Label Ty Value
  renaming ( Lookup to Lookupᴹ
           ; _↦_∈_ to _↦_∈ᴹ_
           ; Write to Writeᴹ
           ; _≔_[_↦_] to _≔_[_↦_]ᴹ
           ; _∷ᴿ_ to snocᴹ
           ; ∥_∥ to ∥_∥ᴹ
           ; _⊆_ to _⊆ᴹ_
           ; _∈_ to _∈ᴹ_
           ; _∉_ to _∉ᴹ_
           ; _⊆′_ to _⊆ᴹ′_
           ) public

Memory : Label → Set
Memory ℓ = Container ℓ
