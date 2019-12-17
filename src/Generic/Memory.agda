open import Lattice

module Generic.Memory {{𝑳 : Lattice}} (Ty : Set) (Value : Ty → Set) where

open import Generic.Container Label Ty Value
  renaming ( Container to Memory
           ; Lookup to Lookupᴹ
           ; _↦_∈_ to _↦_∈ᴹ_
           ; Write to Writeᴹ
           ; _≔_[_↦_] to _≔_[_↦_]ᴹ
           ) public
