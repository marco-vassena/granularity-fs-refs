open import Lattice

module Generic.FS-Store (Ty : Set) (Value : Ty → Set) where

open import Data.Unit

open import Generic.Container ⊤
  renaming ( Container to FS-Store
           ; Lookup to Lookupˢ
           ; _↦_∈_ to _↦_∈ˢ_
           ; Write to Writeˢ
           ; _≔_[_↦_] to _≔_[_↦_]ˢ
           ) public
