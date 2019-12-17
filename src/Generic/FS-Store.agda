open import Lattice

module Generic.FS-Store (Ty : Set) (Value : Ty → Set) where

open import Data.Unit

-- TODO: should we constraint the type of the values (for CG?)

open import Generic.Container ⊤
  renaming ( Lookup to Lookupˢ
           ; _↦_∈_ to _↦_∈ˢ_
           ; Write to Writeˢ
           ; _≔_[_↦_] to _≔_[_↦_]ˢ
           )

FS-Store : Set
FS-Store = Container Ty Value tt
