open import Lattice

module Generic.FS-Store (Ty : Set) (Value : Ty → Set) where

open import Data.Unit

-- TODO: should we constraint the type of the values (for CG?)

open import Generic.Container ⊤ Ty Value
  renaming ( Lookup to Lookupˢ
           ; _↦_∈_ to _↦_∈ˢ_
           ; Write to Writeˢ
           ; _≔_[_↦_] to _≔_[_↦_]ˢ
           ; _∷ᴿ_ to snocˢ
           ; ∥_∥ to ∥_∥ˢ
           ) public

FS-Store : Set
FS-Store = Container tt
