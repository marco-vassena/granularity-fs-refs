module Generic.Heap.Base (Ty : Set) (Value : Ty → Set) where

open import Data.Unit

-- TODO: should we constraint the type of the values (for CG?)

open import Generic.Container ⊤ Ty Value
  renaming ( Lookup to Lookupᴴ
           ; _↦_∈_ to _↦_∈ᴴ_
           ; Write to Writeᴴ
           ; _≔_[_↦_] to _≔_[_↦_]ᴴ
           ; _∷ᴿ_ to snocᴴ
           ; ∥_∥ to ∥_∥ᴴ
           ) public

Heap : Set
Heap = Container tt