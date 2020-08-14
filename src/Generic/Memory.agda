open import Lattice

module Generic.Memory {{𝑳 : Lattice}} (Ty : Set) (Value : Ty → Set) where

open import Generic.Memory.Base Ty Value hiding (Container) public
