open import Lattice

module Generic.Heap.Lemmas
  {{𝑳 : Lattice}}
  (Ty : Set)
  (Value : Ty → Set) where

open import Data.Unit
open import Generic.Container.Lemmas ⊤ Ty Value public
