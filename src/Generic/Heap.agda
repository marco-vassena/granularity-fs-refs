open import Lattice
open import Generic.LValue

-- There is no particular reason for calling this heap.
-- It is mostly to avoid clashing names with memory and store.
module Generic.Heap {{𝑳 : Lattice}} (Ty : Set) (Value : Ty → Set) where

open import Generic.Heap.Base Ty Value public
