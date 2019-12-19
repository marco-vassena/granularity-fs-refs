open import Lattice

-- There is no particular reason for calling this heap.
-- It is mostly to avoid clashing names with memory and store.
module Generic.Heap (Ty : Set) (Value : Ty → Set) where

open import Generic.Heap.Base Ty Value public
