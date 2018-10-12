-- Value and type generic labeled store and memory

import Lattice as L

module Generic.Store {{𝑳 : L.Lattice}} (Ty : Set) (Value : Ty → Set) where

open import Generic.Store.Base Ty Value public
