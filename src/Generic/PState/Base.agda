open import Lattice
open import Generic.Bijection

module Generic.PState.Base
  {{𝑳 : Lattice}}
  (Ty₁ : Set) (Ty₂ : Set)
  (Value₁ : Ty₁ → Set) (Value₂ : Ty₂ → Set)
  where

open import Generic.Store Ty₁ Value₁
open import Generic.Heap Ty₂ Value₂

-- Program State
record PState : Set where
  constructor ⟨_,_⟩
  field
    store : Store
    heap : Heap
