open import Lattice
open import Generic.LValue

module Generic.Heap.Base
  {{𝑳 : Lattice}}
  (Ty : Set)
  (Value : Ty → Set)
  -- (𝑯 : HasLabel Ty Value)
  where

-- open HasLabel 𝑯
open import Data.Unit
open import Function

-- Guaranteed to be labeled by 𝑯
-- LValue : Ty → Set
-- LValue τ = Value (F τ)

-- TODO: should we constraint the type of the values (for CG?)
-- yes, we must be able to project the label to identify secret
-- values.
open import Generic.Container ⊤ Ty Value
  renaming ( Lookup to Lookupᴴ
           ; _↦_∈_ to _↦_∈ᴴ_
           ; Write to Writeᴴ
           ; _≔_[_↦_] to _≔_[_↦_]ᴴ
           ; _∷ᴿ_ to snocᴴ
           ; ∥_∥ to ∥_∥ᴴ
           ; _⊆_ to _⊆ᴴ_
           ) public

open import Generic.Container.Base ⊤ Ty Value using (_∈_) public

Heap : Set
Heap = Container tt

-- open import Relation.Nullary
-- open import Function
-- open import Data.Fin
-- open import Data.Product

-- μ ↓⊑ ℓ returns the sub-heap of μ containing values whose label is below ℓ
-- _↓⊑_ : Heap → Label → Heap
-- _↓⊑_ [] ℓ  = []
-- _↓⊑_ (v ∷ μ) ℓ with (label v) ⊑? ℓ
-- ... | yes p = v ∷ (μ ↓⊑ ℓ)
-- ... | no ¬p = μ ↓⊑ ℓ

-- infixl 5 _↓⊑_

-- _[_]ᴴ : (μ : Heap) (x : Fin ∥ μ ∥ᴴ) →
--            ∃ (λ τ → Σ (LValue τ) (λ v → toℕ x ↦ v ∈ᴴ μ))
-- [] [ () ]ᴴ
-- (v ∷ μ) [ zero ]ᴴ = _ , v , Here
-- (v ∷ μ) [ suc x ]ᴴ = map id (map id There) (μ [ x ]ᴴ)
