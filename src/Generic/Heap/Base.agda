module Generic.Heap.Base (Ty : Set) (Value : Ty → Set) where

open import Data.Unit

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
           ) public

Heap : Set
Heap = Container tt

open import Function
open import Data.Fin
open import Data.Product

_[_]ᴴ : (μ : Heap) (x : Fin ∥ μ ∥ᴴ) →
           ∃ (λ τ → Σ (Value τ) (λ v → toℕ x ↦ v ∈ᴴ μ))
[] [ () ]ᴴ
(v ∷ μ) [ zero ]ᴴ = _ , v , Here
(v ∷ μ) [ suc x ]ᴴ = map id (map id There) (μ [ x ]ᴴ)
