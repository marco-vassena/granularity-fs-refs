open import Lattice
open import Generic.LValue
open import Data.Nat

module Generic.Heap.Valid
  {{𝑳 : Lattice}}
  {Ty : Set}
  {Value : Ty → Set}
  (𝑯 : HasLabel Ty Value)
  (Dom : ∀ {τ} → Value τ → ℕ) where

open import Data.Unit hiding (_≤_)
open import Generic.Heap.Base {Ty} {Value} 𝑯

Validⱽ : ∀ {τ} → LValue τ → Heap → Set
Validⱽ v μ = Dom v ≤ ∥ μ ∥ᴴ

open import Generic.Container.Valid ⊤ Ty LValue Validⱽ renaming (Valid to Validᴴ) public
