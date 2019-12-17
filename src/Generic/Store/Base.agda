open import Lattice

module Generic.Store.Base {{𝑳 : Lattice}} (Ty : Set) (Value : Ty → Set) where

open import Data.Nat hiding (_≟_)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
import Level as L

open import Generic.Memory Ty Value public

-- A store is a mapping from labels to labeled memories.
Store : Set
Store = (ℓ : Label) → Memory ℓ

-- Σ [ ℓ ↦ M ] updates store Σ with ℓ ℓabeℓed memory M.
_[_↦_] : Store -> (ℓ : Label) -> Memory ℓ -> Store
_[_↦_]  Σ ℓ M ℓ' with ℓ ≟ ℓ'
_[_↦_] Σ ℓ M .ℓ | yes refl = M
_[_↦_] Σ ℓ M ℓ' | no ¬p = Σ ℓ'

-- Empty store
∅ : Store
∅ _ = []

-- Function extensionality (used for low-equivalence of stores)
postulate store-≡ : Extensionality L.zero L.zero
