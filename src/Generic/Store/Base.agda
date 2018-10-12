open import Lattice

module Generic.Store.Base {{𝑳 : Lattice}} (Ty : Set) (Value : Ty → Set) where

open import Data.Nat hiding (_≟_)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
import Level as L

--------------------------------------------------------------------------------
-- Labeled memory

-- A memory is a list of closed terms..
-- The label ℓ represents the sensitivity level of the terms contained in the memory.
data Memory (ℓ : Label) : Set where
  [] : Memory ℓ
  _∷_ : ∀ {τ} → (v : Value τ) (M : Memory ℓ) → Memory ℓ

-- Memory operations (read and write) reified as dependent types.
-- Since these operations are partial, it is customary in Agda to
-- exploit dependent types to encode only the well-defined behaviour,
-- i.e., reading and writing to valid addresses.

-- Lookupᴹ e n M is the proof that the n-th cell of the memory M
-- contains labeled value e: M[ n ] = c
data Lookupᴹ {ℓ τ} (v : Value τ) : ℕ → Memory ℓ → Set where
  Here : ∀ {M} → Lookupᴹ v 0 (v ∷ M)
  There : ∀ {M n τ'} {v' : Value τ'} → Lookupᴹ v n M → Lookupᴹ v (suc n) (v' ∷ M)

-- Sytactic sugar for Lookupᴹ
_↦_∈ᴹ_ : ∀ {ℓ τ} → ℕ → Value τ → Memory ℓ → Set
_↦_∈ᴹ_ n v M = Lookupᴹ v n M

-- Writeᴹ v n M₁ M₂ is the proof that updating memory M₁ with v at
-- position n gives memory M₂: M₂ ≔ M₁ [ n ↦ v ]
data Writeᴹ {ℓ τ} (v : Value τ) : ℕ → Memory ℓ → Memory ℓ → Set where
  Here : ∀ {M} {v' : Value τ} → Writeᴹ v 0 (v' ∷ M) (v ∷  M)
  There : ∀ {M M' τ' n} {v' : Value τ'} → Writeᴹ v n M M' → Writeᴹ v (suc n) (v' ∷ M) (v' ∷ M')

-- Syntactic sugar for Writeᴹ
_≔_[_↦_]ᴹ : ∀ {ℓ τ} → Memory ℓ → Memory ℓ → ℕ → Value τ → Set
_≔_[_↦_]ᴹ M' M n v = Writeᴹ v n M M'

-- snoc
_∷ᴿ_ : ∀ {ℓ τ} → Memory ℓ → Value τ → Memory ℓ
[] ∷ᴿ r  = r ∷ []
(r₁ ∷ M) ∷ᴿ r = r₁ ∷ (M ∷ᴿ r)

-- ∥ M ∥ denotes the length of memory M.
∥_∥ : ∀ {ℓ} → Memory ℓ → ℕ
∥ [] ∥  = 0
∥ _ ∷ M ∥ = suc ∥ M ∥

infix 1 ∥_∥

--------------------------------------------------------------------------------
-- Store

-- A store is a mapping from labels to labeled memories.
Store : Set
Store = (ℓ : Label) → Memory ℓ

-- Σ [ l ↦ M ]ˢ updates store Σ with l labeled memory M.
_[_↦_]ˢ : Store -> (l : Label) -> Memory l -> Store
_[_↦_]ˢ  Σ l M l' with l ≟ l'
_[_↦_]ˢ Σ l M .l | yes refl = M
_[_↦_]ˢ Σ l M l' | no ¬p = Σ l'

-- Empty store
∅ : Store
∅ _ = []

-- Function extensionality (used for low-equivalence of stores)
postulate store-≡ : Extensionality L.zero L.zero
