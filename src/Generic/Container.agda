-- Module for generic labeled list-like containers storing typed values
module Generic.Container (Label : Set) (Ty : Set) (Value : Ty → Set) where

open import Data.Nat

data Container (ℓ : Label) : Set where
  [] : Container ℓ
  _∷_ : ∀ {τ} → Value τ → Container ℓ → Container ℓ

open Container public

-- Container operations (read and write) reified as dependent types.
-- Since these operations are partial, it is customary in Agda to
-- exploit dependent types to encode only the well-defined behaviour,
-- i.e., reading and writing to valid addresses.

-- Lookup e n C is the proof that the n-th cell of the container M
-- contains labeled value e: M[ n ] = c
data Lookup {ℓ τ} (v : Value τ) : ℕ → Container ℓ → Set where
  Here : ∀ {M} → Lookup v 0 (v ∷ M)
  There : ∀ {C n τ'} {v' : Value τ'} → Lookup v n C → Lookup v (suc n) (v' ∷ C)

-- Sytactic sugar for Lookup
_↦_∈_ : ∀ {ℓ τ} → ℕ → Value τ → Container ℓ → Set
_↦_∈_ n v C = Lookup v n C

-- Write v n C₁ C₂ is the proof that updating container C₁ with v at
-- position n gives container C₂: C₂ ≔ C₁ [ n ↦ v ]
data Write {ℓ τ} (v : Value τ) : ℕ → Container ℓ → Container ℓ → Set where
  Here : ∀ {M} {v' : Value τ} → Write v 0 (v' ∷ M) (v ∷  M)
  There : ∀ {C C' τ' n} {v' : Value τ'} → Write v n C C' → Write v (suc n) (v' ∷ C) (v' ∷ C')

-- Syntactic sugar for Write
_≔_[_↦_] : ∀ {ℓ τ} → Container ℓ → Container ℓ → ℕ → Value τ → Set
_≔_[_↦_] C' C n v = Write v n C C'

-- snoc
_∷ᴿ_ : ∀ {ℓ τ} → Container ℓ → Value τ → Container ℓ
[] ∷ᴿ r  = r ∷ []
(r₁ ∷ C) ∷ᴿ r = r₁ ∷ (C ∷ᴿ r)

-- ∥ C ∥ denotes the length of container C.
∥_∥ : ∀ {ℓ} → Container ℓ → ℕ
∥ [] ∥  = 0
∥ _ ∷ C ∥ = suc ∥ C ∥

infix 1 ∥_∥

--------------------------------------------------------------------------------
-- Some lemmas.

open import Relation.Binary.PropositionalEquality

-- TODO: haven't we proved this already somewhere?
inj-∈ : ∀ {ℓ n τ} {C : Container ℓ} {v₁ v₂ : Value τ} →
        n ↦ v₁ ∈ C → n ↦ v₂ ∈ C → v₁ ≡ v₂
inj-∈ Here Here = refl
inj-∈ (There x) (There y) = inj-∈ x y
