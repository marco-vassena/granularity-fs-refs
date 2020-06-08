open import Lattice

module Generic.Store.Base {{𝑳 : Lattice}} (Ty : Set) (Value : Ty → Set) where

open import Data.Nat hiding (_≟_)
open import Data.Product

open import Generic.Calculus using (Flow; S; I)

-- A tagged memory cell can store either:
--
-- 1) An unlabeled value for a flow-insesitive reference (I), whose
--    label is stored in the immutable label of the reference
--
-- 2) An explicitly labeled value for a flow-sensitive reference (S),
--    the label in the cell determines its sensitivity and it may
--    increase during the execution.
--
data Cell (τ : Ty) : Flow → Set where
  ⌞_⌟ᴵ : Value τ → Cell τ I
  ⌞_⌟ˢ : Value τ × Label → Cell τ S

-- A store is a linear list of memory cells.
data Store : Set where
  [] : Store
  _∷_ : ∀ {τ s} → Cell τ s → Store → Store

-- Empty store
∅ : Store
∅ = []

-- TODO: Should not need this
-- Function extensionality (used for low-equivalence of stores)
--postulate store-≡ : Extensionality L.zero L.zero

--------------------------------------------------------------------------------
-- TODO : update description
-- Container operations (read and write) reified as dependent types.
-- Since these operations are partial, it is customary in Agda to
-- exploit dependent types to encode only the well-defined behaviour,
-- i.e., reading and writing to valid addresses.

-- Lookup e n Σ is the proof that the n-th cell of the container M
-- contains labeled value e: M[ n ] = c
data Lookup {τ s} (c : Cell s τ) : ℕ → Store → Set where
  Here : ∀ {Σ} → Lookup c 0 (c ∷ Σ)
  There : ∀ {Σ n τ' s'} {c' : Cell τ' s'} → Lookup c n Σ → Lookup c (suc n) (c' ∷ Σ)

-- Sytactic sugar for Lookup
_↦_∈_ : ∀ {τ s} → ℕ → Cell τ s → Store → Set
_↦_∈_ n c Σ = Lookup c n Σ

_∈_ :  ℕ → Store → Set
n ∈ Σ = ∃ (λ τ → ∃ (λ s →
          P.Σ (Cell τ s) (λ c → n ↦ c ∈ Σ)))
  where import Data.Product as P

-- Extracts the value from a flow-insensitive cell
_↦_∈ᴵ_ : ∀ {τ} → ℕ → Value τ → Store → Set
_↦_∈ᴵ_ n v Σ = Lookup ⌞ v ⌟ᴵ n Σ

-- Extracts the value and the label from a flow-sensitive cell
_↦_∈ˢ_ : ∀ {τ} → ℕ → (Value τ × Label) → Store → Set
_↦_∈ˢ_ n x Σ = Lookup ⌞ x ⌟ˢ n Σ

-- Write v n C₁ C₂ is the proof that updating container C₁ with v at
-- position n gives container C₂: C₂ ≔ C₁ [ n ↦ v ]
data Write {τ s} (c : Cell τ s) : ℕ → Store → Store → Set where
  Here : ∀ {Σ} {c' : Cell τ s} → Write c 0 (c' ∷ Σ) (c ∷  Σ)
  There : ∀ {Σ Σ' τ' s' n} {c' : Cell τ' s'} → Write c n Σ Σ' → Write c (suc n) (c' ∷ Σ) (c' ∷ Σ')

-- TODO: shortcuts for S and I?
-- Syntactic sugar for Write
_≔_[_↦_] : ∀ {τ s} → Store → Store → ℕ → Cell τ s → Set
_≔_[_↦_] Σ' Σ n c = Write c n Σ Σ'

_≔_[_↦_]ᴵ : ∀ {τ} → Store → Store → ℕ → Value τ → Set
_≔_[_↦_]ᴵ Σ' Σ n v = Σ' ≔ Σ [ n ↦ ⌞ v ⌟ᴵ ]

_≔_[_↦_]ˢ : ∀ {τ} → Store → Store → ℕ → (Value τ × Label) → Set
_≔_[_↦_]ˢ Σ' Σ n x = Σ' ≔ Σ [ n ↦ ⌞ x ⌟ˢ ]

-- snoc
_∷ᴿ_ : ∀ {τ s} → Store → Cell τ s → Store
[] ∷ᴿ c  = c ∷ []
(c₁ ∷ Σ) ∷ᴿ c = c₁ ∷ (Σ ∷ᴿ c)

-- ∥ C ∥ denotes the length of container C.
∥_∥ : Store → ℕ
∥ [] ∥  = 0
∥ _ ∷ Σ ∥ = suc ∥ Σ ∥

infix 1 ∥_∥

<-∈ : ∀ {n} {Σ : Store} → n < ∥ Σ ∥ → n ∈ Σ
<-∈ {Σ = []} ()
<-∈ {zero} {Σ = c ∷ Σ} (s≤s x) = _ , _ , c , Here
<-∈ {suc n} {Σ = c ∷ Σ} (s≤s x) with <-∈ x
... | _ , _ , _ , n∈Σ = _ , _ , _ , There n∈Σ
