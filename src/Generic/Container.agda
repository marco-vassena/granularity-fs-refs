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
-- Labeled memory

-- Memory : Label → Set
-- Memory ℓ = Container ℓ
--   where open Container Label

-- open Container Label
--   renaming ( -- [] to []ᴹ
--            -- ; _∷_ to _∷ᴹ_
--            -- ;
--            Lookup to Lookupᴹ
--            ; _↦_∈_ to _↦_∈ᴹ_
--            ; Write to Writeᴹ
--            ; _≔_[_↦_] to _≔_[_↦_]ᴹ
--            )

--------------------------------------------------------------------------------
-- Store

-- A store is a mapping from labels to labeled memories.
-- Store : Set
-- Store = (ℓ : Label) → Memory ℓ

-- -- Σ [ l ↦ M ]ˢ updates store Σ with l labeled memory M.
-- _[_↦_]ˢ : Store -> (l : Label) -> Memory l -> Store
-- _[_↦_]ˢ  Σ l M l' with l ≟ l'
-- _[_↦_]ˢ Σ l M .l | yes refl = M
-- _[_↦_]ˢ Σ l M l' | no ¬p = Σ l'

-- -- Empty store
-- ∅ : Store
-- ∅ _ = []

-- -- Function extensionality (used for low-equivalence of stores)
-- postulate store-≡ : Extensionality L.zero L.zero

--------------------------------------------------------------------------------

-- Heterogeneous store for flow-sensitive references

-- TODO: should we constraint the type of the values (for CG?)

-- open import Data.Unit

-- FS-Store : Set
-- FS-Store = GContainer.Container ⊤ tt -- unit because this container is unlabeled

-- open GContainer ⊤ public
--   renaming (
--            -- [] to []ˢ
--             Lookup to Lookupˢ
--            ; _↦_∈_ to _↦_∈ˢ_
--            ; Write to Writeˢ
--            ; _≔_[_↦_] to _≔_[_↦_]ˢ
--            )

-- foo : ∀ {ℓ} → Memory ℓ → Set
-- foo [] = {!!}
-- foo (_ ∷ _)  = {!!}

-- -- fails with
-- -- Can't resolve overloaded constructors targeting the same datatype
-- -- (Generic.Store.Base.GContainer.Container): Generic.Store.Base._.[]
-- -- Generic.Store.Base._.[]
-- -- when checking that the pattern [] has type Memory ℓ
