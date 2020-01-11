open import Lattice
open import Relation.Binary

module Generic.Heap.LowEq
  {Ty : Set}
  {Value : Ty → Set}
  {{𝑳 : Lattice}}
  (_≈ⱽ_ :  ∀ {τ} → Value τ → Value τ → Set)
  (A : Label) where

open import Data.Product

import Generic.Heap.Base as H₁
module H = H₁
open H Ty Value


open import Generic.Bijection
open import Function.Equality
open import Function.Bijection as B
open import Data.Maybe
open import Relation.Binary.PropositionalEquality as P
open import Generic.Value.LowEq {Ty} {Value} _≈ⱽ_

-- β ⊆ᴰ μ if the domain of β is a subset of the domain of μ
-- _⊆ᴰ_ : Bij → Heap → Set
-- β ⊆ᴰ μ = ∀ {n} → n ∈ᴰ β →
--            ∃ (λ τ → Σ (Value τ) (λ v → n ↦ v ∈ᴴ μ))

-- -- β ⊆ᴿ μ if the range of β is a subset of the domain of μ
-- _⊆ᴿ_ : Bij → Heap → Set
-- β ⊆ᴿ μ = ∀ {n} → n ∈ᴿ β →
--            ∃ (λ τ → Σ (Value τ) (λ v → n ↦ v ∈ᴴ μ))

open import Data.Fin

-- Syntatic sugar. A bijection with domain and range equal
-- to the given heaps.
Bij⟨_,_⟩ : Heap → Heap → Set
Bij⟨ μ₁ , μ₂ ⟩ = Bij ∥ μ₁ ∥ᴴ ∥ μ₂ ∥ᴴ

-- Two heaps are A-equivalent up to bijection β iff the addresses
-- related by the bijection map to related values in the respective
-- heaps. Since the domain and the range of the bijection is indexed with
-- the size of the heaps, the lookups are safe.
-- To index the bijection correctly, the relation must first introduce
-- the heaps and then the bijection. The following definition defines
-- the usual infix operator as syntatic sugar.
Heap-≈ : (μ₁ μ₂ : Heap) → Bij⟨ μ₁ , μ₂ ⟩ → Set
Heap-≈ μ₁ μ₂ β =
  ∀ (x : Fin ∥ μ₁ ∥ᴴ) →
  let τ , v , ∈₁ = μ₁ [ x ]ᴴ
      τ' , v' , ∈₂ = μ₂ [ to ⟨$⟩ x ]ᴴ in v ≅ⱽ v'
  where open Bijection β
        open import Function.Equality

-- Syntactic sugar
_≈⟨_⟩ᴴ_ : ∀ {n} → (μ₁ : Heap) → Bij ∥ μ₁ ∥ᴴ n → (μ₂ : Heap) → {{eq : n ≡ ∥ μ₂ ∥ᴴ}} → Set
_≈⟨_⟩ᴴ_ μ₁ β μ₂ {{eq}} rewrite eq = Heap-≈ μ₁ μ₂ β


-- {[]} = {!!} , {!!}
--   where e = {!!}
-- refl-≈ᴴ {x ∷ μ} = {!!}


--        to-witness β
-- ∀ {n₁ n₂ τ} {v₁ v₂ : Value τ} →
--     let ↔ =  n₁ ↔ n₂ ∈ β    -- related in the bijection
--         ∈₁ = n₁ ↦ v₁ ∈ᴴ μ₁  -- value in first heap
--         ∈₂ = n₂ ↦ v₂ ∈ᴴ μ₂  -- value in second heap
--         ≈ = v₁ ≈ⱽ v₂ in     -- values low-equivalent
--           ↔ ⇔ (∈₁ × ∈₂ × ≈)


-- TODO: maybe what we need is an iff (⇔) so that if we split n₁ ↔ n₂
-- ∈ (β₁ ∘ β₂) we can obtain the proof n₂ ↦ v₂ ∈ᴴ μ₂

  -- Here we actually demand that the bijection contains
  -- only addresses in the heap. This could be stronger
  -- than what we need and seems to complicate things.
  --   ∃ (λ τ →
  --     Σ (Value² τ) (λ x →
  --     let v₁ , v₂ = x in
  --       n₁ ↦ v₁ ∈ᴴ μ₁ × n₂ ↦ v₂ ∈ᴴ μ₂ × v₁ ≈ⱽ v₂))
  -- where Value² = λ τ → Value τ × Value τ

-- 1) Define composition of bijections: ok

-- 2) prove transitivity: n₁ ↔ n₂ ∈ (β₁ ∘ β₂) into n₁ ↔ n₂ ∈ β₁ or n₁
-- ↔ n₂ ∈ β₂ (we might need the assumptions on domains)
-- 3) use ⇒ to obtain the membership proofs over the heaps
module ≈ᴴ-Equivalence (𝑽 : ∀ {τ} → IsEquivalence (_≈ⱽ_ {τ})) where

  module Shorthand where

    open import Data.Sum
    open import Data.Nat
    open import Relation.Binary renaming (IsEquivalence to R)
    open import Relation.Binary.PropositionalEquality
    open HProps 𝑽

    open import Data.Unit
    open import Generic.Container.Lemmas ⊤ Ty Value

    refl-≈ᴴ : ∀ {μ} → μ ≈⟨ ι ⟩ᴴ μ
    refl-≈ᴴ {μ} x = refl-≅ⱽ

    sym-≈ᴴ : ∀ {μ₁ μ₂} {β : Bij⟨ μ₁ , μ₂ ⟩ } → μ₁ ≈⟨ β ⟩ᴴ μ₂ → μ₂ ≈⟨ β ⁻¹ ⟩ᴴ μ₁
    sym-≈ᴴ {β = β} ≈ᴴ x with ≈ᴴ (Bijection.to (β ⁻¹) ⟨$⟩ x) | Bijection.left-inverse-of (β ⁻¹) x
    ... | ≈ⱽ | eq rewrite eq = sym-≅ⱽ ≈ⱽ

    trans-≈ᴴ : ∀ {μ₁ μ₂ μ₃} {β₁ : Bij⟨ μ₁ , μ₂ ⟩} {β₂ : Bij⟨ μ₂ , μ₃ ⟩} →
                 μ₁ ≈⟨ β₁ ⟩ᴴ μ₂ → μ₂ ≈⟨ β₂ ⟩ᴴ μ₃ → μ₁ ≈⟨ β₂ B.∘ β₁ ⟩ᴴ μ₃
    trans-≈ᴴ {β₁ = β₁} {β₂} ≈₁ ≈₂ x = trans-≅ⱽ (≈₁ x) (≈₂ (Bijection.to β₁ ⟨$⟩ x) )

    -- Notice that this is not strictly an equivalence because we must be able to choose the
    -- bijection and we need disjointness (as an extra assumption) for transitivity.

  open Shorthand
