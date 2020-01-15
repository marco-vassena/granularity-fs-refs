{-# OPTIONS --allow-unsolved-metas #-}

open import Lattice
open import Relation.Binary
open import Generic.LValue as L

module Generic.Heap.LowEq
  {Ty : Set}
  {Value : Ty → Set}
  {{𝑳 : Lattice}}
  (𝑯 : HasLabel Ty Value)
  (_≈ⱽ_ :  ∀ {τ} → Value τ → Value τ → Set)
  (A : Label) where

open import Data.Product
open import Data.Fin hiding (_<_)
open import Data.Maybe
open import Generic.Bijection
open import Generic.Heap.Base 𝑯
-- open import Function.Equality
-- open import Function.Bijection as B
open import Relation.Binary.PropositionalEquality as P

-- A bijection with domain and range equal to the size of the heaps.
Bij⟨_,_⟩ : Heap → Heap → Set
Bij⟨ μ₁ , μ₂ ⟩ = Bij ∥ μ₁ ∥ᴴ ∥ μ₂ ∥ᴴ

-- Two heaps are A-equivalent up to bijection β iff the low addresses
-- related by the bijection correspond to related values in the
-- respective heaps. Since the domain and the range of the bijection
-- is indexed with the size of the (low parts of) heaps, the lookups
-- are safe.  To index the bijection correctly, the relation must
-- first introduce the heaps and then the bijection. The following
-- definition defines the usual infix operator as syntatic sugar.
Heap-≈ : (μ₁ μ₂ : Heap) → Bij⟨ μ₁ , μ₂ ⟩ → Set
Heap-≈ μ₁ μ₂ β =
  ∀ {x : Fin ∥ μ₁ ∥ᴴ} {y : Fin ∥ μ₂ ∥ᴴ} → (x , y) ∈ᵗ β →
  let τ , v , ∈₁ = μ₁ [ x ]ᴴ
      τ' , v' , ∈₂ = μ₂ [  y ]ᴴ in v ≅ⱽ v'
  where open Bijectionᴾ β
        open import Function.Equality
        open import Generic.Value.HLowEq {Ty} {Value} _≈ⱽ_

-- Syntactic sugar
_≈⟨_⟩ᴴ_ : ∀ {n} → (μ₁ : Heap) → Bij ∥ μ₁ ∥ᴴ n → (μ₂ : Heap) → {{eq : n ≡ ∥ μ₂ ∥ᴴ}} → Set
_≈⟨_⟩ᴴ_ μ₁ β μ₂ {{eq}} rewrite eq = Heap-≈ μ₁ μ₂ β

_≈ᴴ_ : Heap → Heap → Set
μ₁ ≈ᴴ μ₂ = Σ Bij⟨ μ₁ , μ₂ ⟩ (λ β → μ₁ ≈⟨ β ⟩ᴴ μ₂)

module Props (𝑽 : ∀ {τ} → IsEquivalence (_≈ⱽ_ {τ})) where

  open import Data.Unit
  open import Generic.LValue Ty Value
  open L.HasLabel 𝑯
  open import Generic.Value.HLowEq {Ty} {Value} _≈ⱽ_
  open Props 𝑽
  open import Relation.Binary.PropositionalEquality

  refl-≈ᴴ : ∀ {μ} → μ ≈⟨ ι ⟩ᴴ μ
  refl-≈ᴴ {μ} eq rewrite just-injective eq = refl-≅ⱽ

  sym-≈ᴴ : ∀ {μ₁ μ₂} {β : Bij⟨ μ₁ , μ₂ ⟩ } → μ₁ ≈⟨ β ⟩ᴴ μ₂ → μ₂ ≈⟨ β ⁻¹ ⟩ᴴ μ₁
  sym-≈ᴴ {β = β} ≈ᴴ eq = sym-≅ⱽ (≈ᴴ (right-inverse-of eq))
    where open Bijectionᴾ (β ⁻¹)

  trans-≈ᴴ : ∀ {μ₁ μ₂ μ₃} {β₁ : Bij⟨ μ₁ , μ₂ ⟩} {β₂ : Bij⟨ μ₂ , μ₃ ⟩} →
               μ₁ ≈⟨ β₁ ⟩ᴴ μ₂ → μ₂ ≈⟨ β₂ ⟩ᴴ μ₃ → μ₁ ≈⟨ β₂ ∘ β₁  ⟩ᴴ μ₃
  trans-≈ᴴ {β₁ = β₁} {β₂} ≈₁ ≈₂ x with  split-∈ᵗ {β₁ = β₁} {β₂} x
  ... | (b , ab∈ , bc∈) = trans-≅ⱽ (≈₁ ab∈) (≈₂ bc∈)

  -- Notice that this is not strictly an equivalence because we must be able to choose the
  -- identity bijection for refl.

  refl-≈ᴴ′ : ∀ {μ} → μ ≈ᴴ μ
  refl-≈ᴴ′ = ι , refl-≈ᴴ

  sym-≈ᴴ′ : ∀ {μ₁ μ₂} → μ₁ ≈ᴴ μ₂ → μ₂ ≈ᴴ μ₁
  sym-≈ᴴ′ (β , ≈ᴴ) = β ⁻¹ , sym-≈ᴴ {β = β} ≈ᴴ

  trans-≈ᴴ′ : ∀ {μ₁ μ₂ μ₃} → μ₁ ≈ᴴ μ₂ → μ₂ ≈ᴴ μ₃ → μ₁ ≈ᴴ μ₃
  trans-≈ᴴ′ (β₁ , ≈₁) (β₂ , ≈₂) = (β₂ ∘ β₁) , trans-≈ᴴ {β₁ = β₁} {β₂} ≈₁ ≈₂

open import Data.Nat
open import Data.Unit
open import Generic.Heap.Lemmas 𝑯
open import Relation.Binary.HeterogeneousEquality

-- Maybe move to Heap.Lemmas

-- Snoc and reduce commute
snoc-reduce-≡ : ∀ {τ'} (μ : Heap) →
        let n = ∥ μ ∥ᴴ in (x : Fin (suc n)) (v₂ : LValue τ') (x<n : (toℕ x) < n) →
        let (τ , v₁ , _) = (snocᴴ μ v₂) [ x ]ᴴ
            (τ' , v₁′ , _) = μ [ reduce₁ x x<n ]ᴴ in τ ≡ τ' × v₁ ≅ v₁′
snoc-reduce-≡ [] zero v₂ ()
snoc-reduce-≡ (x ∷ μ) zero v₂ (s≤s x<n) = refl , refl
snoc-reduce-≡ [] (suc x) v₂ ()
snoc-reduce-≡ (_ ∷ μ) (suc x) v₂ (s≤s x<n) = snoc-reduce-≡ μ x v₂ x<n

-- Add smth secret, remain related
new-≈ᴴ : ∀ {μ₁ μ₂} {β : Bij⟨ μ₁ , μ₂ ⟩} {τ} →
         μ₁ ≈⟨ β ⟩ᴴ μ₂ → (v : LValue τ) →
         μ₁ ≈⟨ β ↑ᴿ ⟩ᴴ (snocᴴ μ₂ v)
new-≈ᴴ {μ₂ = μ₂} {β = β} ≈ v {x} {y} xy∈βᴿ with ↑ᴿ-∈ {β = β} xy∈βᴿ
... | y<m , xy∈β with ≈ xy∈β
... | ≈ⱽ with μ₂ [ reduce₁ y y<m ]ᴴ | snoc-reduce-≡ μ₂ y v y<m
new-≈ᴴ {μ₂ = μ₂} {β} ≈ v {x} {y} xy∈βᴿ | y<m , xy∈β | ≈ⱽ | _ , ._ , ∈₁ | refl , refl = ≈ⱽ
