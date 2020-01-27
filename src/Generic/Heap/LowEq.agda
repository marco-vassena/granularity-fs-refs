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
open import Data.Fin hiding (_<_ ; _≤_)
open import Data.Nat
open import Data.Maybe
open import Generic.Bijection
open import Generic.Heap.Base 𝑯 as H

open import Relation.Binary.PropositionalEquality as P

-- Domain inclusion between bijection and heap
_⊆ᴰ_ : Bij → Heap → Set
β ⊆ᴰ μ = ∀ {n : ℕ} → n ∈ᴰ β → n H.∈ μ

_⊆ᴿ_ : Bij → Heap → Set
β ⊆ᴿ μ = ∀ {n : ℕ} → n ∈ᴿ β → n H.∈ μ

⊆ᴰ-⊆ᴿ : ∀ {β μ} → β ⊆ᴰ μ → (β ⁻¹) ⊆ᴿ μ
⊆ᴰ-⊆ᴿ {β} ⊆ (n , x) = ⊆ (n , left-inverse-of x)
  where open Bijectionᴾ β

⊆ᴿ-⊆ᴰ : ∀ {β μ} → β ⊆ᴿ μ → (β ⁻¹) ⊆ᴰ μ
⊆ᴿ-⊆ᴰ {β} ⊆ (n , x) = ⊆ (n , left-inverse-of x)
  where open Bijectionᴾ β


Lift-≈ : Heap → Heap → Bij → Set
Lift-≈ μ₁ μ₂ β =  ∀ {n₁ n₂ τ} {v₁ v₂ : LValue τ} → (n₁ , n₂) ∈ᵗ β →
            n₁ ↦ v₁ ∈ᴴ μ₁ → n₂ ↦ v₂ ∈ᴴ μ₂ →
            v₁ ≈ⱽ v₂

-- For proving properties (cf. transitivity) heterogeneous L-equivalence
-- is more convenient.
Lift-≅ : Heap → Heap → Bij → Set
Lift-≅ μ₁ μ₂ β =  ∀ {n₁ n₂ τ₁ τ₂} {v₁ : LValue τ₁} {v₂ : LValue τ₂} →
           (n₁ , n₂) ∈ᵗ β →
            n₁ ↦ v₁ ∈ᴴ μ₁ → n₂ ↦ v₂ ∈ᴴ μ₂ →
            v₁ ≅ⱽ v₂
  where open import Generic.Value.HLowEq {Ty} {Value} _≈ⱽ_

-- TODO: update
-- Two heaps are A-equivalent up to bijection β iff the low addresses
-- related by the bijection correspond to related values in the
-- respective heaps. Since the domain and the range of the bijection
-- is indexed with the size of the (low parts of) heaps, the lookups
-- are safe.  To index the bijection correctly, the relation must
-- first introduce the heaps and then the bijection. The following
-- definition defines the usual infix operator as syntatic sugar.

-- Definition inspired by "Stack-based Access Control and Secure
-- Information Flow" by Banerjee and Naumann.
record _≈⟨_⟩ᴴ_ (μ₁ : Heap) (β : Bij) (μ₂ : Heap) : Set where

  field dom-⊆ : β ⊆ᴰ μ₁
        rng-⊆ : β ⊆ᴿ μ₂
        lift-≅ : Lift-≅ μ₁ μ₂ β

  open import Generic.Value.HLowEq {Ty} {Value} _≈ⱽ_

  -- Homogeneous (same type) lifting is implied by the heterogenous lifting.
  lift-≈ : Lift-≈ μ₁ μ₂ β
  lift-≈ x ∈₁ ∈₂ with lift-≅ x ∈₁ ∈₂
  lift-≈ x ∈₁ ∈₂ | ⌞ ≈ⱽ ⌟ = ≈ⱽ

-- _≈ᴴ_ : Heap → Heap → Set
-- μ₁ ≈ᴴ μ₂ = Σ Bij⟨ μ₁ , μ₂ ⟩ (λ β → μ₁ ≈⟨ β ⟩ᴴ μ₂)

module Props (𝑽 : ∀ {τ} → IsEquivalence (_≈ⱽ_ {τ})) where

  open import Data.Unit
  open import Generic.LValue Ty Value
  open L.HasLabel 𝑯
  open import Generic.Value.HLowEq {Ty} {Value} _≈ⱽ_
  open import Generic.Heap.Lemmas 𝑯
  open Props 𝑽
  open import Relation.Binary.PropositionalEquality
  import Function as F

  refl-≈ᴴ : ∀ {μ} → μ ≈⟨ ι ∥ μ ∥ᴴ ⟩ᴴ μ
  refl-≈ᴴ {μ} =
    record { dom-⊆ = dom-⊆
           ; rng-⊆ = rng-⊆
           ; lift-≅ = lift-≅ }
    where
          open Id ∥ μ ∥ᴴ
          dom-⊆ : ι ∥ μ ∥ᴴ ⊆ᴰ μ
          dom-⊆ (n , ∈ᴮ) with lemma ∈ᴮ
          ... | refl , n< = <-∈ n<

          rng-⊆ : ι ∥ μ ∥ᴴ ⊆ᴿ μ
          rng-⊆ (n , ∈ᴮ) with lemma ∈ᴮ
          ... | refl , n< = <-∈ n<

          lift-≅ : Lift-≅ μ μ (ι ∥ μ ∥ᴴ)
          lift-≅ x ∈₁ ∈₂ rewrite idᴾ-≡ x with inj-∈′ ∈₁ ∈₂
          ... | refl , refl = refl-≅ⱽ


  sym-≈ᴴ : ∀ {β μ₁ μ₂} → μ₁ ≈⟨ β ⟩ᴴ μ₂ → μ₂ ≈⟨ β ⁻¹ ⟩ᴴ μ₁
  sym-≈ᴴ {β} {μ₁} {μ₂} ≈ =
    record { dom-⊆ = ⊆ᴿ-⊆ᴰ {β} rng-⊆
           ; rng-⊆ = ⊆ᴰ-⊆ᴿ {β} dom-⊆
           ; lift-≅ = λ ∈ᴮ ∈₁ ∈₂ → sym-≅ⱽ (lift-≅ (right-inverse-of ∈ᴮ) ∈₂ ∈₁) }
    where open _≈⟨_⟩ᴴ_ ≈
          open Bijectionᴾ (β ⁻¹)


  trans-≈ᴴ : ∀ {μ₁ μ₂ μ₃} {β₁ β₂} →
               μ₁ ≈⟨ β₁ ⟩ᴴ μ₂ →
               μ₂ ≈⟨ β₂ ⟩ᴴ μ₃ →
               μ₁ ≈⟨ β₂ ∘ β₁  ⟩ᴴ μ₃
  trans-≈ᴴ {μ₁} {μ₂} {μ₃} {β₁ = β₁} {β₂} ≈₁ ≈₂ =
    record { dom-⊆ = dom-⊆ᴰ
           ; rng-⊆ = rng-⊆ᴿ
           ; lift-≅ = lift-≅′ }
    where open _≈⟨_⟩ᴴ_

          dom-⊆ᴰ : (β₂ ∘ β₁) ⊆ᴰ μ₁
          dom-⊆ᴰ (n , ∈ᴮ) with split-∈ᵗ {β₁ = β₁} {β₂} ∈ᴮ
          ... | (b , ab∈ , bc∈) = dom-⊆ ≈₁ (b , ab∈)

          rng-⊆ᴿ : (β₂ ∘ β₁) ⊆ᴿ μ₃
          rng-⊆ᴿ (n , ∈ᴮ) with split-∈ᵗ {β₁ = β₁} {β₂} ∈ᴮ
          ... | (b , ab∈ , bc∈) = rng-⊆ ≈₂ (b , bc∈) -- rng-⊆ ≈₁ (b , bc∈)

          lift-≅′ : Lift-≅ μ₁ μ₃ (β₂ ∘ β₁)
          lift-≅′ {a} {c} {τ} {v₁} {v₃} ∈ᴮ ∈₁ ∈₃ with split-∈ᵗ {β₁ = β₁} {β₂} ∈ᴮ
          ... | (b , ab∈ , bc∈) with rng-⊆ ≈₁ (_ , ab∈) | dom-⊆ ≈₂ (_ , bc∈)
          ... | τ₂ , v₂ , ∈₂ | τ₂' , v₂' , ∈₂' with inj-∈′ ∈₂ ∈₂'
          ... | refl , refl = trans-≅ⱽ (lift-≅ ≈₁ ab∈ ∈₁ ∈₂) (lift-≅ ≈₂ bc∈ ∈₂' ∈₃)


-- open import Data.Nat
-- open import Data.Unit
-- open import Generic.Heap.Lemmas 𝑯
-- open import Relation.Binary.HeterogeneousEquality

-- -- Maybe move to Heap.Lemmas

-- -- Snoc and reduce commute
-- -- snoc-reduce-≡ : ∀ {τ'} (μ : Heap) →
-- --         let n = ∥ μ ∥ᴴ in (x : Fin (suc n)) (v₂ : LValue τ') (x<n : (toℕ x) < n) →
-- --         let (τ , v₁ , _) = (snocᴴ μ v₂) [ x ]ᴴ
-- --             (τ' , v₁′ , _) = μ [ reduce₁ x x<n ]ᴴ in τ ≡ τ' × v₁ ≅ v₁′
-- -- snoc-reduce-≡ [] zero v₂ ()
-- -- snoc-reduce-≡ (x ∷ μ) zero v₂ (s≤s x<n) = refl , refl
-- -- snoc-reduce-≡ [] (suc x) v₂ ()
-- -- snoc-reduce-≡ (_ ∷ μ) (suc x) v₂ (s≤s x<n) = snoc-reduce-≡ μ x v₂ x<n

-- -- Add smth secret, remain related
-- -- new-≈ᴴ : ∀ {μ₁ μ₂} {β : Bij⟨ μ₁ , μ₂ ⟩} {τ} →
-- --          μ₁ ≈⟨ β ⟩ᴴ μ₂ → (v : LValue τ) →
-- --          μ₁ ≈⟨ β ↑ᴿ ⟩ᴴ (snocᴴ μ₂ v)
-- -- new-≈ᴴ {μ₂ = μ₂} {β = β} ≈ v {x} {y} xy∈βᴿ with ↑ᴿ-∈ {β = β} xy∈βᴿ
-- -- ... | y<m , xy∈β with ≈ xy∈β
-- -- ... | ≈ⱽ with μ₂ [ reduce₁ y y<m ]ᴴ | snoc-reduce-≡ μ₂ y v y<m
-- -- new-≈ᴴ {μ₂ = μ₂} {β} ≈ v {x} {y} xy∈βᴿ | y<m , xy∈β | ≈ⱽ | _ , ._ , ∈₁ | refl , refl = ≈ⱽ
