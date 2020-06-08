-- Generic pointwise L-equivalence for stores and memories and their
-- properties.
{-# OPTIONS --allow-unsolved-metas #-}

open import Lattice
open import Relation.Binary
open import Generic.Bijection hiding (_↦_)

module Generic.Store.LowEq
  {Ty : Set}
  {Value : Ty → Set}
  {{𝑳 : Lattice}}
  (_≈⟨_⟩ⱽ_ : IProps.Relᴮ Ty Value)
  (A : Label) where

open import Generic.Store.Base Ty Value as S
-- open import Generic.Memory.LowEq {Ty} {Value} _≈ⱽ_ A as M using (_≈⟨_⟩ᴹ_ ; _≈⟨_,_⟩ᴹ_ ; ⌞_⌟ᴹ) public

open IProps Ty Value
open import Data.Product as P

data _≈⟨_⟩ᶜ_ : ∀ {τ s} → Cell τ s → Bij → Cell τ s → Set where
  ⌞_⌟ᴵ : ∀ {τ β} → {v v' : Value τ} → v ≈⟨ β ⟩ⱽ v' → ⌞ v ⌟ᴵ ≈⟨ β ⟩ᶜ ⌞ v' ⌟ᴵ
  -- Not sure if I should make a distinction for ℓ ⋤ A ?
  -- Probably no because when we read them, we get tainted with ℓ.
  ⌞_⌟ˢ : ∀ {ℓ τ β} → {v v' : Value τ} → v ≈⟨ β ⟩ⱽ v' → ⌞ v , ℓ ⌟ˢ ≈⟨ β ⟩ᶜ ⌞ v' , ℓ ⌟ˢ


-- Cells
data _≅⟨_⟩ᶜ_ {τ s} (c : Cell τ s) (β : Bij) : ∀ {τ' s'} → Cell τ' s' → Set where
  ⌞_⌟ : ∀ {c' : Cell τ s} → c ≈⟨ β ⟩ᶜ c' → c ≅⟨ β ⟩ᶜ c'

open import Data.Empty
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

--------------------------------------------------------------------------------

open import Data.Product
open import Data.Fin hiding (_<_ ; _≤_)
open import Data.Nat renaming (_⊔_ to _⊔ᴺ_)
open import Data.Nat.Properties
open import Data.Maybe
-- open import Generic.Heap.Base 𝑯 as H

--open import Relation.Binary.PropositionalEquality as P

-- Domain inclusion between bijection and heap
_⊆ᴰ_ : Bij → Store → Set
β ⊆ᴰ Σ = ∀ {n : ℕ} → n ∈ᴰ β → n S.∈ Σ

_⊆ᴿ_ : Bij → Store → Set
β ⊆ᴿ Σ = ∀ {n : ℕ} → n ∈ᴿ β → n S.∈ Σ

⊆ᴰ-⊆ᴿ : ∀ {β Σ} → β ⊆ᴰ Σ → (β ⁻¹) ⊆ᴿ Σ
⊆ᴰ-⊆ᴿ {β} ⊆ (n , x) = ⊆ (n , left-inverse-of x)
  where open Bijectionᴾ β

⊆ᴿ-⊆ᴰ : ∀ {β Σ} → β ⊆ᴿ Σ → (β ⁻¹) ⊆ᴰ Σ
⊆ᴿ-⊆ᴰ {β} ⊆ (n , x) = ⊆ (n , left-inverse-of x)
  where open Bijectionᴾ β

-- Homogeneous L-equivalence.
-- TODO: do we ever use this?
Lift-≈ : Store → Store → Bij → Set
Lift-≈ Σ₁ Σ₂ β =
  ∀ {n₁ n₂ s τ} {c₁ c₂ : Cell s τ} →
    (n₁ , n₂) ∈ᵗ β →
    n₁ ↦ c₁ ∈ Σ₁ → n₂ ↦ c₂ ∈ Σ₂ →
    c₁ ≈⟨ β ⟩ᶜ c₂

-- For proving properties (cf. transitivity) *heterogeneous* L-equivalence
-- is more convenient.
Lift-≅ : Store → Store → Bij → Set
Lift-≅ Σ₁ Σ₂ β =
  ∀ {n₁ n₂ τ₁ τ₂ s₁ s₂} {c₁ : Cell τ₁ s₁} {c₂ : Cell τ₂ s₂} →
    (n₁ , n₂) ∈ᵗ β →
     n₁ ↦ c₁ ∈ Σ₁ → n₂ ↦ c₂ ∈ Σ₂ →
     c₁ ≅⟨ β ⟩ᶜ c₂
  -- where open import Generic.Value.HLowEq {Ty} {Value} _≈⟨_⟩ⱽ_

-- -- TODO: update
-- -- Two heaps are A-equivalent up to bijection β iff the low addresses
-- -- related by the bijection correspond to related values in the
-- -- respective heaps. Since the domain and the range of the bijection
-- -- is indexed with the size of the (low parts of) heaps, the lookups
-- -- are safe.  To index the bijection correctly, the relation must
-- -- first introduce the heaps and then the bijection. The following
-- -- definition defines the usual infix operator as syntatic sugar.

-- Definition inspired by "Stack-based Access Control and Secure
-- Information Flow" by Banerjee and Naumann.
record _≈⟨_⟩ˢ_ (Σ₁ : Store) (β : Bij) (Σ₂ : Store) : Set where

  field dom-⊆ : β ⊆ᴰ Σ₁
        rng-⊆ : β ⊆ᴿ Σ₂
        lift-≅ : Lift-≅ Σ₁ Σ₂ β

  -- Homogeneous (same type) lifting is implied by the heterogenous lifting.
  lift-≈ : Lift-≈ Σ₁ Σ₂ β
  lift-≈ x ∈₁ ∈₂ with lift-≅ x ∈₁ ∈₂
  lift-≈ x ∈₁ ∈₂ | ⌞ ≈ⱽ ⌟ = ≈ⱽ

-- -- _≈ˢ_ : Store → Store → Set
-- -- Σ₁ ≈ˢ Σ₂ = Σ Bij⟨ Σ₁ , Σ₂ ⟩ (λ β → Σ₁ ≈⟨ β ⟩ˢ Σ₂)

module Props (𝑽 : IsEquivalenceᴮ _≈⟨_⟩ⱽ_ ) where

  open import Generic.LValue Ty Value
  -- open L.HasLabel 𝑯
  -- open import Generic.Value.HLowEq {Ty} {Value} _≈⟨_⟩ⱽ_
  -- open import Generic.Store.Lemmas 𝑯
  -- open Props 𝑽
  open import Relation.Binary.PropositionalEquality
  import Function as F

  open IsEquivalenceᴮ 𝑽 renaming
    ( Dom to ∣_∣ⱽ
    ; reflᴮ to refl-≈ⱽ
    ; symᴮ to sym-≈ⱽ
    ; transᴮ to trans-≈ⱽ
    ; wkenᴮ to wken-≈ⱽ) public

  ∣_∣ᶜ : ∀ {s τ} → Cell s τ → ℕ
  ∣ ⌞ v ⌟ᴵ ∣ᶜ = ∣ v ∣ⱽ
  ∣ ⌞ v , ℓ ⌟ˢ ∣ᶜ = ∣ v ∣ⱽ


  refl-≈ᶜ : ∀ {s τ} {c : Cell τ s} → c ≈⟨ ι ∣ c ∣ᶜ ⟩ᶜ c
  refl-≈ᶜ {c = ⌞ ≈ⱽ ⌟ᴵ} = ⌞ refl-≈ⱽ ⌟ᴵ
  refl-≈ᶜ {c = ⌞ ≈ⱽ ⌟ˢ} = ⌞ refl-≈ⱽ ⌟ˢ

  wken-≈ᶜ : ∀ {s τ n m} {c : Cell τ s} → n ≤ m → c ≈⟨ ι n ⟩ᶜ c → c ≈⟨ ι m ⟩ᶜ c
  wken-≈ᶜ n≤m ⌞ ≈ⱽ ⌟ᴵ = ⌞ wken-≈ⱽ n≤m ≈ⱽ ⌟ᴵ
  wken-≈ᶜ n≤m ⌞ ≈ⱽ ⌟ˢ = ⌞ wken-≈ⱽ n≤m ≈ⱽ ⌟ˢ

  sym-≈ᶜ : ∀ {τ s β} {c₁ c₂ : Cell τ s} → c₁ ≈⟨ β ⟩ᶜ c₂ → c₂ ≈⟨ β ⁻¹ ⟩ᶜ c₁
  sym-≈ᶜ ⌞ ≈ⱽ ⌟ᴵ = ⌞ sym-≈ⱽ ≈ⱽ ⌟ᴵ
  sym-≈ᶜ ⌞ ≈ⱽ ⌟ˢ = ⌞ sym-≈ⱽ ≈ⱽ ⌟ˢ

  trans-≈ᶜ : ∀ {τ s β₁ β₂} {c₁ c₂ c₃ : Cell τ s} →
               c₁ ≈⟨ β₁ ⟩ᶜ c₂ →
               c₂ ≈⟨ β₂ ⟩ᶜ c₃ →
               c₁ ≈⟨ β₂ ∘ β₁ ⟩ᶜ c₃
  trans-≈ᶜ ⌞ ≈₁ ⌟ᴵ ⌞ ≈₂ ⌟ᴵ = ⌞ trans-≈ⱽ ≈₁ ≈₂ ⌟ᴵ
  trans-≈ᶜ ⌞ ≈₁ ⌟ˢ ⌞ ≈₂ ⌟ˢ = ⌞ trans-≈ⱽ ≈₁ ≈₂ ⌟ˢ

  sym-≅ᶜ : ∀ {τ₁ τ₂ s₁ s₂ β} {c₁ : Cell τ₁ s₁} {c₂ : Cell τ₂ s₂} →
             c₁ ≅⟨ β ⟩ᶜ c₂ → c₂ ≅⟨ β ⁻¹ ⟩ᶜ c₁
  sym-≅ᶜ ⌞ ≈ᶜ ⌟ = ⌞ sym-≈ᶜ ≈ᶜ ⌟

  trans-≅ᶜ : ∀ {β₁ β₂ τ₁ τ₂ τ₃ s₁ s₂ s₃} {c₁ : Cell τ₁ s₁}
               {c₂ : Cell τ₂ s₂} {c₃ : Cell τ₃ s₃} →
               c₁ ≅⟨ β₁ ⟩ᶜ c₂ →
               c₂ ≅⟨ β₂ ⟩ᶜ c₃ →
               c₁ ≅⟨ β₂ ∘ β₁ ⟩ᶜ c₃
  trans-≅ᶜ ⌞ ≈₁ ⌟ ⌞ ≈₂ ⌟ = ⌞ trans-≈ᶜ ≈₁ ≈₂ ⌟

  ∣_∣ˢ : Store → ℕ
  -- ∣ [] ∣ˢ = 0
  -- ∣ c ∷ Σ ∣ˢ = ∣ c ∣ᶜ ⊔ᴺ ∣ Σ ∣ˢ
  ∣_∣ˢ = ∥_∥

  -- A cell is valid for a store if the domain of its content points
  -- inside the store.
  Validᶜ : ∀ {s τ} → Cell s τ → Store → Set
  Validᶜ c Σ = ∣ c ∣ᶜ ≤ ∥ Σ ∥

  Validˢ : Store → Set
  Validˢ Σ = ∀ {τ s n} {c : Cell τ s} → n ↦ c ∈ Σ → Validᶜ c Σ

  -- For heterogeneous values.
  inj-∈′ : ∀ {n τ₁ τ₂ s₁ s₂} {Σ : Store} {c₁ : Cell τ₁ s₁} {c₂ : Cell τ₂ s₂} →
          n ↦ c₁ ∈ Σ → n ↦ c₂ ∈ Σ → P.Σ (τ₁ ≡ τ₂ × s₁ ≡ s₂) (λ {(refl , refl) → c₁ ≡ c₂})
  inj-∈′ Here Here = (refl , refl) , refl
  inj-∈′ (There x) (There y) with inj-∈′ x y
  ... | (refl , refl) , refl = (refl , refl) , refl

  -- TODO: haven't we proced this already somewhere?
  inj-∈ : ∀ {n τ s} {Σ : Store} {c₁ c₂ : Cell τ s} →
          n ↦ c₁ ∈ Σ → n ↦ c₂ ∈ Σ → c₁ ≡ c₂
  inj-∈ x y with inj-∈′ x y
  ... | (refl , refl) , eq = eq


  refl-≈ˢ : ∀ {Σ} {{validˢ : Validˢ Σ}} → Σ ≈⟨ ι ∣ Σ ∣ˢ ⟩ˢ Σ
  refl-≈ˢ {Σ} {{validˢ}} =
    record { dom-⊆ = dom-⊆
           ; rng-⊆ = rng-⊆
           ; lift-≅ = lift-≅ }
    where
          open Id ∣ Σ ∣ˢ
          dom-⊆ : ι ∣ Σ ∣ˢ ⊆ᴰ Σ
          dom-⊆ (n , ∈ᴮ) with lemma ∈ᴮ
          ... | refl , n< = <-∈ n<

          rng-⊆ : ι ∣ Σ ∣ˢ ⊆ᴿ Σ
          rng-⊆ (n , ∈ᴮ) with lemma ∈ᴮ
          ... | refl , n< = <-∈ n<

          -- Here I need to know that references in the heap are valid
          -- (point to the heap) to prove that they are related by the
          -- finite identity bijection of size ∣ Σ ∣ˢ.  Intuitively if
          -- Σ = [ 0 ↦ Refˢ L 1 ] I cannot prove that Σ ≈⟨ ι 1 ⟩ Σ,
          -- because Refˢ L 1 ≈⟨ ι 1 ⟩ Refˢ L 1, because ι 1 = 0 ↔ 0,
          -- i.e., 1 is not defined in the bijection.
          -- Why ... it seems that this definition works ...
          lift-≅ : Lift-≅ Σ Σ (ι ∣ Σ ∣ˢ)
          lift-≅ {_} {_} {τ₁} {τ₂} {v₁} {v₂} x ∈₁ ∈₂ rewrite idᴾ-≡ x with inj-∈′ ∈₁ ∈₂
          ... | (refl , refl) , refl = ⌞ wken-≈ᶜ (validˢ ∈₁) refl-≈ᶜ ⌟

  sym-≈ˢ : ∀ {β Σ₁ Σ₂} → Σ₁ ≈⟨ β ⟩ˢ Σ₂ → Σ₂ ≈⟨ β ⁻¹ ⟩ˢ Σ₁
  sym-≈ˢ {β} {Σ₁} {Σ₂} ≈ =
    record { dom-⊆ = ⊆ᴿ-⊆ᴰ {β} rng-⊆
           ; rng-⊆ = ⊆ᴰ-⊆ᴿ {β} dom-⊆
           ; lift-≅ = λ ∈ᴮ ∈₁ ∈₂ → sym-≅ᶜ (lift-≅ (right-inverse-of ∈ᴮ) ∈₂ ∈₁)
           }
    where open _≈⟨_⟩ˢ_ ≈
          open Bijectionᴾ (β ⁻¹)


  trans-≈ˢ : ∀ {Σ₁ Σ₂ Σ₃} {β₁ β₂} →
               Σ₁ ≈⟨ β₁ ⟩ˢ Σ₂ →
               Σ₂ ≈⟨ β₂ ⟩ˢ Σ₃ →
               Σ₁ ≈⟨ β₂ ∘ β₁  ⟩ˢ Σ₃
  trans-≈ˢ {Σ₁} {Σ₂} {Σ₃} {β₁ = β₁} {β₂} ≈₁ ≈₂ =
    record { dom-⊆ = dom-⊆ᴰ
           ; rng-⊆ = rng-⊆ᴿ
           ; lift-≅ = lift-≅′ }
    where open _≈⟨_⟩ˢ_

          dom-⊆ᴰ : (β₂ ∘ β₁) ⊆ᴰ Σ₁
          dom-⊆ᴰ (n , ∈ᴮ) with split-∈ᵗ {β₁ = β₁} {β₂} ∈ᴮ
          ... | (b , ab∈ , bc∈) = dom-⊆ ≈₁ (b , ab∈)

          rng-⊆ᴿ : (β₂ ∘ β₁) ⊆ᴿ Σ₃
          rng-⊆ᴿ (n , ∈ᴮ) with split-∈ᵗ {β₁ = β₁} {β₂} ∈ᴮ
          ... | (b , ab∈ , bc∈) = rng-⊆ ≈₂ (b , bc∈) -- rng-⊆ ≈₁ (b , bc∈)

          lift-≅′ : Lift-≅ Σ₁ Σ₃ (β₂ ∘ β₁)
          lift-≅′ {a} {c} {τ} {v₁} {v₃} ∈ᴮ ∈₁ ∈₃ with split-∈ᵗ {β₁ = β₁} {β₂} ∈ᴮ
          ... | (b , ab∈ , bc∈) with rng-⊆ ≈₁ (_ , ab∈) | dom-⊆ ≈₂ (_ , bc∈)
          ... | τ₂ , s₂ , c₂ , ∈₂ | τ₂' , s₂' , c₂' , ∈₂' with inj-∈′ ∈₂ ∈₂'
          ... | (refl , refl) , refl = trans-≅ᶜ (lift-≅ ≈₁ ab∈ ∈₁ ∈₂) (lift-≅ ≈₂ bc∈ ∈₂' ∈₃)

--------------------------------------------------------------------------------

-- TODO: remove

-- open import Data.Nat
-- open import Data.Unit
-- open import Generic.Store.Lemmas 𝑯
-- open import Relation.Binary.HeterogeneousEquality

-- -- Maybe move to Store.Lemmas

-- -- Snoc and reduce commute
-- -- snoc-reduce-≡ : ∀ {τ'} (Σ : Store) →
-- --         let n = ∣ Σ ∣ˢ in (x : Fin (suc n)) (v₂ : LValue τ') (x<n : (toℕ x) < n) →
-- --         let (τ , v₁ , _) = (snocˢ Σ v₂) [ x ]ˢ
-- --             (τ' , v₁′ , _) = Σ [ reduce₁ x x<n ]ˢ in τ ≡ τ' × v₁ ≅ v₁′
-- -- snoc-reduce-≡ [] zero v₂ ()
-- -- snoc-reduce-≡ (x ∷ Σ) zero v₂ (s≤s x<n) = refl , refl
-- -- snoc-reduce-≡ [] (suc x) v₂ ()
-- -- snoc-reduce-≡ (_ ∷ Σ) (suc x) v₂ (s≤s x<n) = snoc-reduce-≡ Σ x v₂ x<n

-- -- Add smth secret, remain related
-- -- new-≈ˢ : ∀ {Σ₁ Σ₂} {β : Bij⟨ Σ₁ , Σ₂ ⟩} {τ} →
-- --          Σ₁ ≈⟨ β ⟩ˢ Σ₂ → (v : LValue τ) →
-- --          Σ₁ ≈⟨ β ↑ᴿ ⟩ˢ (snocˢ Σ₂ v)
-- -- new-≈ˢ {Σ₂ = Σ₂} {β = β} ≈ v {x} {y} xy∈βᴿ with ↑ᴿ-∈ {β = β} xy∈βᴿ
-- -- ... | y<m , xy∈β with ≈ xy∈β
-- -- ... | ≈ⱽ with Σ₂ [ reduce₁ y y<m ]ˢ | snoc-reduce-≡ Σ₂ y v y<m
-- -- new-≈ˢ {Σ₂ = Σ₂} {β} ≈ v {x} {y} xy∈βᴿ | y<m , xy∈β | ≈ⱽ | _ , ._ , ∈₁ | refl , refl = ≈ⱽ
