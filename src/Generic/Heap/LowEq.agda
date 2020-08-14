-- TODO: this module should be simplified and split in different modules

-- Generic pointwise L-equivalence for stores and memories and their
-- properties.

open import Lattice hiding (_≟_)
open import Relation.Binary
open import Generic.Bijection as B hiding (_↦_ ; _∈_ ; _⊆ᴰ_ ; _⊆ᴿ_)

module Generic.Heap.LowEq
  {Ty : Set}
  {Value : Ty → Set}
  {{𝑳 : Lattice}}
  (_≈⟨_⟩ⱽ_ : IProps.Relᴮ Ty Value)
  (A : Label) where

open import Generic.Heap.Base Ty Value

open IProps Ty Value
open import Generic.Value.HLowEq {Ty} {Value} _≈⟨_⟩ⱽ_
open import Data.Product as P

-- Here I  should make a distinction depending on the label of the cell.
-- All cells should have a label
-- data _≈⟨_⟩ᶜ_ : ∀ {τ} → Value τ → Bij → Value τ → Set where
--   -- ⌞_⌟ᴵ : ∀ {τ β} → {v v' : Value τ} → v ≈⟨ β ⟩ⱽ v' → ⌞ v ⌟ᴵ ≈⟨ β ⟩ᶜ ⌞ v' ⌟ᴵ
--   -- Not sure if I should make a distinction for ℓ ⋤ A ?
--   -- Probably no because when we read them, we get tainted with ℓ.
--   -- ⌞_⌟ᴴ : ∀ {ℓ τ β} → {v v' : Value τ} → v ≈⟨ β ⟩ⱽ v' → ⌞ v , ℓ ⌟ᴴ ≈⟨ β ⟩ᶜ ⌞ v' , ℓ ⌟ᴴ
--   -- TODO: here we need to remove the flow s
--   cellᴸ : ∀ {ℓ τ β} → {v v' : Value τ} → ℓ ⊑ A → v ≈⟨ β ⟩ⱽ v' → (v , ℓ) ≈⟨ β ⟩ᶜ (v' , ℓ)
--   cellᴴ : ∀ {ℓ ℓ' τ β} → {v v' : Value τ} → ℓ ⋤ A → ℓ' ⋤ A → (v , ℓ) ≈⟨ β ⟩ᶜ (v' , ℓ')

-- open import Relation.Nullary

-- -- TODO: move to Heap.LowEq
-- ≈ᶜ-⊑ :  ∀ {τ β} {v₁ v₂ : Value τ} (pc : Label) →
--                    let (v₁ , ℓ₁) = v₁
--                        (v₂ , ℓ₂) = v₂ in
--                        v₁ ≈⟨ β ⟩ᶜ v₂ → ( v₁ , (pc ⊔ ℓ₁) ) ≈⟨ β ⟩ᶜ ( v₂ , (pc ⊔ ℓ₂) )
-- ≈ᶜ-⊑ pc (cellᴸ {ℓ = ℓ} x x₁) with (pc ⊔ ℓ) ⊑? A
-- ... | yes p = cellᴸ p x₁
-- ... | no ¬p = cellᴴ ¬p ¬p
-- ≈ᶜ-⊑ pc (cellᴴ x x₁) = cellᴴ (trans-⋤ (join-⊑₂ _ _) x) (trans-⋤ (join-⊑₂ _ _) x₁)


-- -- Values
-- data _≅⟨_⟩ᶜ_ {τ} (c : Value τ) (β : Bij) : ∀ {τ'} → Value τ' → Set where
--   ⌞_⌟ : ∀ {c' : Value τ} → c ≈⟨ β ⟩ᶜ c' → c ≅⟨ β ⟩ᶜ c'

-- open import Data.Empty
-- open import Relation.Binary.PropositionalEquality

open import Data.Product
open import Data.Fin hiding (_<_ ; _≤_)
open import Data.Nat renaming (_⊔_ to _⊔ᴺ_)
open import Data.Nat.Properties
open import Data.Maybe
-- open import Generic.Heap.Base 𝑯 as H

--open import Relation.Binary.PropositionalEquality as P

-- Domain inclusion between bijection and heap
_⊆ᴰ_ : Bij → Heap → Set
β ⊆ᴰ μ = ∀ {n : ℕ} → n ∈ᴰ β → n ∈ᴴ μ

_⊆ᴿ_ : Bij → Heap → Set
β ⊆ᴿ μ = ∀ {n : ℕ} → n ∈ᴿ′ β → n ∈ᴴ μ

-- With the new definitions these seems not needed
-- ⊆ᴰ-⊆ᴿ : ∀ {β μ} → β ⊆ᴰ μ → (β ⁻¹) ⊆ᴿ μ
-- ⊆ᴰ-⊆ᴿ {β} ⊆ (n , x) = ⊆ (n , x)
-- --  where open Bijectionᴾ (β ⁻¹)

-- ⊆ᴿ-⊆ᴰ : ∀ {β μ} → β ⊆ᴿ μ → (β ⁻¹) ⊆ᴰ μ
-- ⊆ᴿ-⊆ᴰ {β} ⊆ (n , x) = {!!} -- ⊆ (n , left-inverse-of x)
--   where open Bijectionᴾ β

-- Homogeneous L-equivalence.
-- TODO: do we ever use this?
Lift-≈ : Heap → Heap → Bij → Set
Lift-≈ μ₁ μ₂ β =
  ∀ {n₁ n₂ τ} {v₁ v₂ : Value τ} →
    (n₁ , n₂) ∈ᵗ β →
    n₁ ↦ v₁ ∈ᴴ μ₁ → n₂ ↦ v₂ ∈ᴴ μ₂ →
    v₁ ≈⟨ β ⟩ⱽ v₂

-- For proving properties (cf. transitivity) *heterogeneous* L-equivalence
-- is more convenient.
Lift-≅ : Heap → Heap → Bij → Set
Lift-≅ μ₁ μ₂ β =
  ∀ {n₁ n₂ τ₁ τ₂} {v₁ : Value τ₁} {v₂ : Value τ₂} →
    (n₁ , n₂) ∈ᵗ β →
     n₁ ↦ v₁ ∈ᴴ μ₁ → n₂ ↦ v₂ ∈ᴴ μ₂ →
     v₁ ≅⟨ β ⟩ⱽ v₂
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
record _≈⟨_⟩ᴴ_ (μ₁ : Heap) (β : Bij) (μ₂ : Heap) : Set where

  field dom-⊆ : β ⊆ᴰ μ₁
        rng-⊆ : β ⊆ᴿ μ₂
        lift-≅ : Lift-≅ μ₁ μ₂ β

  -- Homogeneous (same type) lifting is implied by the heterogenous lifting.
  lift-≈ : Lift-≈ μ₁ μ₂ β
  lift-≈ x ∈₁ ∈₂ with lift-≅ x ∈₁ ∈₂
  lift-≈ x ∈₁ ∈₂ | ⌞ ≈ⱽ ⌟ = ≈ⱽ

  -- open Bijectionᴾ β public

-- -- _≈ᴴ_ : Heap → Heap → Set
-- -- μ₁ ≈ᴴ μ₂ = μ Bij⟨ μ₁ , μ₂ ⟩ (λ β → μ₁ ≈⟨ β ⟩ᴴ μ₂)

module ≈ᴴ-Props (𝑽 : IsEquivalenceᴮ _≈⟨_⟩ⱽ_ ) where

  open import Generic.LValue Ty Value
  -- open L.HasLabel 𝑯
  -- open import Generic.Value.HLowEq {Ty} {Value} _≈⟨_⟩ⱽ_
  -- open import Generic.Heap.Lemmas 𝑯
  open Props 𝑽 -- Can we get this as a renaming as below?
  open import Relation.Binary.PropositionalEquality
  import Function as F

  open IsEquivalenceᴮ 𝑽 renaming
    ( Dom to ∣_∣ⱽ
    ; reflᴮ to refl-≈ⱽ
    ; symᴮ to sym-≈ⱽ
    ; transᴮ to trans-≈ⱽ
    ; wkenᴮ to wken-≈ⱽ)


  open import Generic.Heap.Valid Ty Value ∣_∣ⱽ -- renaming (∥_∥ᶜ to ∣_∣ᶜ)
  open import Generic.Heap.Lemmas Ty Value

  snoc-⊆ᴿ : ∀ {β μ τ} {v : Value τ} → β ⊆ᴿ μ → β ⊆ᴿ (snocᴴ μ v)
  snoc-⊆ᴿ ⊆₁ x = wken-∈′ (⊆₁ x)


  ∣_∣ᴴ : Heap → ℕ
  ∣_∣ᴴ = ∥_∥ᴴ

  -- A cell is valid for a store if the domain of its content points
  -- inside the store.
  -- Validᶜ : ∀ {s τ} → Value s τ → Heap → Set
  -- Validᶜ c μ = ∣ c ∣ᶜ ≤ ∥ μ ∥

  -- Validᴴ : Heap → Set
  -- Validᴴ μ = ∀ {τ s n} {c : Value τ s} → n ↦ c ∈ μ → Validᶜ c μ

  refl-⊆ᴰ : ∀ {μ} → ι ∣ μ ∣ᴴ ⊆ᴰ μ
  refl-⊆ᴰ {μ} (n , ∈ᴮ) with Id.lemma ∣ μ ∣ᴴ ∈ᴮ
  ... | refl , n< = <-∈ n<

  refl-≈ᴴ : ∀ {μ} {{validᴴ : Validᴴ μ}} → μ ≈⟨ ι ∣ μ ∣ᴴ ⟩ᴴ μ
  refl-≈ᴴ {μ} {{validᴴ}} =
    record { dom-⊆ = dom-⊆
           ; rng-⊆ = rng-⊆
           ; lift-≅ = lift-≅ }
    where
          -- Use Generic lemma
          open Id ∣ μ ∣ᴴ
          dom-⊆ : ι ∣ μ ∣ᴴ ⊆ᴰ μ
          dom-⊆ (n , ∈ᴮ) with lemma ∈ᴮ
          ... | refl , n< = <-∈ n<

          rng-⊆ : ι ∣ μ ∣ᴴ ⊆ᴿ μ
          rng-⊆ (n , ∈ᴮ) with lemma ∈ᴮ
          ... | refl , n< = <-∈ n<

          -- Here I need to know that references in the heap are valid
          -- (point to the heap) to prove that they are related by the
          -- finite identity bijection of size ∣ μ ∣ᴴ.  Intuitively if
          -- μ = [ 0 ↦ Refᴴ L 1 ] I cannot prove that μ ≈⟨ ι 1 ⟩ μ,
          -- because Refᴴ L 1 ≈⟨ ι 1 ⟩ Refᴴ L 1, because ι 1 = 0 ↔ 0,
          -- i.e., 1 is not defined in the bijection.
          -- Why ... it seems that this definition works ...
          lift-≅ : Lift-≅ μ μ (ι ∣ μ ∣ᴴ)
          lift-≅ {_} {_} {τ₁} {τ₂} {v₁} {v₂} x ∈₁ ∈₂ rewrite idᴾ-≡ x with inj-∈′ ∈₁ ∈₂
          ... | refl , refl = ⌞ (wken-≈ⱽ (ι-⊆ (validᴴ ∈₁)) refl-≈ⱽ) ⌟

  sym-≈ᴴ : ∀ {β μ₁ μ₂} → μ₁ ≈⟨ β ⟩ᴴ μ₂ → μ₂ ≈⟨ β ⁻¹ ⟩ᴴ μ₁
  sym-≈ᴴ {β} {μ₁} {μ₂} ≈ =
    record { dom-⊆ = rng-⊆
           ; rng-⊆ = dom-⊆
           ; lift-≅ = λ ∈ᴮ ∈₁ ∈₂ → sym-≅ⱽ (lift-≅ (left-inverse-of ∈ᴮ) ∈₂ ∈₁)
           }
    where open _≈⟨_⟩ᴴ_ ≈
          open Bijectionᴾ β

  trans-≈ᴴ : ∀ {μ₁ μ₂ μ₃} {β₁ β₂} →
               μ₁ ≈⟨ β₁ ⟩ᴴ μ₂ →
               μ₂ ≈⟨ β₂ ⟩ᴴ μ₃ →
               μ₁ ≈⟨ β₂ ∘ β₁ ⟩ᴴ μ₃
  trans-≈ᴴ {μ₁} {μ₂} {μ₃} {β₁ = β₁} {β₂} ≈₁ ≈₂ =
    record { dom-⊆ = dom-⊆ᴰ
           ; rng-⊆ = rng-⊆ᴿ
           ; lift-≅ = lift-≅′ }
    where open _≈⟨_⟩ᴴ_
          open Bijectionᴾ
          dom-⊆ᴰ : (β₂ ∘ β₁) ⊆ᴰ μ₁
          dom-⊆ᴰ (n , ∈ᴮ) with split-∈ᵗ {β₁ = β₁} {β₂} ∈ᴮ
          ... | (b , ab∈ , bc∈) = dom-⊆ ≈₁ (b , ab∈)

          rng-⊆ᴿ : (β₂ ∘ β₁) ⊆ᴿ μ₃
          rng-⊆ᴿ (n , eq ) with split-∈ᵗ {β₁ = β₁} {β₂} (left-inverse-of (β₂ ∘ β₁) eq)
          ... | (b , ab∈ , bc∈) = rng-⊆ ≈₂ (b , right-inverse-of β₂ bc∈)

          lift-≅′ : Lift-≅ μ₁ μ₃ (β₂ ∘ β₁)
          lift-≅′ {a} {c} {τ} {v₁} {v₃} ∈ᴮ ∈₁ ∈₃ with split-∈ᵗ {β₁ = β₁} {β₂} ∈ᴮ
          ... | (b , ab∈ , bc∈) with rng-⊆ ≈₁ (_ , right-inverse-of β₁ ab∈) | dom-⊆ ≈₂ (_ , bc∈)
          ... | τ₂ , v₂ , ∈₂ | τ₂' , v₂' , ∈₂' with inj-∈′ ∈₂ ∈₂'
          ... | refl , refl = trans-≅ⱽ (lift-≅ ≈₁ ab∈ ∈₁ ∈₂) (lift-≅ ≈₂ bc∈ ∈₂' ∈₃)

  -- This lemma constructs the double dashed (||) edged of the square
  -- by using symmetry and transitivity of L-equvialence. The
  -- bijection of this edge is obtained by composing the other
  -- bijection as the diagram below shows.
  --
  --        β₁
  --   μ₁ ------ μ₁'
  --   |         ||
  -- β |         || β' = β₂ ∘ β ∘ β₁⁻¹
  --   |         ||
  --   μ₂ ------ μ₂'
  --        β₂
  --
  square-≈ᴴ : ∀ {μ₁ μ₁' μ₂ μ₂' β β₁ β₂} →
                μ₁ ≈⟨ β ⟩ᴴ μ₂ →
                μ₁ ≈⟨ β₁ ⟩ᴴ μ₁' →
                μ₂ ≈⟨ β₂ ⟩ᴴ μ₂' →
                μ₁' ≈⟨ β₂ ∘ β ∘ (β₁ ⁻¹) ⟩ᴴ μ₂'
  square-≈ᴴ {β₁ = β₁} μ₁≈μ₂ μ₁≈μ₁' μ₂≈μ₂' =
    let μ₁'≈μ₁ = sym-≈ᴴ μ₁≈μ₁'
        μ₁'≈μ₂ = trans-≈ᴴ μ₁'≈μ₁ μ₁≈μ₂ in
        trans-≈ᴴ μ₁'≈μ₂ μ₂≈μ₂'

--------------------------------------------------------------------------------

  snoc-≈ᴴ : ∀ {β μ₁ μ₂ τ} (c : Value τ) → μ₁ ≈⟨ β ⟩ᴴ μ₂ → μ₁ ≈⟨ β ⟩ᴴ (snocᴴ μ₂ c)
  snoc-≈ᴴ {β} {μ₁} {μ₂} c ≈₁ =
    record { dom-⊆ = dom-⊆
           ; rng-⊆ = snoc-⊆ᴿ {β = β} rng-⊆
           ; lift-≅ = lift-≅′ }
    where open _≈⟨_⟩ᴴ_ ≈₁
          open Bijectionᴾ β
          lift-≅′ : Lift-≅ μ₁ (snocᴴ μ₂ c) β
          lift-≅′ x ∈₁ ∈₂ with rng-⊆ (_ , right-inverse-of x)
          ... | τ' , c' , ∈₂′ with inj-∈′ ∈₂ (wken-∈ ∈₂′)
          ... | refl , refl = lift-≅ x ∈₁ ∈₂′

  writeᴴ-≈ᴴ : ∀ {μ μ' n τ} {v v' : Value τ} {{validᴴ : Validᴴ μ}} →
              n ↦ v ∈ᴴ μ → μ' ≔ μ [ n ↦ v' ]ᴴ → v ≈⟨ ι ∥ μ ∥ᴴ ⟩ⱽ v' → -- Probably should be ≈
              μ ≈⟨ ι ∥ μ ∥ᴴ ⟩ᴴ μ'
  writeᴴ-≈ᴴ {μ} {μ'} {n} {{validᴴ}} n∈μ w ≈₁ =
    record { dom-⊆ = refl-⊆ᴰ ; rng-⊆ = rng-⊆ ; lift-≅ = lift-≅ }
    where
      open Id ∣ μ ∣ᴴ
      open import Relation.Nullary
      rng-⊆ : ι ∥ μ ∥ᴴ ⊆ᴿ μ'
      rng-⊆ (n , ∈ᴮ) with lemma ∈ᴮ
      ... | refl , n< with write-length-≡ w
      ... | eq = <-∈ (≤-trans n< (≤-reflexive (sym eq)))

      lift-≅ : Lift-≅ μ μ' (ι ∥ μ ∥ᴴ)
      lift-≅ {n₁} {n₂} ∈ᴮ ∈₁ ∈₂ with lemma ∈ᴮ
      ... | refl , _  with n ≟ n₁

       -- The written cell is secret
      lift-≅ {n₁} {.n₁} ∈ᴮ ∈₁ ∈₂ | refl , _ | yes refl with inj-∈′ ∈₁ n∈μ
      lift-≅ {n₁} {.n₁} ∈ᴮ ∈₁ ∈₂ | refl , _ | yes refl | refl , refl with inj-∈′ ∈₂ (write-∈ w)
      ... | refl , refl = ⌞ ≈₁ ⌟

      -- Identical cells are looked up, use reflexivity.
      lift-≅ {n₁} {.n₁} ∈ᴮ ∈₁ ∈₂ | refl , _ | no n₁≠n with write-only-one w n₁≠n ∈₁ ∈₂
      lift-≅ {n₁} {.n₁} ∈ᴮ ∈₁ ∈₂ | refl , _ | no n₁≠n | refl , refl = ⌞ (wken-≈ⱽ (ι-⊆ (validᴴ ∈₁)) refl-≈ⱽ) ⌟

  -- Low-equivalence over the identity bijection implies containment of stores
  ≈ᴴ-⊆ : ∀ {μ₁ μ₂} → μ₁ ≈⟨ ι ∥ μ₁ ∥ᴴ ⟩ᴴ μ₂ → μ₁ ⊆ᴴ μ₂
  ≈ᴴ-⊆ ≈₁ ∈₁ with ι-∈ (∈-< (lookup-∈ ∈₁))
  ... | ∈ι with _≈⟨_⟩ᴴ_.rng-⊆ ≈₁ (_ , ∈ι)
  ... | _ , _ , ∈₂ with _≈⟨_⟩ᴴ_.lift-≅ ≈₁ ∈ι ∈₁ ∈₂
  ... | ≅ⱽ with ≅ⱽ-type-≡ ≅ⱽ
  ... | refl = _ , ∈₂

  with-≡ : ∀ {μ μ' β β'} → μ ≈⟨ β ⟩ᴴ μ' → β ≡ β' → μ ≈⟨ β' ⟩ᴴ μ'
  with-≡ x eq rewrite eq = x

  trans-≈ᴴ-ι : ∀ {μ₁ μ₂ μ₃} → μ₁ ≈⟨ ι ∥ μ₁ ∥ᴴ ⟩ᴴ μ₂ → μ₂ ≈⟨ ι ∥ μ₂ ∥ᴴ ⟩ᴴ μ₃ → μ₁ ≈⟨ ι ∥ μ₁ ∥ᴴ ⟩ᴴ μ₃
  trans-≈ᴴ-ι {μ₁} {μ₂} {μ₃} ≈₁ ≈₂ = with-≡ (trans-≈ᴴ ≈₁ ≈₂) (absorb-ι (⊆-≤ (⊆-⊆′ ⊆₁)))
    where ⊆₁ = ≈ᴴ-⊆ ≈₁

  square-≈ᴴ-ι : ∀ {μ₁ μ₁' μ₂ μ₂' β} →
                μ₁ ≈⟨ β ⟩ᴴ μ₂ →
                μ₁ ≈⟨ ι ∣ μ₁ ∣ᴴ ⟩ᴴ μ₁' →
                μ₂ ≈⟨ ι ∣ μ₂ ∣ᴴ ⟩ᴴ μ₂' →
                μ₁' ≈⟨ β ⟩ᴴ μ₂'
  square-≈ᴴ-ι {μ₁} {μ₁'} {μ₂} {μ₂'} {β} μ₁≈μ₂ μ₁≈μ₁' μ₂≈μ₂' = μ₁'≈μ₂'
    where  open ≡-Reasoning
           open Bijectionᴾ β
           β' : Bij
           β' = ι ∣ μ₂ ∣ᴴ ∘ β ∘ (ι ∣ μ₁ ∣ᴴ) ⁻¹

           open _≈⟨_⟩ᴴ_  μ₁≈μ₂

           ⊆₂ : β B.⊆ᴰ (ι ∣ μ₁ ∣ᴴ)
           ⊆₂ x = _ , ι-∈ (∈-< (dom-⊆ x))

           ∈-≡ : ∀ {β β' : Bij} {x : ℕ} → x ∈ᴿ′ β → β ≡ β' → x ∈ᴿ′ β'
           ∈-≡ ∈₁ eq rewrite eq = ∈₁

           ⊆₁′ : (β ∘ ι ∣ μ₁ ∣ᴴ) B.⊆ᴿ (ι ∣ μ₂ ∣ᴴ)
           ⊆₁′ x =  _ , ι-∈ (∈-< ≤₁)
             where ≤₁ = rng-⊆ (∈-≡ {β = (β ∘ ι ∣ μ₁ ∣ᴴ)} {β' = β} x (absorb-ι₂ ⊆₂))

           ⊆₁ : (β ∘ ι ∣ μ₁ ∣ᴴ ⁻¹) B.⊆ᴿ (ι ∣ μ₂ ∣ᴴ)
           ⊆₁ x rewrite ι-inv {∣ μ₁ ∣ᴴ} = ⊆₁′ x

           β'≡β : β' ≡ β
           β'≡β =
             begin
               (ι ∣ μ₂ ∣ᴴ ∘ β ∘ (ι ∣ μ₁ ∣ᴴ) ⁻¹) ≡⟨ absorb-ι₁ ⊆₁ ⟩
               β ∘ (ι ∣ μ₁ ∣ᴴ) ⁻¹ ≡⟨ absorb-ι₂ ⊆₂ ⟩
               β
             ∎

           μ₁'≈μ₂' : μ₁' ≈⟨ β ⟩ᴴ μ₂'
           μ₁'≈μ₂' with square-≈ᴴ {β = β} μ₁≈μ₂ μ₁≈μ₁' μ₂≈μ₂'
           ... | ≈₁ rewrite β'≡β = ≈₁

  newᴴ-≈ᴴ : ∀ {μ₁ μ₂ β τ} {v₁ v₂ : Value τ} →
              μ₁ ≈⟨ β ⟩ᴴ μ₂ →
             (snocᴴ μ₁ v₁) ≈⟨ β ⟩ᴴ (snocᴴ μ₂ v₂)
  newᴴ-≈ᴴ {μ₁} {μ₂} {β} {τ} {v₁} {v₂} ≈
    = record { dom-⊆ = λ n∈β → wken-∈′ (dom-⊆ n∈β)
             ; rng-⊆ = λ n∈β → wken-∈′ (rng-⊆ n∈β)
             ; lift-≅ = lift-≅′ }
    where open _≈⟨_⟩ᴴ_ ≈
          open Bijectionᴾ β
          lift-≅′ : Lift-≅ (snocᴴ μ₁ v₁) (snocᴴ μ₂ v₂) β
          lift-≅′ n∈β ∈₁ ∈₂ with dom-⊆ (_ , n∈β) |  rng-⊆ (_ , right-inverse-of n∈β)
          ... | τ₁ , v₁ , ∈₁′ | τ₂ , v₂ , ∈₂′ with inj-∈′ ∈₁ (wken-∈ ∈₁′) |  inj-∈′ ∈₂ (wken-∈ ∈₂′)
          ... | refl , refl | refl , refl = lift-≅ n∈β ∈₁′ ∈₂′

  instance _≟ᴺ_ = _≟_

  ≈-# : ∀ {μ₁ μ₂ β} → μ₁ ≈⟨ β ⟩ᴴ μ₂ → β # (∥ μ₁ ∥ᴴ ↔ ∥ μ₂ ∥ᴴ)
  ≈-# {μ₁} {μ₂} {β} ≈ = ∉-# to ∉₁ , ∉-# from ∉₂
     where open _≈⟨_⟩ᴴ_ ≈
           open import Data.Empty
           open import Generic.Partial.Function
           open Bijectionᴾ β

           ∉₁ : ∥ μ₁ ∥ᴴ ∉ᴰ to
           ∉₁ with to ∥ μ₁ ∥ᴴ | inspect to ∥ μ₁ ∥ᴴ
           ∉₁ | just x | [ eq ] = ⊥-elim (∉-oob (dom-⊆ (_ , eq)))
           ∉₁ | nothing | [ eq ] = nothing

           ∉₂ : ∥ μ₂ ∥ᴴ ∉ᴰ from
           ∉₂ with from ∥ μ₂ ∥ᴴ | inspect from ∥ μ₂ ∥ᴴ
           ∉₂ | just x | [ eq ] = ⊥-elim (∉-oob (rng-⊆ (_ ,  eq)))
           ∉₂ | nothing | [ eq ] = nothing

  -- Also newᴴ ?
  newᴸ-≈ᴴ : ∀ {μ₁ μ₂ β τ} {v₁ v₂ : Value τ} →
              v₁ ≈⟨ β ⟩ⱽ v₂ →
              (≈ : μ₁ ≈⟨ β ⟩ᴴ μ₂) →
              let instance _ =  ≈-# ≈ in
             (snocᴴ μ₁ v₁) ≈⟨ β ∣ᴮ (∥ μ₁ ∥ᴴ ↔ ∥ μ₂ ∥ᴴ) ⟩ᴴ (snocᴴ μ₂ v₂)
  newᴸ-≈ᴴ {μ₁} {μ₂} {β} {τ} {v₁} {v₂} ≈ⱽ ≈
    = record { dom-⊆ = dom-⊆
             ; rng-⊆ = rng-⊆
             ; lift-≅ = lift-≅ }
      where module S₁ = _≈⟨_⟩ᴴ_ ≈
            instance _ =  ≈-# ≈
            open Bijectionᴾ β
            open import Relation.Nullary

            β' = β ∣ᴮ (∥ μ₁ ∥ᴴ ↔ ∥ μ₂ ∥ᴴ)

            β⊆β' : β ⊆ β'
            β⊆β' = ∣ᴮ-⊆₁ β (∥ μ₁ ∥ᴴ ↔ ∥ μ₂ ∥ᴴ)

            module B₁ = Bijectionᴾ β'
            module B₂ = Bijectionᴾ (β' ⁻¹)

            dom-⊆ : β' ⊆ᴰ (snocᴴ μ₁ v₁)
            dom-⊆ {n} (_ , eq) with to n | inspect to n
            dom-⊆ {n} (_ , eq) | just x | [ eq' ] = wken-∈′ (S₁.dom-⊆ (_ , eq'))
            dom-⊆ {n} (_ , eq) | nothing | [ eq' ] with ∥ μ₁ ∥ᴴ ≟ n
            dom-⊆ {._} (_ , eq) | nothing | [ eq' ] | yes refl = last-∈′ μ₁
            dom-⊆ {n} (_ , ()) | nothing | [ eq' ] | no ¬p

            rng-⊆ : β' ⊆ᴿ (snocᴴ μ₂ v₂)
            rng-⊆ {n} (m , eq) with from n | inspect from n
            rng-⊆ {n} (m , eq) | just x | [ eq' ] = wken-∈′ (S₁.rng-⊆ (_ , eq'))
            rng-⊆ {n} (m , eq) | nothing | [ eq' ] with ∥ μ₂ ∥ᴴ ≟ n
            rng-⊆ {._} (m , eq) | nothing | [ eq' ] | yes refl = last-∈′ μ₂
            rng-⊆ {n} (m , ()) | nothing | [ eq' ] | no ¬p

            lift-≅ : Lift-≅ (snocᴴ μ₁ v₁) (snocᴴ μ₂ v₂) β'
            lift-≅ {n₁} {n₂} ∈ᴮ ∈₁ ∈₂ with to n₁ | inspect to n₁
            lift-≅ {n₁} {n₂} refl ∈₁ ∈₂ | just x | [ eq ] with S₁.dom-⊆ (_ , eq) | S₁.rng-⊆ (_ , right-inverse-of eq)
            ... | τ₁' , v₁' , ∈₁′ | τ₂' , v₂' , ∈₂′ with inj-∈′ ∈₁ (wken-∈ ∈₁′) | inj-∈′ ∈₂ (wken-∈ ∈₂′)
            ... | refl , refl | refl , refl = wken-≅ⱽ β⊆β' (S₁.lift-≅ eq ∈₁′ ∈₂′)
            lift-≅ {n₁} {n₂} ∈ᴮ ∈₁ ∈₂ | nothing | [ eq ] with ∥ μ₁ ∥ᴴ ≟ n₁
            lift-≅ .{∥ μ₁ ∥ᴴ} {n₂} ∈ᴮ ∈₁ ∈₂ | nothing | [ eq ] | yes refl with last-≡ ∈₁
            lift-≅ .{∥ μ₁ ∥ᴴ} .{∥ μ₂ ∥ᴴ} refl ∈₁ ∈₂ | nothing | [ eq ] | yes refl | refl , refl with last-≡ ∈₂
            ... | refl , refl = wken-≅ⱽ β⊆β' ⌞ ≈ⱽ ⌟
            lift-≅ {n₁} {n₂} () ∈₁ ∈₂ | nothing | [ eq ] | no ¬p

  -- TODO maybe this can be inlined
  readᴸ-≈ⱽ : ∀ {β n₁ n₂ μ₁ μ₂ τ} {v₁ v₂ : Value τ} →
                       (n₁ , n₂) ∈ᵗ β → n₁ ↦ v₁ ∈ᴴ μ₁ → n₂ ↦ v₂ ∈ᴴ μ₂ →
                       μ₁ ≈⟨ β ⟩ᴴ μ₂ → v₁ ≈⟨ β ⟩ⱽ v₂
  readᴸ-≈ⱽ {β} ∈β ∈₁ ∈₂ μ≈ = lift-≈ ∈β ∈₁ ∈₂
    where open _≈⟨_⟩ᴴ_ μ≈


  writeᴸ-≈ᴴ : ∀ {β μ₁ μ₂ μ₁' μ₂' n₁ n₂ τ} {v₁ v₂ : Value τ} →
              μ₁ ≈⟨ β ⟩ᴴ μ₂ →
              v₁ ≈⟨ β ⟩ⱽ v₂ →
              μ₁' ≔ μ₁ [ n₁ ↦ v₁ ]ᴴ → μ₂' ≔ μ₂ [ n₂ ↦ v₂ ]ᴴ →
              (n₁ , n₂) ∈ᵗ β →
              μ₁' ≈⟨ β ⟩ᴴ μ₂'
  writeᴸ-≈ᴴ {β} {μ₁} {μ₂} {μ₁'} {μ₂'} {n₁} {n₂} μ≈ c≈ w₁ w₂ ∈β
    = record { dom-⊆ = dom-⊆′ ; rng-⊆ = rng-⊆′ ; lift-≅ = lift-≅′ }

    where open import Relation.Nullary
          open import Data.Empty
          open _≈⟨_⟩ᴴ_ μ≈

          dom-⊆′ : β ⊆ᴰ μ₁'
          dom-⊆′ ∈β with ∈-< (dom-⊆ ∈β)
          ... | n≤μ₁ rewrite sym (write-length-≡ w₁) = <-∈ n≤μ₁

          rng-⊆′ : β ⊆ᴿ μ₂'
          rng-⊆′ ∈β with ∈-< (rng-⊆ ∈β)
          ... | n≤μ₂ rewrite sym (write-length-≡ w₂) = <-∈ n≤μ₂

          lift-≅′ : Lift-≅ μ₁' μ₂' β
          lift-≅′ {n₁'} {n₂'} ∈β' ∈₁ ∈₂ with n₁' ≟ n₁ | n₂' ≟ n₂
          -- The updated cells are looked up, they are related by hypothesis
          lift-≅′ {_} {_} ∈β' ∈₁ ∈₂ | yes refl | yes refl with inj-∈′ ∈₁ (write-∈ w₁) | inj-∈′ ∈₂ (write-∈ w₂)
          ... | refl , refl | refl , refl = ⌞ c≈ ⌟
          -- Spurious cases, the bijection has multiple images/pre-images
          lift-≅′ {_} {n₂'} ∈β' ∈₁ ∈₂ | yes refl | no ¬p = ⊥-elim (¬p (only-oneᵗ β ∈β' ∈β) )
          lift-≅′ {n₁'} {_} ∈β' ∈₁ ∈₂ | no ¬p | yes refl = ⊥-elim (¬p (only-oneᶠ β ∈β' ∈β) )
          -- All the other cells are unchanged and remain related
          lift-≅′ {_} {_} ∈β' ∈₁ ∈₂ | no ¬p₁ | no ¬p₂ with write-∈′′ w₁ (_ , _ , ∈₁)
          ... | _ , _ , ∈₁' with write-only-one′ w₁ (λ p₁ → ¬p₁ (sym p₁)) ∈₁' ∈₁
          ... | refl , refl with write-∈′′ w₂ (_ , _ , ∈₂)
          ... | _ , _ , ∈₂' with write-only-one′ w₂ (λ p₂ → ¬p₂ (sym p₂)) ∈₂' ∈₂
          ... | refl , refl = lift-≅ ∈β' ∈₁' ∈₂'
