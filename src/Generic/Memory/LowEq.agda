{-# OPTIONS --allow-unsolved-metas #-}

open import Lattice
open import Relation.Binary
open import Generic.Bijection

module Generic.Memory.LowEq
  {Ty : Set}
  {Value : Ty → Set}
  {{𝑳 : Lattice}}
  (_≈⟨_⟩ⱽ_ : Relᴮ {Ty} Value)
  (A : Label) where

open import Generic.Memory Ty Value public
open import Data.Unit hiding (_≟_)
open import Relation.Nullary

data Memory-≈ᴹ {ℓ} (β : Bij) : Memory ℓ → Memory ℓ → Set where
  [] : Memory-≈ᴹ β [] []
  _∷_ : ∀ {τ M₁ M₂} {v₁ v₂ : Value τ} →
          (v₁≈v₂ : v₁ ≈⟨ β ⟩ⱽ v₂) (M₁≈M₂ : Memory-≈ᴹ β M₁ M₂) →
          Memory-≈ᴹ β (v₁ ∷ M₁) (v₂ ∷ M₂)

-- Pointwise low-equivalence (for observable memories)
_≈⟨_⟩ᴹ_ : ∀ {ℓ} → Memory ℓ → Bij → Memory ℓ → Set
M₁ ≈⟨ β ⟩ᴹ M₂ = Memory-≈ᴹ β M₁ M₂


-- Any pair of non-observable memories are related, otherwise they are related pointwise
_≈⟨_,_⟩ᴹ_ : ∀ {ℓ} → Memory ℓ → Bij → Dec (ℓ ⊑ A) → Memory ℓ → Set
M₁ ≈⟨ β , yes p ⟩ᴹ M₂ = M₁ ≈⟨ β ⟩ᴹ M₂
M₁ ≈⟨ _ , no ¬p ⟩ᴹ M₂ = ⊤

_≈⟨_⟩ᴹ′_ : ∀ {ℓ} → Memory ℓ → Bij → Memory ℓ → Set
M₁ ≈⟨ β ⟩ᴹ′ M₂ = M₁ ≈⟨ β , _ ⊑? A ⟩ᴹ M₂

⌞_⌟ᴹ : ∀ {ℓ β} {M₁ M₂ : Memory ℓ} → M₁ ≈⟨ β ⟩ᴹ M₂ → M₁ ≈⟨ β , ℓ ⊑? A ⟩ᴹ M₂
⌞_⌟ᴹ {ℓ} M₁≈M₂ with ℓ ⊑? A
... | yes ℓ⊑A = M₁≈M₂
... | no ℓ⋤A = tt

module Props (𝑽 : IsEquivalenceᴮ {Ty} {Value} _≈⟨_⟩ⱽ_) where

  open import Generic.Value.LowEq {Ty} {Value} _≈⟨_⟩ⱽ_
  open Props 𝑽
  open IsEquivalenceᴮ
  open import Data.Nat using (ℕ ; _≤_ ; _<_ ; s≤s ; z≤n) renaming (_⊔_ to _⊔ᴺ_)
  open import Data.Nat.Properties

  ∣_∣ᴹ : ∀ {ℓ} → Memory ℓ → ℕ
  ∣ [] ∣ᴹ = 0
  ∣ v ∷ M ∣ᴹ = ∣ v ∣ⱽ ⊔ᴺ ∣ M ∣ᴹ

  infixl 1 ∣_∣ᴹ

  module ≈ᴹ-Equivalence where

    wken-≈ᴹ : Wkenᴮ {F = Memory} _≈⟨_⟩ᴹ_
    wken-≈ᴹ n≤m [] = []
    wken-≈ᴹ n≤m (v₁≈v₂ ∷ M₁≈M₂) = wken-≈ⱽ n≤m v₁≈v₂ ∷ wken-≈ᴹ n≤m M₁≈M₂


    -- Reflexive
    refl-≈ᴹ :  Reflexiveᴮ {F = Memory} _≈⟨_⟩ᴹ_ ∣_∣ᴹ
    refl-≈ᴹ {x = []} = []
    refl-≈ᴹ {x = v ∷ M} = ≈ⱽ ∷ ≈ᴹ
      where ≈ⱽ = wken-≈ⱽ (m≤m⊔n ∣ v ∣ⱽ ∣ M ∣ᴹ) refl-≈ⱽ
            ≈ᴹ = wken-≈ᴹ (n≤m⊔n ∣ v ∣ⱽ ∣ M ∣ᴹ) refl-≈ᴹ

    -- Symmetric
    sym-≈ᴹ : Symmetricᴮ {F = Memory} _≈⟨_⟩ᴹ_
    sym-≈ᴹ [] = []
    sym-≈ᴹ (v₁≈v₂ ∷ M₁≈M₂) = sym-≈ⱽ v₁≈v₂ ∷ sym-≈ᴹ M₁≈M₂

    -- Transitive
    trans-≈ᴹ : Transitiveᴮ {F = Memory} _≈⟨_⟩ᴹ_ -- {ℓ} → {M₁ M₂ M₃ : Memory ℓ} → M₁ ≈ᴹ M₂ → M₂ ≈ᴹ M₃ → M₁ ≈ᴹ M₃
    trans-≈ᴹ [] [] = []
    trans-≈ᴹ (v₁≈v₂ ∷ M₁≈M₂) (v₂≈v₃ ∷ M₂≈M₃) = trans-≈ⱽ v₁≈v₂ v₂≈v₃ ∷ trans-≈ᴹ M₁≈M₂ M₂≈M₃

    ≈ᴹ-isEquivalence : IsEquivalenceᴮ {F = Memory} _≈⟨_⟩ᴹ_
    ≈ᴹ-isEquivalence =
      record { Dom = ∣_∣ᴹ
             ; wkenᴮ = wken-≈ᴹ
             ; reflᴮ = refl-≈ᴹ
             ; symᴮ = sym-≈ᴹ
             ; transᴮ = trans-≈ᴹ }

  open ≈ᴹ-Equivalence public

  --------------------------------------------------------------------------------

  module ≈ᴹ′-Equivalence  where

  wken-≈ᴹ′ : Wkenᴮ {F = Memory} _≈⟨_⟩ᴹ′_
  wken-≈ᴹ′ {a = ℓ} n≤m x with ℓ ⊑? A
  wken-≈ᴹ′ {a} n≤m x | yes p = wken-≈ᴹ n≤m x
  wken-≈ᴹ′ {a} n≤m x | no ¬p = tt

  refl-≈ᴹ′ : Reflexiveᴮ {F = Memory}  _≈⟨_⟩ᴹ′_ ∣_∣ᴹ
  refl-≈ᴹ′ = ⌞ refl-≈ᴹ ⌟ᴹ

  sym-≈ᴹ′ : Symmetricᴮ {F = Memory} _≈⟨_⟩ᴹ′_
  sym-≈ᴹ′ {a = ℓ} x with ℓ ⊑? A
  sym-≈ᴹ′ {a} x | yes p = sym-≈ᴹ x
  sym-≈ᴹ′ {a} x | no ¬p = tt

  trans-≈ᴹ′ : Transitiveᴮ {F = Memory} _≈⟨_⟩ᴹ′_
  trans-≈ᴹ′ {a = ℓ} x y with ℓ ⊑? A
  trans-≈ᴹ′ {a} x y | yes p = trans-≈ᴹ x y
  trans-≈ᴹ′ {a} x y | no ¬p = tt

  ≈ᴹ′-isEquivalence : IsEquivalenceᴮ {F = Memory} _≈⟨_⟩ᴹ′_
  ≈ᴹ′-isEquivalence =
    record { Dom = ∣_∣ᴹ
           ; wkenᴮ = wken-≈ᴹ′
           ; reflᴮ = refl-≈ᴹ′
           ; symᴮ = sym-≈ᴹ′
           ; transᴮ = trans-≈ᴹ′ }

  open ≈ᴹ′-Equivalence public


  -- Not sure if this API is better, but they don't fix exactly our Equivalenceᴮ definitions
  -- refl-≈⟨_⟩ᴹ : ∀ {ℓ} {M : Memory ℓ} (x : Dec (ℓ ⊑ A)) → M ≈⟨ ι ∣ M ∣ᴹ , x ⟩ᴹ M
  -- refl-≈⟨ yes p ⟩ᴹ = refl-≈ᴹ
  -- refl-≈⟨ no ¬p ⟩ᴹ = tt

--     sym-≈⟨_⟩ᴹ : ∀ {ℓ} {M₁ M₂ : Memory ℓ} (x : Dec (ℓ ⊑ A)) → M₁ ≈⟨ x ⟩ᴹ M₂ → M₂ ≈⟨ x ⟩ᴹ M₁
--     sym-≈⟨ yes p ⟩ᴹ M₁≈M₂ = sym-≈ᴹ M₁≈M₂
--     sym-≈⟨ no ¬p ⟩ᴹ M₁≈M₂ = tt

--     trans-≈⟨_⟩ᴹ : ∀ {ℓ} {M₁ M₂ M₃ : Memory ℓ} → (x : Dec (ℓ ⊑ A)) →  M₁ ≈⟨ x ⟩ᴹ M₂ → M₂ ≈⟨ x ⟩ᴹ M₃ → M₁ ≈⟨ x ⟩ᴹ M₃
--     trans-≈⟨ yes p ⟩ᴹ M₁≈M₂ M₂≈M₃ = trans-≈ᴹ M₁≈M₂ M₂≈M₃
--     trans-≈⟨ no ¬p ⟩ᴹ M₁≈M₂ M₂≈M₃ = tt

    -- ≈⟨_⟩ᴹ-isEquivalence : ∀ {ℓ} (x : Dec (ℓ ⊑ A)) → IsEquivalence (λ (M₁ M₂ : Memory ℓ) → M₁ ≈⟨ x ⟩ᴹ M₂)
    -- ≈⟨ x ⟩ᴹ-isEquivalence = record { refl = refl-≈⟨ x ⟩ᴹ ; sym = sym-≈⟨ x ⟩ᴹ ; trans = trans-≈⟨ x ⟩ᴹ }

--   open ≈⟨_⟩ᴹ-Equivalence public

  --------------------------------------------------------------------------------
  open import Relation.Binary.PropositionalEquality

  -- Low memories have the same length
  ∥_∥-≡ : ∀ {ℓ β} {M₁ M₂ : Memory ℓ} → M₁ ≈⟨ β ⟩ᴹ M₂ → ∥ M₁ ∥ ≡ ∥ M₂ ∥
  ∥ [] ∥-≡ = refl
  ∥ x ∷ M₁≈M₂ ∥-≡ rewrite ∥ M₁≈M₂ ∥-≡ = refl

  new-≈ᴹ : ∀ {τ ℓ β} {M₁ M₂ : Memory ℓ} {v₁ v₂ : Value τ} →
                M₁ ≈⟨ β ⟩ᴹ M₂ → v₁ ≈⟨ β ⟩ⱽ v₂ → (M₁ ∷ᴿ v₁) ≈⟨ β ⟩ᴹ (M₂ ∷ᴿ v₂)
  new-≈ᴹ [] v₁≈v₂ = v₁≈v₂ ∷ []
  new-≈ᴹ (v₁≈v₂' ∷ M₁≈M₂) v₁≈v₂ = v₁≈v₂' ∷ (new-≈ᴹ M₁≈M₂ v₁≈v₂)

  update-≈ᴹ : ∀ {ℓ τ n β} {M₁ M₁' M₂ M₂' : Memory ℓ} {v₁ v₂ : Value τ} →
                M₁ ≈⟨ β ⟩ᴹ M₂ →
                v₁ ≈⟨ β ⟩ⱽ v₂ →
                M₁' ≔ M₁ [ n ↦ v₁ ]ᴹ →
                M₂' ≔ M₂ [ n ↦ v₂ ]ᴹ →
                M₁' ≈⟨ β ⟩ᴹ M₂'
  update-≈ᴹ (_ ∷ M₁≈M₂) v₁≈v₂ Here Here = v₁≈v₂ ∷ M₁≈M₂
  update-≈ᴹ (v₁≈v₂' ∷ M₁≈M₂) v₁≈v₂ (There u₁) (There u₂) = v₁≈v₂' ∷ update-≈ᴹ M₁≈M₂ v₁≈v₂ u₁ u₂

  read-≈ᴹ : ∀ {ℓ τ n β} {M₁ M₂ : Memory ℓ} {v₁ v₂ : Value τ} →
              M₁ ≈⟨ β ⟩ᴹ M₂ →
              n ↦ v₁ ∈ᴹ M₁ →
              n ↦ v₂ ∈ᴹ M₂ →
              v₁ ≈⟨ β ⟩ⱽ v₂
  read-≈ᴹ (v₁≈v₂ ∷ _) Here Here = v₁≈v₂
  read-≈ᴹ (_ ∷ M₁≈M₂) (There r₁) (There r₂) = read-≈ᴹ M₁≈M₂ r₁ r₂

  --------------------------------------------------------------------------------
