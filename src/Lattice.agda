module Lattice where

-- Definition of Security Lattice.
open import Lattice.Base public

open import Algebra.FunctionProperties
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

-- This REWRITE pragma is here because it is not allowed it in a
-- bound context like a parametrized modules (virtually all other
-- modules are parmetrized)

{-# BUILTIN REWRITE _≡_ #-}

IsLattice : ∀ {A : Set} → Rel A _ → Op₂ A → Op₂ A → Set
IsLattice = IsSecurityLattice _≡_

-- Lattice is a security lattice for simple types
Lattice : Set₁
Lattice = SecurityLattice zero zero
  where open import Level

module API (𝑳 : Lattice) where

  -- Friendly API obtained from the algebraic and order theoreic
  -- lattice definitions and decidability.

  open import Relation.Nullary
  open import Data.Empty
  open import Data.Product
  open import Data.Sum

  open SecurityLattice 𝑳 renaming
    ( Carrier to Label
    ; _∨_ to _⊔_
    ; _∧_ to _⊓_
    ; _≤_ to _⊑_
    ; _≤?_ to _⊑?_
    ) public

  private
    module S = IsSecurityLattice isSecurityLattice

  _⋤_ : Label → Label → Set
  ℓ₁ ⋤ ℓ₂ = ¬ (ℓ₁ ⊑ ℓ₂)

  refl-⊑ : ∀ {l} → l ⊑ l
  refl-⊑ = S.refl

  trans-⊑ : ∀ {ℓ₁ ℓ₂ l₃} → ℓ₁ ⊑ ℓ₂ → ℓ₂ ⊑ l₃ → ℓ₁ ⊑ l₃
  trans-⊑ = S.trans --  IsPreorder.trans PO.isPreorder

  antisym-⊑ : ∀ {ℓ₁ ℓ₂} → ℓ₁ ⊑ ℓ₂ → ℓ₂ ⊑ ℓ₁ → ℓ₁ ≡ ℓ₂
  antisym-⊑ = S.antisym

  private
    prop₁ : ∀ x y → x ⊑ (x ⊔ y)
    prop₁ x y = proj₁ (supremum x y)

    prop₂ : ∀ x y → y ⊑ (x ⊔ y)
    prop₂ x y = proj₁ (proj₂ (supremum x y))

    prop₃ : ∀ {x y z} → x ⊑ z → y ⊑ z → (x ⊔ y) ⊑ z
    prop₃ {x} {y} {z} = proj₂ (proj₂ (supremum x y)) z

  idem-⊔ : ∀ ℓ → (ℓ ⊔ ℓ) ≡ ℓ
  idem-⊔ ℓ = antisym-⊑ (prop₃ refl-⊑ refl-⊑) (prop₁ ℓ ℓ)

  sym-⊔ : ∀ ℓ₁ ℓ₂ → (ℓ₁ ⊔ ℓ₂) ≡ (ℓ₂ ⊔ ℓ₁)
  sym-⊔ = ∨-comm

  assoc-⊔ : ∀ ℓ₁ ℓ₂ ℓ₃ → (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃) ≡ ((ℓ₁ ⊔ ℓ₂) ⊔ ℓ₃)
  assoc-⊔ x y z = sym (∨-assoc x y z)

  join-⊑₁ : ∀ ℓ₁ ℓ₂ → ℓ₁ ⊑ (ℓ₁ ⊔ ℓ₂)
  join-⊑₁ = prop₁

  join-⊑₂ : ∀ ℓ₁ ℓ₂ → ℓ₁ ⊑ (ℓ₂ ⊔ ℓ₁)
  join-⊑₂ ℓ₁ ℓ₂ rewrite sym-⊔ ℓ₂ ℓ₁ = join-⊑₁ ℓ₁ ℓ₂

  ub : ∀ {ℓ₁ ℓ₂} → ℓ₁ ⊑ ℓ₂ → (ℓ₁ ⊔ ℓ₂) ≡ ℓ₂
  ub x = antisym-⊑ (prop₃ x refl-⊑) (prop₂ _ _)

  ub' : ∀ {ℓ₁ ℓ₂} → ℓ₁ ⊑ ℓ₂ → (ℓ₂ ⊔ ℓ₁) ≡ ℓ₂
  ub' {ℓ₁} {ℓ₂} p rewrite sym-⊔ ℓ₂ ℓ₁ = ub p

  split-≡ : ∀ {ℓ₁ ℓ₁' ℓ₂ ℓ₂'} → ℓ₁ ≡ ℓ₁' → ℓ₂ ≡ ℓ₂' → ℓ₁ ⊔ ℓ₂ ≡ ℓ₁' ⊔ ℓ₂'
  split-≡ eq₁ eq₂ rewrite eq₁ | eq₂ = refl

  idem-⊔' : ∀ ℓ → ℓ ≡ ℓ ⊔ ℓ
  idem-⊔' _ = sym (idem-⊔ _)

  idem-⊑ : ∀ {ℓ} → (ℓ ⊔ ℓ) ⊑ ℓ
  idem-⊑ {ℓ} rewrite idem-⊔ ℓ = refl-⊑

  join-⊑ : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} → ℓ₁ ⊑ ℓ₂ → ℓ₃ ⊑ ℓ₄ → (ℓ₁ ⊔ ℓ₃) ⊑ (ℓ₂ ⊔ ℓ₄)
  join-⊑ {ℓ₁} {ℓ₂} {ℓ₃} {ℓ₄} ℓ₁⊑ℓ₂ ℓ₃⊑ℓ₄ with join-⊑₁ ℓ₁ ℓ₃ | join-⊑₁ ℓ₂ ℓ₄
  ... | ℓ₁⊑ℓ₃ | ℓ₂⊑ℓ₄ with join-⊑₁ (ℓ₁ ⊔ ℓ₃) (ℓ₂ ⊔ ℓ₄)
  ... | r = subst₂ _⊑_ refl eq r
    where
          eq : (ℓ₁ ⊔ ℓ₃) ⊔ (ℓ₂ ⊔ ℓ₄) ≡ ℓ₂ ⊔ ℓ₄
          eq =
            begin
              (ℓ₁ ⊔ ℓ₃) ⊔ ℓ₂ ⊔ ℓ₄
            ≡⟨ assoc-⊔ (ℓ₁ ⊔ ℓ₃) ℓ₂ ℓ₄ ⟩
              ((ℓ₁ ⊔ ℓ₃) ⊔ ℓ₂) ⊔ ℓ₄
            ≡⟨ cong (λ x → x ⊔ ℓ₄) (sym (assoc-⊔ ℓ₁ ℓ₃ ℓ₂)) ⟩
              (ℓ₁ ⊔ ℓ₃ ⊔ ℓ₂) ⊔ ℓ₄
            ≡⟨ cong (λ x → (ℓ₁ ⊔ x) ⊔ ℓ₄) (sym-⊔ ℓ₃ ℓ₂) ⟩
              (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃) ⊔ ℓ₄
            ≡⟨ cong (λ x → x ⊔ ℓ₄) (assoc-⊔ ℓ₁ ℓ₂ ℓ₃) ⟩
              ((ℓ₁ ⊔ ℓ₂) ⊔ ℓ₃) ⊔ ℓ₄
            ≡⟨ sym (assoc-⊔ (ℓ₁ ⊔ ℓ₂) ℓ₃ ℓ₄) ⟩
              (ℓ₁ ⊔ ℓ₂) ⊔ (ℓ₃ ⊔ ℓ₄)
            ≡⟨ cong (λ x → x ⊔ _) (ub ℓ₁⊑ℓ₂)  ⟩
              ℓ₂ ⊔ (ℓ₃ ⊔ ℓ₄)
            ≡⟨ cong (λ y → _ ⊔ y) (ub ℓ₃⊑ℓ₄) ⟩
              ℓ₂ ⊔ ℓ₄
            ∎
            where open ≡-Reasoning

  join-⊑' : ∀ {ℓ₁ ℓ₂ ℓ₃} → ℓ₁ ⊑ ℓ₃ → ℓ₂ ⊑ ℓ₃ → (ℓ₁ ⊔ ℓ₂) ⊑ ℓ₃
  join-⊑' {ℓ₃ = ℓ₃}  p₁ p₂ with join-⊑ p₁ p₂
  ... | x rewrite idem-⊔ ℓ₃ = x

  trans-⋤  : ∀ {a b c} → a ⊑ b → a ⋤ c → b ⋤ c
  trans-⋤ a⊑b ¬a⊑c b⊑c = ⊥-elim (¬a⊑c (trans-⊑ a⊑b b⊑c))

  join-⋤₁ : ∀ {ℓ₁ ℓ₂ ℓ₃} → ℓ₁ ⋤ ℓ₂ → (ℓ₁ ⊔ ℓ₃) ⋤ ℓ₂
  join-⋤₁ ℓ₁⋤ℓ₂ p = trans-⋤ (join-⊑₁ _ _) ℓ₁⋤ℓ₂ p

  join-⋤₂ : ∀ {ℓ₁ ℓ₂ ℓ₃} → ℓ₁ ⋤ ℓ₂ → (ℓ₃ ⊔ ℓ₁) ⋤ ℓ₂
  join-⋤₂ ℓ₁⋤ℓ₂ p = trans-⋤ (join-⊑₂ _ _) ℓ₁⋤ℓ₂ p

  unjoin-⊑ : ∀ {x y z} → (x ⊔ y) ⊑ z → (x ⊑ z) × (y ⊑ z)
  unjoin-⊑ {x} {y} {z} p with x ⊑? z | y ⊑? z
  unjoin-⊑ {x} {y} {z} p | yes x⊑z | yes y⊑z = x⊑z , y⊑z
  unjoin-⊑ {x} {y} {z} p | yes x⊑z | no y⋤z = ⊥-elim (join-⋤₂ y⋤z p)
  unjoin-⊑ {x} {y} {z} p | no x⋤z | _ = ⊥-elim (join-⋤₁ x⋤z p)

open API {{...}} public
