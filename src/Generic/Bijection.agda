-- {-# OPTIONS --allow-unsolved-metas #-}

module Generic.Bijection where

open import Data.Empty
open import Data.Fin hiding (_≤?_ ; _≤_ ; _<_ ; #_)
open import Data.Maybe as M
open import Data.Nat renaming (_+_ to _+ᴺ_)
open import Data.Nat.Properties hiding (suc-injective)
open import Data.Product
open import Generic.Partial.Bijection public
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

-- Bijection between memory addresses represented as natural numbers.
Bij : Set
Bij = ℕ ⤖ᴾ ℕ

-- ι n is the identity bijection over the domain {0, ... n-1}
ι : ℕ → Bij
ι n = bijᴾ idᴾ idᴾ (inv , inv)
  where open Id n

ι-∈ : ∀ {m n} → m < n → (m , m) ∈ᵗ (ι n)
ι-∈ {m} {n} m<n with m <? n
ι-∈ {m} {n} m<n | yes _ = refl
ι-∈ {m} {n} m<n | no m≮n = ⊥-elim (m≮n m<n)

ι-≡ : ∀ {a b c} → (a , b) ∈ᵗ (ι c) → a ≡ b
ι-≡ {c = c} = idᴾ-≡
  where open Id c

ι-≤ᴰ : ∀ {a b c} → (a , b) ∈ᵗ (ι c) → a < c
ι-≤ᴰ {c = c} = idᴾ-<ᴰ
  where open Id c

ι-extends : ∀ {n m} → n ≤ m → (ι m) Extends (ι n)
ι-extends {n} {m} n≤m {a , b} ∈₁ with a <? m | a <? n
ι-extends {n} {m} n≤m {a , b} ∈₁ | yes p | yes p₁ = ∈₁
ι-extends {n} {m} n≤m {a , b} () | yes p | no ¬p
ι-extends {n} {m} n≤m {a , .a} refl | no ¬p | yes p = ⊥-elim (¬p (≤-trans p n≤m))
ι-extends {n} {m} n≤m {a , b} () | no ¬p | no ¬p₁

ι-⊆ : ∀ {n m} → n ≤ m → ι n ⊆ ι m
ι-⊆ n≤m = record { bij-⊆ = ι-extends n≤m }

ι-⊆ᴿ : ∀ {n m} → n ≤ m → ι n ⊆ᴿ ι m
ι-⊆ᴿ {n} {m} n≤m (x , ∈₁) rewrite ι-≡ ∈₁ = _ , ι-extends n≤m ∈₁′
  where open Bijectionᴾ (ι n)
        ∈₁′ = left-inverse-of ∈₁

-- Absorbs the ι with the greater domain.
absorb-ι₁ : ∀ {n β} →  β ⊆ᴿ (ι n) → (ι n ∘ β) ≡ β
absorb-ι₁ {n} {β} ⊆₁ = bij-≡ (ι n ∘ β) β (funext _ _ to-ι) (funext _ _ from-ι)

  where open Bijectionᴾ
        to-ι : ∀ x → to (ι n ∘ β) x ≡ to β x
        to-ι x with to β x | inspect (to β) x
        to-ι x | just y | [ eq ] with y <? n
        to-ι x | just y | [ eq ] | yes p = refl
        to-ι x | just y | [ eq ] | no ¬p with ⊆₁ (_ , right-inverse-of β eq)
        to-ι x | just y | [ eq ] | no ¬p | _ , eq' with y <? n
        to-ι x | just y | [ eq ] | no ¬p | _ , eq' | yes p = ⊥-elim (¬p p)
        to-ι x | just y | [ eq ] | no ¬p | _ , () | no ¬p₁
        to-ι x | nothing | [ eq ] = refl


        from-ι : (x : ℕ) → from (ι n ∘ β) x ≡ from β x
        from-ι x with x <? n
        from-ι x | yes p = refl
        from-ι x | no ¬p with from β x | inspect (from β) x
        from-ι x | no ¬p | just y | [ eq ] with ⊆₁ (_ , eq)
        from-ι x | no ¬p | just y | [ eq ] | _ , eq' with x <? n
        from-ι x | no ¬p | just y | [ eq ] | _ , eq' | yes p = ⊥-elim (¬p p)
        from-ι x | no ¬p | just y | [ eq ] | _ , () | no ¬p₁
        from-ι x | no ¬p | nothing | [ eq ] = refl

absorb-ι₂ : ∀ {n β} → β ⊆ᴰ (ι n) → (β ∘ ι n) ≡ β
absorb-ι₂ {n} {β} ⊆₁ = bij-≡ (β ∘ ι n) β (funext _ _ to-ι) (funext _ _ from-ι)
  where open Bijectionᴾ
        to-ι : (x : ℕ) → to (β ∘ ι n) x ≡ to β x
        to-ι x with x <? n
        to-ι x | yes p = refl
        to-ι x | no ¬p with to β x | inspect (to β) x
        to-ι x | no ¬p | just x₁ | [ eq ] with ⊆₁ (_ , eq)
        to-ι x | no ¬p | just x₁ | [ eq ] | _ , eq' with x <? n
        to-ι x | no ¬p | just x₁ | [ eq ] | _ , eq' | yes p = ⊥-elim (¬p p)
        to-ι x | no ¬p | just x₁ | [ eq ] | _ , () | no ¬p₁
        to-ι x | no ¬p | nothing | [ eq ] = refl

        from-ι : (x : ℕ) → from (β ∘ ι n) x ≡ from β x
        from-ι x with from β x | inspect (from β) x
        from-ι x | just y | [ eq ] with y <? n
        from-ι x | just y | [ eq ] | yes p = refl
        from-ι x | just y | [ eq ] | no ¬p with ⊆₁ (_ , left-inverse-of β eq)
        from-ι x | just y | [ eq ] | no ¬p | _ , eq' with y <? n
        from-ι x | just y | [ eq ] | no ¬p | _ , eq' | yes p = ⊥-elim (¬p p)
        from-ι x | just y | [ eq ] | no ¬p | _ , () | no ¬p₁
        from-ι x | nothing | [ eq ] = refl

-- Absorbs the ι with the greater domain.
absorb-ι : ∀ {n m} → m ≤ n → (ι n ∘ ι m) ≡ ι m
absorb-ι {n} {m} m≤n = absorb-ι₁ (ι-⊆ᴿ m≤n)

-- The inverse of the identitiy bijection is the identity bijection.
ι-inv : ∀ n → (ι n) ≡ (ι n)⁻¹
ι-inv n = bij-≡ _ _ refl refl

cong₃ : ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d}
        (f : A → B → C → D) {x y u v w z} → x ≡ y → u ≡ v → z ≡ w → f x u z ≡ f y v w
cong₃ f refl refl refl = refl

square-lemma : ∀ {n₁ n₂ β} → β ⊆ᴿ (ι n₂) → β ⊆ᴰ (ι n₁) → (ι n₂ ∘ β ∘ (ι n₁) ⁻¹) ≡ β
square-lemma {n₁} {n₂} {β} ⊆₁ ⊆₂ = ≡β
  where open ≡-Reasoning

        ⊆₁′ : (β ∘ ι n₁) ⊆ᴿ (ι n₂)
        ⊆₁′ {x} (_ , ∈₁) with split-∈ᶠ {β₁ = ι n₁} {β₂ = β} ∈₁
        ... | y , ∈ᴵ , ∈ᴮ = ⊆₁ (_ , ∈ᴮ)

        ≡β : (ι n₂ ∘ β ∘ (ι n₁) ⁻¹) ≡ β
        ≡β = begin
               ι n₂ ∘ β ∘ (ι n₁) ⁻¹
             ≡⟨ cong₃ (λ a b c → a ∘ b ∘ c) refl refl (ι-inv n₁) ⟩
               ι n₂ ∘ β ∘ (ι n₁)
             ≡⟨ absorb-ι₁ ⊆₁′ ⟩
               β ∘ (ι n₁)
             ≡⟨ absorb-ι₂ ⊆₂ ⟩
               β
             ∎

--------------------------------------------------------------------------------

-- Bijection-indexed equivalence relations for indexed types
module IProps (A : Set) (F : A → Set) where

  Relᴮ : Set₁
  Relᴮ = ∀ {a} → F a → Bij → F a → Set

  Wkenᴮ : Relᴮ → Set
  Wkenᴮ R = ∀ {a β β'} {x y : F a} → β ⊆ β' → R x β y → R x β' y

  Reflexiveᴮ : Relᴮ → (Dom : ∀ {a} → F a → ℕ) → Set
  Reflexiveᴮ R Dom = ∀ {a} {x : F a} → R x (ι (Dom x)) x

  Symmetricᴮ : Relᴮ → Set
  Symmetricᴮ R = ∀ {a β} {x y : F a} → R x β y → R y (β ⁻¹) x

  Transitiveᴮ : Relᴮ → Set
  Transitiveᴮ R = ∀ {a β₁ β₂} {x y z : F a} → R x β₁ y → R y β₂ z → R x (β₂ ∘ β₁) z

  record IsEquivalenceᴮ (R : Relᴮ) (Dom : ∀ {a} → F a → ℕ) : Set where
    field wkenᴮ : Wkenᴮ R
          reflᴮ : Reflexiveᴮ R Dom
          symᴮ : Symmetricᴮ R
          transᴮ : Transitiveᴮ R

  open IsEquivalenceᴮ public


-- Bijection-indexed equivalence relations for simple (not-indexed) types
module SProps (F : Set) where

  open import Data.Unit
  open IProps ⊤ (λ _ → F) public
