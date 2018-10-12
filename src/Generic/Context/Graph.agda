-- This module defines the graph of the function for contexts, given
-- the graph of type transformation.

open import Generic.Graph

module Generic.Context.Graph {Ty₁ Ty₂ : Set} {⟪_⟫ : Ty₁ → Ty₂} (𝑮 : Graph ⟪_⟫)  where

open import Generic.Context Ty₁ as S
open import Generic.Context Ty₂ as T

open import Generic.Context.Convert {Ty₁} {Ty₂} ⟪_⟫
open import Relation.Binary.PropositionalEquality as P

open Graph 𝑮 renaming (P to S2Tᵗ ; ⌜_⌝ to mkS2Tᵗ ; ⌞_⌟ to ≡-S2Tᵗ)

--------------------------------------------------------------------------------

-- Graph of context translation ⟪·⟫ᶜ
data S2Tᶜ : S.Ctx → T.Ctx → Set where
  instance
    [] : S2Tᶜ S.[] T.[]
    _∷_ : ∀ {τ₁ τ₂ Γ₁ Γ₂} → S2Tᵗ τ₁ τ₂ → S2Tᶜ Γ₁ Γ₂ → S2Tᶜ (τ₁ S.∷ Γ₁) (τ₂ T.∷ Γ₂)

instance
  mkS2Tᶜ : ∀ Γ → S2Tᶜ Γ ⟪ Γ ⟫ᶜ
  mkS2Tᶜ S.[] = []
  mkS2Tᶜ (τ S.∷ Γ) = mkS2Tᵗ τ ∷ mkS2Tᶜ Γ

≡-S2Tᶜ : ∀ {Γ Γ'} → S2Tᶜ Γ Γ' → Γ' ≡ ⟪ Γ ⟫ᶜ
≡-S2Tᶜ [] = refl
≡-S2Tᶜ (x ∷ x₁) = cong₂ T._∷_ (≡-S2Tᵗ x) (≡-S2Tᶜ x₁)

open import Function.Injection as F
open import Function.Equality using (_⟶_)

𝑭 : (setoid Ty₁) ⟶ (setoid Ty₂)
𝑭 = record { _⟨$⟩_ = ⟪_⟫ ; cong = λ { refl → refl } }

module Injective (𝑰 : F.Injective 𝑭) where

  inj-S2Tᶜ : ∀ {Γ₁ Γ₂ Γ₃} → S2Tᶜ Γ₁ Γ₃ → S2Tᶜ Γ₂ Γ₃ → Γ₁ ≡ Γ₂
  inj-S2Tᶜ [] [] = refl
  inj-S2Tᶜ (p₁ ∷ x) (p₂ ∷ y)
    rewrite 𝑰 (trans (sym (≡-S2Tᵗ p₁)) (≡-S2Tᵗ p₂)) | inj-S2Tᶜ x y = refl

  inj-⟪_⟫ᶜ : ∀ {Γ₁ Γ₂} → ⟪ Γ₁ ⟫ᶜ ≡ ⟪ Γ₂ ⟫ᶜ → Γ₁ ≡ Γ₂
  inj-⟪_⟫ᶜ {Γ₁} {Γ₂} eq with mkS2Tᶜ Γ₁ | mkS2Tᶜ Γ₂
  ... | x | y rewrite eq = inj-S2Tᶜ x y

--------------------------------------------------------------------------------

-- Graph of variable transformation ⟪·⟫∈
data S2T-∈ {τ τ'} (p : S2Tᵗ τ τ') : ∀ {Γ Γ'} (c : S2Tᶜ Γ Γ') → τ S.∈ Γ → τ' T.∈ Γ' → Set where
  Here : ∀ {Γ Γ'} {c : S2Tᶜ Γ Γ'} → S2T-∈ p (p ∷ c) S.here T.here
  There : ∀ {Γ Γ' τ₁ τ₁'} {p' : S2Tᵗ τ₁ τ₁'} {c : S2Tᶜ Γ Γ'} {x : τ S.∈ Γ} {y : τ' T.∈ Γ'} →
            S2T-∈ p c x y →
            S2T-∈ p (p' ∷ c) (S.there x) (T.there y)

mkS2T-∈ : ∀ {τ Γ} → (x : τ S.∈ Γ) → S2T-∈ (mkS2Tᵗ τ) (mkS2Tᶜ Γ) x ⟪ x ⟫∈
mkS2T-∈ S.here = Here
mkS2T-∈ (S.there x) = There (mkS2T-∈ x)

≡-S2T-∈ : ∀ {τ Γ p c y} {x : τ S.∈ Γ} → S2T-∈ p c x y → y ≡ ⟪ x ⟫∈
≡-S2T-∈ Here = refl
≡-S2T-∈ (There x) rewrite ≡-S2T-∈ x = refl

-- Injectivity.
inj-S2T-∈ : ∀ {τ₁ τ₂ Γ₁ Γ₂ p₁ p₂ c₁ c₂} {x₁ x₂ : τ₁ S.∈ Γ₁} {y : τ₂ T.∈ Γ₂} →
              S2T-∈ p₁ c₁ x₁ y →
              S2T-∈ p₂ c₂ x₂ y →
              x₁ ≡ x₂
inj-S2T-∈ Here Here = refl
inj-S2T-∈ (There a) (There b) = cong S.there (inj-S2T-∈ a b)

inj-⟪_⟫∈ : ∀ {τ Γ} {x y : τ S.∈ Γ} → ⟪ x ⟫∈ ≡ ⟪ y ⟫∈ → x ≡ y
inj-⟪_⟫∈ {x = x} {y} eq with mkS2T-∈ x | mkS2T-∈ y
... | a | b rewrite eq = inj-S2T-∈ a b

--------------------------------------------------------------------------------

-- Graph of subset transformation ⟪·⟫⊆
data S2T-⊆ : ∀ {Γ₁ Γ₂ Γ₁' Γ₂'} → S2Tᶜ Γ₁ Γ₁' → S2Tᶜ Γ₂ Γ₂' → Γ₁ S.⊆ Γ₂ → Γ₁' T.⊆ Γ₂' → Set where

  base : S2T-⊆ [] [] S.base T.base

  cons : ∀ {τ τ' Γ₁ Γ₂ Γ₁' Γ₂'} {c₁ : S2Tᶜ Γ₁ Γ₁'} {c₂ : S2Tᶜ Γ₂ Γ₂'} →
           {p : S2Tᵗ τ τ'} {x : Γ₁ S.⊆ Γ₂} {y : Γ₁' T.⊆ Γ₂'} →
            S2T-⊆ c₁ c₂ x y →
            S2T-⊆ (p ∷ c₁) (p ∷ c₂) (S.cons x) (T.cons y)

  drop : ∀ {τ τ' Γ₁ Γ₂ Γ₁' Γ₂'} {c₁ : S2Tᶜ Γ₁ Γ₁'} {c₂ : S2Tᶜ Γ₂ Γ₂'} →
           {p : S2Tᵗ τ τ'} {x : Γ₁ S.⊆ Γ₂} {y : Γ₁' T.⊆ Γ₂'} →
            S2T-⊆ c₁ c₂ x y →
            S2T-⊆ c₁ (p ∷ c₂) (S.drop x) (T.drop y)

mkS2T-⊆ : ∀ {Γ₁ Γ₂} → (x : Γ₁ S.⊆ Γ₂) → S2T-⊆ (mkS2Tᶜ _) (mkS2Tᶜ _) x ⟪ x ⟫⊆
mkS2T-⊆ S.base = base
mkS2T-⊆ (S.cons x) = cons (mkS2T-⊆ x)
mkS2T-⊆ (S.drop x) = drop (mkS2T-⊆ x)

≡-S2T-⊆ : ∀ {Γ₁ Γ₂ y c₁ c₂} {x : Γ₁ S.⊆ Γ₂} → S2T-⊆ c₁ c₂ x y → y ≡ ⟪ x ⟫⊆
≡-S2T-⊆ base = refl
≡-S2T-⊆ (cons x) rewrite ≡-S2T-⊆ x = refl
≡-S2T-⊆ (drop x) rewrite ≡-S2T-⊆ x = refl

-- Injective
inj-S2T-⊆ : ∀ {Γ₁ Γ₂ Γ₃ Γ₄ c₁ c₂ c₃ c₄} {x₁ x₂ : Γ₁ S.⊆ Γ₂} {y : Γ₃ T.⊆ Γ₄} →
               S2T-⊆ c₁ c₂ x₁ y →
               S2T-⊆ c₃ c₄ x₂ y →
               x₁ ≡ x₂
inj-S2T-⊆ base base = refl
inj-S2T-⊆ (cons a) (cons b) = cong S.cons (inj-S2T-⊆ a b)
inj-S2T-⊆ (drop a) (drop b) = cong S.drop (inj-S2T-⊆ a b)

inj-⟪_⟫⊆ : ∀ {Γ₁ Γ₂} {x₁ x₂ : Γ₁ S.⊆ Γ₂} → ⟪ x₁ ⟫⊆ ≡ ⟪ x₂ ⟫⊆ → x₁ ≡ x₂
inj-⟪_⟫⊆ {x₁ = x₁} {x₂} eq with mkS2T-⊆ x₁ | mkS2T-⊆ x₂
... | a | b rewrite eq = inj-S2T-⊆ a b

--------------------------------------------------------------------------------

Unique : (Ty₁ → Ty₂ → Set) → Set
Unique P = ∀ {a b} → (x y : P a b) → x ≡ y

module Unique (!-S2Tᵗ : Unique S2Tᵗ) where

  !-S2Tᶜ : ∀ {Γ Γ'} → (x y : S2Tᶜ Γ Γ') → x ≡ y
  !-S2Tᶜ [] [] = refl
  !-S2Tᶜ (p₁ ∷ c₁) (p₂ ∷ c₂) = cong₂ _∷_ (!-S2Tᵗ p₁ p₂) (!-S2Tᶜ c₁ c₂ )
