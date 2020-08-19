module Generic.Valid (A : Set) (F : A → Set) where

open import Data.Nat

record IsValid (∥_∥ : ∀ {a} → F a → ℕ) : Set₁ where
  field Valid : ∀ {a} → ℕ → F a → Set
        wken-valid : ∀ {a n n'} (x : F a) → n ≤ n' → Valid n x → Valid n' x
        valid-≤ : ∀ {a n} (x : F a) → Valid n x → ∥ x ∥ ≤ n

-- TODO: remove
-- IsValid′ : (A : Set) → Set₁
-- IsValid′ A = IsValid {⊤} λ _ → A
--   where open import Data.Unit
