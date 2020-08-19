module Generic.Valid where

open import Data.Nat

record IsValid {A : Set} (F : A → Set) : Set₁ where
  field Valid : ∀ {a} → ℕ → F a → Set
        ∥_∥ : ∀ {a} → F a → ℕ
        wken-valid : ∀ {a n n'} (x : F a) → n ≤ n' → Valid n x → Valid n' x
        valid-≤ : ∀ {a n} (x : F a) → Valid n x → ∥ x ∥ ≤ n

IsValid′ : (A : Set) → Set₁
IsValid′ A = IsValid {⊤} λ _ → A
  where open import Data.Unit
