import Generic.Container.Base as B
open import Data.Nat

module Generic.Container.Valid
  (Label : Set)
  (Ty : Set)
  (Value : Ty → Set)
  (Validⱽ : ∀ {τ} → ℕ → Value τ  → Set) where

open B Label Ty Value
open import Data.Nat

Valid : ∀ {ℓ} → ℕ → Container ℓ → Set
Valid n' C = ∀ {n τ} {v : Value τ} → n ↦ v ∈ C → Validⱽ n' v

tail-valid : ∀ {ℓ n τ} {v : Value τ} {C : Container ℓ} → Valid n (v ∷ C) → Valid n C
tail-valid valid ∈ = valid (There ∈)
  where open import Generic.Container.Lemmas Label Ty Value

read-valid : ∀ {ℓ τ n'} {v : Value τ} {C : Container ℓ} n → Valid n C → n' ↦ v ∈ C → Validⱽ n v
read-valid n isV ∈₁ = isV ∈₁ -- Can be inlined

-- We need this just for memory
postulate snoc-valid : ∀ {ℓ τ} {v : Value τ} {C : Container ℓ} n → Valid n C → Validⱽ n v → Valid n (C ∷ᴿ v)

postulate write-valid : ∀ {ℓ τ n'} {v : Value τ} {C C' : Container ℓ} n →
              Valid n C → C' ≔ C [ n' ↦ v ] → Validⱽ n v → Valid n C'
-- write-valid = ?

-- Need weakining to prove this, but not needed
-- postulate valid-⊆ : ∀ {ℓ n n'} {C : Container ℓ} → n ≤ n' → Valid n C → Valid n' C
