import Generic.Container.Base as B
open import Data.Nat
open import Generic.Valid

module Generic.Container.Valid
  (Label : Set)
  (Ty : Set)
  (Value : Ty → Set)
  {{𝑽 : IsValid Value}} where

open IsValid 𝑽 renaming (Valid to Validⱽ ; ∥_∥ to ∥_∥ⱽ ; valid-≤ to valid-≤ⱽ)

 -- (Validⱽ : ∀ {τ} → ℕ → Value τ  → Set) where

open B Label Ty Value
open import Data.Nat
open import Generic.Container.Lemmas Label Ty Value
open import Data.Sum
open import Relation.Binary.PropositionalEquality
open import Data.Product

Validᶜ : ∀ {ℓ} → ℕ → Container ℓ → Set
Validᶜ n' C = ∀ {n τ} {v : Value τ} → n ↦ v ∈ C → Validⱽ n' v

tail-valid : ∀ {ℓ n τ} {v : Value τ} {C : Container ℓ} → Validᶜ n (v ∷ C) → Validᶜ n C
tail-valid valid ∈ = valid (There ∈)

read-valid : ∀ {ℓ τ n'} {v : Value τ} {C : Container ℓ} n → Validᶜ n C → n' ↦ v ∈ C → Validⱽ n v
read-valid n isV ∈₁ = isV ∈₁ -- Can be inlined

-- We need this just for memory.
snoc-valid : ∀ {ℓ τ} {v : Value τ} {C : Container ℓ} n → Validᶜ n C → Validⱽ n v → Validᶜ n (C ∷ᴿ v)
snoc-valid {v = v} {C = C} _ isV isVⱽ ∈₁ with split-lookup C v ∈₁
snoc-valid {v = v} {C} _ isV isVⱽ ∈₁ | inj₁ ∈₁′ = isV ∈₁′
snoc-valid {v = v} {C} _ isV isVⱽ ∈₁ | inj₂ (refl , refl) = isVⱽ

write-valid : ∀ {ℓ τ n'} {v : Value τ} {C C' : Container ℓ} n →
              Validᶜ n C → C' ≔ C [ n' ↦ v ] → Validⱽ n v → Validᶜ n C'
write-valid {v = v} {C} {C'} _ isV w isVⱽ ∈₁ with split-write w ∈₁
... | inj₁ ∈₁′ = isV ∈₁′
... | inj₂ (refl , refl) = isVⱽ

wken-validᶜ : ∀ {ℓ n n'} (C : Container ℓ) → n ≤ n' → Validᶜ n C → Validᶜ n' C
wken-validᶜ C ≤₁ isV ∈₁ = wken-valid _ ≤₁ (isV ∈₁)

∥_∥ᶜ : ∀ {ℓ} → Container ℓ → ℕ
∥ [] ∥ᶜ = 0
∥ v ∷ C ∥ᶜ = ∥ v ∥ⱽ ⊔ ∥ C ∥ᶜ

open import Data.Nat.Properties

valid-≤ᶜ : ∀ {ℓ n} (C : Container ℓ) → Validᶜ n C → ∥ C ∥ᶜ ≤ n
valid-≤ᶜ B.[] isV = z≤n
valid-≤ᶜ (v B.∷ C) isV = join-≤ (valid-≤ⱽ v (isV Here)) (valid-≤ᶜ C (tail-valid isV))

-- Need weakining to prove this, but not needed
-- postulate valid-⊆ : ∀ {ℓ n n'} {C : Container ℓ} → n ≤ n' → Validᶜ n C → Validᶜ n' C

instance
  IsValidᶜ : IsValid Container
  IsValidᶜ = record { Valid = Validᶜ
                    ; ∥_∥ = ∥_∥ᶜ
                    ; wken-valid = wken-validᶜ
                    ; valid-≤ = valid-≤ᶜ }
