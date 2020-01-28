import Generic.Container.Base as B

module Generic.Container.Valid
  (Label : Set)
  (Ty : Set)
  (Value : Ty → Set)
  (Validⱽ : ∀ {τ ℓ} → Value τ → B.Container Label Ty Value ℓ → Set) where

open B Label Ty Value
open import Data.Nat

Valid : ∀ {ℓ} → Container ℓ → Set
Valid C = ∀ {n τ} {v : Value τ} → n ↦ v ∈ C → Validⱽ v C
