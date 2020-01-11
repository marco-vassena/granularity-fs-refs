module Generic.Container.Lemmas (Label : Set) (Ty : Set) (Value : Ty → Set) where

open import Generic.Container.Base Label Ty Value

open import Relation.Binary.PropositionalEquality
open import Data.Product

-- For heterogeneous values.
inj-∈′ : ∀ {ℓ n τ₁ τ₂} {C : Container ℓ} {v₁ : Value τ₁} {v₂ : Value τ₂} →
        n ↦ v₁ ∈ C → n ↦ v₂ ∈ C → Σ (τ₁ ≡ τ₂) (λ {refl → v₁ ≡ v₂})
inj-∈′ Here Here = refl , refl
inj-∈′ (There x) (There y) with inj-∈′ x y
... | refl , refl = refl , refl

-- TODO: haven't we proved this already somewhere?
inj-∈ : ∀ {ℓ n τ} {C : Container ℓ} {v₁ v₂ : Value τ} →
        n ↦ v₁ ∈ C → n ↦ v₂ ∈ C → v₁ ≡ v₂
inj-∈ x y with inj-∈′ x y
... | refl , eq = eq
