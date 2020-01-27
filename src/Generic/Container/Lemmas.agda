module Generic.Container.Lemmas (Label : Set) (Ty : Set) (Value : Ty → Set) where

open import Generic.Container.Base Label Ty Value

open import Relation.Binary.PropositionalEquality
open import Data.Product
open import Function

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

open import Lattice -- Here just because it defines the pragma {#- BUILTIN REWRITE #-}
open import Data.Nat

∥snoc∥ : ∀ {ℓ τ} (C : Container ℓ) (v : Value τ) → ∥ C ∷ᴿ v ∥ ≡ suc ∥ C ∥
∥snoc∥ [] v = refl
∥snoc∥ (x ∷ C) v = cong suc (∥snoc∥ C v)

{-# REWRITE ∥snoc∥ #-}

<-∈ : ∀ {n ℓ} {C : Container ℓ} → n < ∥ C ∥ → n ∈ C
<-∈ {C = []} ()
<-∈ {zero} {C = v ∷ C} (s≤s x) = _ , v , Here
<-∈ {suc n} {C = v ∷ C} (s≤s x) = map id (map id There) (<-∈ x)
