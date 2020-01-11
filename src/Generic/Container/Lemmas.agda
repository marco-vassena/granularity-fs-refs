module Generic.Container.Lemmas (Label : Set) (Ty : Set) (Value : Ty → Set) where

open import Generic.Container.Base Label Ty Value

open import Relation.Binary.PropositionalEquality

-- TODO: haven't we proved this already somewhere?
inj-∈ : ∀ {ℓ n τ} {C : Container ℓ} {v₁ v₂ : Value τ} →
        n ↦ v₁ ∈ C → n ↦ v₂ ∈ C → v₁ ≡ v₂
inj-∈ Here Here = refl
inj-∈ (There x) (There y) = inj-∈ x y
