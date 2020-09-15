import Lattice as L

open import Generic.CrossEq
import Generic.ICrossEq as G

module Generic.Container.CrossEq
  {{𝑳 : L.Lattice}}
  {Ty₁ : Set} {Ty₂ : Set}
  (𝑻 : CEq Ty₁ Ty₂)
  (Label : Set)
  {Value₁ : Ty₁ → Set} {Value₂ : Ty₂ → Set}
  (𝑽 : G.ICEq Label 𝑻 Value₁ Value₂)
  where

open CEq 𝑻 renaming ( _↓≈_ to _↓≈ᵗ_
                    ; ⟦_⟧ to ⟦_⟧ᵗ
                    ; refl-↓≈ to refl-↓≈ᵗ)
open import Generic.ICrossEq Label 𝑻

open ICEq 𝑽 renaming ( _↓≈⟨_⟩_ to _↓≈⟨_⟩ⱽ_
                     ; _↓≈⟨_,_⟩_ to _↓≈⟨_,_⟩ⱽ_
                     ; ⟦_⟧ to ⟦_⟧ⱽ)

import Generic.Container

open import Generic.Container Label Ty₁ Value₁ as S
open import Generic.Container Label Ty₂ Value₂ as T

data _↓≈_ {ℓ} : T.Container ℓ → S.Container ℓ → Set where
  nil : T.[] ↓≈ S.[]
  cons : ∀ {C₁ C₂ τ₁ τ₂} {v₁ : Value₁ τ₁} {v₂ : Value₂ τ₂} →
           (τ≈ : τ₂ ↓≈ᵗ τ₁) → v₂ ↓≈⟨ ℓ , τ≈ ⟩ⱽ v₁ → C₂ ↓≈ C₁ → (v₂ T.∷ C₂) ↓≈ (v₁ S.∷ C₁)

open import Generic.Container.Convert Label {Ty₁} {Ty₂} {Value₁} {Value₂}  ⟦_⟧ᵗ ⟦_⟧ⱽ
  renaming (⟪_⟫ᶜ to ⟦_⟧ᶜ)

refl-↓≈ : ∀ {ℓ} → (C : S.Container ℓ) → ⟦ C ⟧ᶜ ↓≈ C
refl-↓≈ S.[] = nil
refl-↓≈ (v S.∷ M) = cons _ (refl-↓≈⟨ _ ⟩ v) (refl-↓≈ M)


-- Extending related memories with related values gives related memoryes.
new-↓≈ : ∀ {ℓ τ} {M : T.Container ℓ} {M' : S.Container ℓ} {v₁ : Value₁ τ} {v₂ : Value₂ ⟦ τ ⟧ᵗ} →
        let instance _ = refl-↓≈ᵗ τ in
           M ↓≈ M' →
           v₂ ↓≈⟨ ℓ ⟩ⱽ v₁ →
           (M T.∷ᴿ v₂) ↓≈ (M' S.∷ᴿ v₁)
new-↓≈ nil v≈ = cons _ v≈ nil
new-↓≈ (cons τ≈ v≈' M≈) v≈ = cons τ≈ v≈' (new-↓≈ M≈ v≈)

open import Relation.Binary.PropositionalEquality
open import Data.Product renaming (_,_ to _∧_)

∥_∥-↓≈ : ∀ {ℓ} {C : T.Container ℓ} {C' : S.Container ℓ} → C ↓≈ C' → T.∥ C ∥ ≡ S.∥ C' ∥
∥ nil ∥-↓≈ = refl
∥ cons _ _ C≈ ∥-↓≈ rewrite ∥ C≈ ∥-↓≈ = refl

lookup-↓≈ : ∀ {n ℓ τ} {v₁ : Value₁ τ} {C : T.Container ℓ} {C' : S.Container ℓ} →
                 n S.↦ v₁ ∈ C' →
                 C ↓≈ C' →
                 Σ (Value₂ ⟦ τ ⟧ᵗ) (λ v₂ → (n T.↦ v₂ ∈ C) × (v₂ ↓≈⟨ ℓ , refl-↓≈ᵗ _ ⟩ⱽ v₁))
lookup-↓≈ S.Here (cons τ≈ v≈ _) with ⌞ τ≈  ⌟
... | refl rewrite !-↓≈ τ≈ (refl-↓≈ᵗ _) =  _ ∧ T.Here ∧ v≈
lookup-↓≈ (S.There ∈₁) (cons _ _ C≈) with lookup-↓≈ ∈₁ C≈
... | _ ∧ ∈₂ ∧ v≈ = _ ∧ T.There ∈₂ ∧ v≈

unlift-⟦_⟧∈  : ∀ {n ℓ τ₂} {v₂ : Value₂ τ₂} {C' : S.Container ℓ} →
               n T.↦ v₂ ∈ ⟦ C' ⟧ᶜ →
               ⟦ C' ⟧ᶜ ↓≈ C' →
               ∃ (λ τ₁ → Σ ( (Value₁ τ₁) × (τ₂ ≡ ⟦ τ₁ ⟧ᵗ) )
                 (λ { (v₁ ∧ refl)  → (n S.↦ v₁ ∈ C') × v₂ ≡ ⟦ v₁ ⟧ⱽ ℓ } ))
unlift-⟦_⟧∈ () nil
unlift-⟦_⟧∈ T.Here (cons {v₁ = v₁} τ≈ x x₁) = _ ∧ (v₁ ∧ refl) ∧ S.Here ∧ refl
unlift-⟦_⟧∈ (T.There ∈₁) (cons τ≈ x C≈) with unlift-⟦ ∈₁ ⟧∈ C≈
... | τ ∧ (v₁ ∧ refl) ∧ ∈₁′ ∧ refl =  τ ∧ (v₁ ∧ refl) ∧ (S.There ∈₁′) ∧ refl

write-↓≈ : ∀ {n ℓ τ} {v₁ : Value₁ τ} {v₂ : Value₂ ⟦ τ ⟧ᵗ} {C₁ : T.Container ℓ} {C₂ C₂' : S.Container ℓ} →
             v₂ ↓≈⟨ ℓ , refl-↓≈ᵗ _ ⟩ⱽ v₁ →
             C₂' S.≔ C₂ [ n ↦ v₁ ] →
             C₁ ↓≈ C₂ →
             ∃ (λ C₁' → C₁' T.≔ C₁ [ n ↦ v₂ ] × C₁' ↓≈ C₂')
write-↓≈ v≈′ S.Here (cons τ≈ v≈ C≈) with ⌞ τ≈  ⌟
... | refl rewrite !-↓≈ τ≈ (refl-↓≈ᵗ _) = _ ∧ T.Here ∧ (cons _ v≈′ C≈)
write-↓≈ v≈′ (S.There C≔) (cons _ v≈ C≈) with write-↓≈ v≈′ C≔ C≈
... | _ ∧ ∈₂ ∧ C≈′ = _ ∧ T.There ∈₂ ∧ cons _ v≈ C≈′
