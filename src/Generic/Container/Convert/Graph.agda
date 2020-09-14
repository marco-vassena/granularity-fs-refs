open import Lattice
open import Generic.Graph

open import Generic.IGraph

module Generic.Container.Convert.Graph
  {{𝑳 : Lattice}}
  (Label : Set)
  {Ty₁ Ty₂ : Set}
  {Value₁ : Ty₁ → Set}
  {Value₂ : Ty₂ → Set}
  {⟪_⟫ᵗ : Ty₁ → Ty₂}
  {⟪_⟫ⱽ : ∀ {τ} → Value₁ τ → Value₂ ⟪ τ ⟫ᵗ}
  (𝑮ᵗ : Graph ⟪_⟫ᵗ)
  (𝑮ⱽ : IGraph {Ty₁} {Ty₂} 𝑮ᵗ {Value₁} {Value₂}  ⟪_⟫ⱽ) where

open import Generic.Container.Base Label as B using ([] ; _∷_)
private module S = B Ty₁ Value₁
private module T = B Ty₂ Value₂

open Graph 𝑮ᵗ renaming (P to Graphᵗ ; ⌞_⌟ to ⌞_⌟ᵗ ; ⌜_⌝ to ⌜_⌝ᵗ)
open IGraph 𝑮ⱽ renaming (R to Graphⱽ)

data Graphᶜ {ℓ} : S.Container ℓ → T.Container ℓ → Set where
  nil : Graphᶜ [] []
  cons : ∀ {C₁ C₂ τ₁ τ₂} {v₁ : Value₁ τ₁} {v₂ : Value₂ τ₂} (p : Graphᵗ τ₁ τ₂) →
          Graphⱽ p v₁ v₂ → Graphᶜ C₁ C₂ → Graphᶜ (v₁ ∷ C₁) (v₂ ∷ C₂)

open import Data.Product
open import Function
open import Generic.Container.Convert.Base Label {Ty₁} {Ty₂} {Value₁} {Value₂}  ⟪_⟫ᵗ (flip $ const ⟪_⟫ⱽ)
open import Relation.Binary.PropositionalEquality

mkGraphᶜ : ∀ {ℓ} (C : S.Container ℓ) → Graphᶜ C ⟪ C ⟫ᶜ
mkGraphᶜ [] = nil
mkGraphᶜ (v ∷ C) = cons _ ⌜ v ⌝  (mkGraphᶜ C)

≡-Graphᶜ : ∀ {ℓ} {C : S.Container ℓ} {C' : T.Container ℓ} → Graphᶜ C C' → C' ≡ ⟪ C ⟫ᶜ
≡-Graphᶜ nil = refl
≡-Graphᶜ (cons p x y) with ⌞ p ⌟ᵗ
... | refl rewrite ⌞ x ⌟ =  cong (_ ∷_) (≡-Graphᶜ y)

private unlift-⟪_⟫∈′ : ∀ {ℓ τ₂ n} {v₂ : Value₂ τ₂} {C₁ : S.Container ℓ} {C₂ : T.Container ℓ} →
               n T.↦ v₂ ∈ C₂ → Graphᶜ C₁ C₂ →
               ∃ (λ τ₁ → ∃ (λ p → Σ (Value₁ τ₁) (λ v₁ →  n S.↦ v₁ ∈ C₁ × Graphⱽ p v₁ v₂)))
unlift-⟪ T.Here ⟫∈′ (cons _ v _) = _ , _ , _ , S.Here , v
unlift-⟪ T.There ∈₂ ⟫∈′ (cons _ _ G) with unlift-⟪ ∈₂ ⟫∈′ G
... | _ , _ , _ , ∈₁ , v = _ , _ , _ , S.There ∈₁ , v

-- This should be added as an assumption somewhere, but I am not sure where now.
-- Maybe graph?
-- private postulate inj-⟪_⟫ᵗ : ∀ {τ₁ τ₂} → ⟪ τ₁ ⟫ᵗ ≡ ⟪ τ₂ ⟫ᵗ → τ₁ ≡ τ₂
-- private postulate inj-⟪_⟫ⱽ : ∀ {τ} {v₁ v₂ : Value₁ τ}  → ⟪ v₁ ⟫ⱽ ≡ ⟪ v₂ ⟫ⱽ → v₁ ≡ v₂

-- Seems not needed
-- unlift-⟪_⟫∈ : ∀ {ℓ τ n} {v : Value₁ τ} {M : S.Container ℓ} → n T.↦ ⟪ v ⟫ⱽ ∈ ⟪ M ⟫ᶜ → n S.↦ v ∈ M
-- unlift-⟪_⟫∈ {_} {τ'} ∈₂ with unlift-⟪ ∈₂ ⟫∈′ (mkGraphᶜ _ )
-- ... | τ , p , v , ∈₁ , g with inj-⟪ ⌞ p ⌟ᵗ ⟫ᵗ
-- ... | refl rewrite inj-⟪ ⌞ g ⌟ ⟫ⱽ = ∈₁

unlift-⟪_⟫∈ : ∀ {ℓ τ₂ n} {v₂ : Value₂ τ₂} {C₁ : S.Container ℓ} →
                n T.↦ v₂ ∈ ⟪ C₁ ⟫ᶜ →
               ∃ (λ τ₁ → Σ (Value₁ τ₁)
                    (λ v₁ → (n S.↦ v₁ ∈ C₁) × Σ (τ₂ ≡ ⟪ τ₁ ⟫ᵗ) (λ { refl → (v₂ ≡ ⟪ v₁ ⟫ⱽ) })))
unlift-⟪_⟫∈ ∈₂ with unlift-⟪ ∈₂ ⟫∈′ (mkGraphᶜ _ )
... | τ , p , v , ∈₁ , g with  ⌞ p ⌟ᵗ
... | refl = τ , v , ∈₁ , refl , ⌞ g ⌟
--                 Σ (τ₂ ≡ ⟪ τ₁ ⟫  (λ v₁ → v₂ ≡ ⟪ v₁ ⟫ⱽ × n S.↦ v₂ ∈ ⟪ C₁ ⟫ᶜ)
-- unlift-⟪_⟫∈′′ = {!!}
