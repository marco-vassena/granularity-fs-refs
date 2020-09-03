open import Lattice

open import Generic.CrossEq
import Generic.ICrossEq as G
open import Data.Unit

module Generic.PState.CrossEq
  {{𝑳 : Lattice}}
  {Ty₁ : Set} {Ty₂ : Set}
  (𝑻₁ : CEq Ty₁ Ty₂)
  (𝑻₂ : CEq Ty₁ Ty₂)
  {Valueˢ₁ : Ty₁ → Set} {Valueˢ₂ : Ty₂ → Set}
  {Valueᴴ₁ : Ty₁ → Set} {Valueᴴ₂ : Ty₂ → Set}
  (𝑽₁ : G.ICEq Label 𝑻₁ Valueˢ₁ Valueˢ₂)
  (𝑽₂ : G.ICEq ⊤ 𝑻₂ Valueᴴ₁ Valueᴴ₂)
  where

open import Generic.PState Ty₁ Ty₁ Valueˢ₁ Valueᴴ₁ as S
open import Generic.PState Ty₂ Ty₂ Valueˢ₂ Valueᴴ₂ as T

-- Rexport cross equivalence for store and heap
open import Generic.Store.CrossEq 𝑻₁ 𝑽₁ public
open import Generic.Heap.CrossEq 𝑻₂ 𝑽₂ public

open S.PState
open T.PState

record _↓≈ᴾ_  (p₁ : T.PState) (p₂ : S.PState) : Set where
  constructor ⟨_,_⟩
  field
    store-↓≈ˢ : store p₁ ↓≈ˢ store p₂
    heap-↓≈ᴴ : heap p₁ ↓≈ᴴ heap p₂

open CEq 𝑻₁ renaming (⟦_⟧ to ⟦_⟧₁ᵗ)
open CEq 𝑻₂ renaming (⟦_⟧ to ⟦_⟧₂ᵗ)
open G.ICEq 𝑽₁ renaming (⟦_⟧ to ⟦_⟧₁ⱽ)
open G.ICEq 𝑽₂ renaming (⟦_⟧ to ⟦_⟧₂ⱽ)

open import Generic.Store.Convert {Ty₁} {Ty₂} {Valueˢ₁} {Valueˢ₂} ⟦_⟧₁ᵗ ⟦_⟧₁ⱽ
  renaming (⟪_⟫ˢ to ⟦_⟧ˢ)

open import Generic.Heap.Convert {Ty₁} {Ty₂} {Valueᴴ₁} {Valueᴴ₂} ⟦_⟧₂ᵗ (λ v → ⟦ v ⟧₂ⱽ tt)
  renaming (⟪_⟫ᴴ to ⟦_⟧ᴴ)

⟦_⟧ᴾ : S.PState → T.PState
⟦ S.⟨ Σ , μ ⟩ ⟧ᴾ = T.⟨ ⟦ Σ ⟧ˢ , ⟦ μ ⟧ᴴ ⟩
  where

refl-↓≈ᴾ : ∀ (p : S.PState) → ⟦ p ⟧ᴾ ↓≈ᴾ p
refl-↓≈ᴾ S.⟨ Σ , μ ⟩ = ⟨ refl-↓≈ˢ Σ , refl-↓≈ᴴ μ ⟩
