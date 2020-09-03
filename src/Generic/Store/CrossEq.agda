open import Lattice

open import Generic.CrossEq
import Generic.ICrossEq as G

module Generic.Store.CrossEq
  {{𝑳 : Lattice}}
  {Ty₁ : Set} {Ty₂ : Set}
  (𝑻 : CEq Ty₁ Ty₂)
  {Value₁ : Ty₁ → Set} {Value₂ : Ty₂ → Set}
  (𝑽 : G.ICEq Label 𝑻 Value₁ Value₂)
  where

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Generic.Store Ty₁ Value₁ as S
open import Generic.Store Ty₂ Value₂ as T

open CEq 𝑻 renaming (⟦_⟧ to ⟦_⟧ᵗ)
open import Generic.ICrossEq Label 𝑻
open ICEq 𝑽 renaming (⟦_⟧ to ⟦_⟧ⱽ)
open import Generic.Store.Convert {Ty₁} {Ty₂} {Value₁} {Value₂} ⟦_⟧ᵗ ⟦_⟧ⱽ
  renaming (⟪_⟫ˢ to ⟦_⟧ˢ  )

-- Derive cross-language equivalence relation and lemmas for memories.
open import Generic.Container.CrossEq 𝑻 Label 𝑽
  renaming (_↓≈_ to _↓≈ᴹ_
           ; new-↓≈ to new-↓≈ᴹ
           ; ∥_∥-↓≈ to ∥_∥-↓≈ᴹ
           ; lookup-↓≈ to lookup-↓≈ᴹ
           ; write-↓≈ to write-↓≈ᴹ
           ; refl-↓≈ to refl-↓≈ᴹ) public

-- Stores
_↓≈ˢ_ : T.Store → S.Store → Set
Σ ↓≈ˢ Σ' = ∀ (ℓ : Label) → (Σ ℓ) ↓≈ᴹ (Σ' ℓ)

infixr 2 _↓≈ˢ_

-- Updating related stores with related memory gives related stores
update-↓≈ˢ : ∀ {ℓ Σ Σ'} {M : T.Memory ℓ} {M' : S.Memory ℓ} →
            Σ ↓≈ˢ Σ' → M ↓≈ᴹ M' →
            (Σ T.[ ℓ ↦ M ]ˢ) ↓≈ˢ (Σ' S.[ ℓ ↦ M' ]ˢ)
update-↓≈ˢ {ℓ} Σ≈ M≈ ℓ' with ℓ ≟ ℓ'
... | yes refl = M≈
... | no ℓ≢ℓ' = Σ≈ ℓ'

refl-↓≈ˢ : ∀ (Σ : S.Store) → ⟦ Σ ⟧ˢ ↓≈ˢ Σ
refl-↓≈ˢ Σ = λ ℓ → refl-↓≈ᴹ (Σ ℓ)
