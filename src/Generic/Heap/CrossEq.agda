open import Lattice

open import Generic.CrossEq
import Generic.ICrossEq as G
open import Data.Unit

module Generic.Heap.CrossEq
  {{𝑳 : Lattice}}
  {Ty₁ : Set} {Ty₂ : Set}
  (𝑻 : CEq Ty₁ Ty₂)
  {Value₁ : Ty₁ → Set} {Value₂ : Ty₂ → Set}
  (𝑽 : G.ICEq ⊤ 𝑻 Value₁ Value₂)
  where

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Generic.Heap Ty₁ Value₁ as S
open import Generic.Heap Ty₂ Value₂ as T

open CEq 𝑻 renaming (⟦_⟧ to ⟦_⟧ᵗ)
open import Generic.ICrossEq ⊤ 𝑻
open ICEq 𝑽 renaming (⟦_⟧ to ⟦_⟧ⱽ)
-- TODO: first it seems that we pass an argument to ⟦_⟧ⱽ, but then we ignore it.
-- Can we provide a better interface?
open import Generic.Heap.Convert {Ty₁} {Ty₂} {Value₁} {Value₂} ⟦_⟧ᵗ (λ v → ⟦ v ⟧ⱽ tt)
  renaming (⟪_⟫ᴴ to ⟦_⟧ᴴ  )

-- Derive cross-language equivalence relation and lemmas for heaps.
open import Generic.Container.CrossEq 𝑻 ⊤ 𝑽
  renaming (_↓≈_ to _↓≈ᴴ_
           ; new-↓≈ to new-↓≈ᴴ
           ; ∥_∥-↓≈ to ∥_∥-↓≈ᴴ
           ; lookup-↓≈ to lookup-↓≈ᴴ
           ; write-↓≈ to write-↓≈ᴴ
           ; refl-↓≈ to refl-↓≈ᴴ
           ; nil to nilᴴ
           ; cons to consᴴ
           ; unlift-⟦_⟧∈ to unlift-⟦_⟧∈ᴴ
           ; unlift-∈′ to unlift-∈ᴴ′  -- TODO: FIX NAMES
           ) public
