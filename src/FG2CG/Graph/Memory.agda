open import Lattice

module FG2CG.Graph.Memory {{𝑳 : Lattice}} where

open import FG as FG
open import CG as CG
open import FG2CG.Syntax
open import Relation.Binary.PropositionalEquality

open import FG2CG.Graph.Types
open import FG2CG.Graph.Value

data Fg2Cgᴹ {ℓ} : FG.Memory ℓ → CG.Memory ℓ → Set where
  [] : Fg2Cgᴹ FG.[] CG.[]
  _∷_ : ∀ {τ τ' M₁ M₂ p} {r : FG.Raw τ} {v : CG.Value τ'}  → Fg2Cgᴿ p r v → Fg2Cgᴹ M₁ M₂ → Fg2Cgᴹ (r FG.∷ M₁) (v CG.∷ M₂)

mkFg2Cgᴹ : ∀ {ℓ} (M : FG.Memory ℓ) → Fg2Cgᴹ M ⟪ M ⟫ᴹ
mkFg2Cgᴹ FG.[] = []
mkFg2Cgᴹ (r FG.∷ M) = mkFg2Cgᴿ r ∷ mkFg2Cgᴹ M

≡-Fg2Cgᴹ : ∀ {ℓ} {M₁ : FG.Memory ℓ} {M₂ : CG.Memory ℓ} → Fg2Cgᴹ M₁ M₂ → M₂ ≡ ⟪ M₁ ⟫ᴹ
≡-Fg2Cgᴹ [] = refl
≡-Fg2Cgᴹ (_∷_ {p = p} r M) with ≡-MkTy′ p
... | refl = cong₂ CG._∷_ (≡-Fg2Cgᴿ r) (≡-Fg2Cgᴹ M)
