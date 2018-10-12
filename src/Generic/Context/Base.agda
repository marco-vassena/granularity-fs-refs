-- Generic context and basic proofs.

module Generic.Context.Base (Ty : Set)  where

open import Data.List using (List ; _∷_ ; [] ; _++_) public

-- Ctx is a generic typing context, i.e., a list of types.
Ctx : Set
Ctx = List Ty

-- (p : τ ∈ Γ) is a De Bruijn, i.e., an index that represents an
-- unnamed variable of type τ that identifies an element of the
-- context Γ by its position.

open import Relation.Binary.PropositionalEquality
import Data.List.Any as A
open import Data.List.Any.Membership (setoid Ty) using (_∈_ ) public
open import Function

pattern here = A.here refl
pattern there x = A.there x

-- Subset relation for contexts.
data _⊆_ : Ctx → Ctx → Set where
  base : [] ⊆ []
  cons : ∀ {τ Γ₁ Γ₂} → Γ₁ ⊆ Γ₂ → (τ ∷ Γ₁) ⊆ (τ ∷ Γ₂)
  drop : ∀ {τ Γ₁ Γ₂} → Γ₁ ⊆ Γ₂ → Γ₁ ⊆ (τ ∷ Γ₂)

infixr 2 _⊆_

-- ⊆ is reflexive
refl-⊆ : ∀ {Γ : Ctx} → Γ ⊆ Γ
refl-⊆ {[]} = base
refl-⊆ {τ ∷ Γ} = cons refl-⊆

-- Our inductive definition implies the standard definition of subset
-- (Data.List.Any.Membership), but it is more convenient, e.g., for
-- shrinking environments.
wken-∈ : ∀ {x} {Γ₁ : Ctx} {Γ₂ : Ctx} → Γ₁ ⊆ Γ₂ → x ∈ Γ₁ → x ∈ Γ₂
wken-∈ base ()
wken-∈ (cons p) here = here
wken-∈ (cons p) (there q) = there (wken-∈ p q)
wken-∈ (drop p) q = there (wken-∈ p q)

drop-⊆₂ : ∀ (Γ₁ Γ₂ : Ctx) -> Γ₁ ⊆ Γ₂ ++ Γ₁
drop-⊆₂ Γ₁ [] = refl-⊆
drop-⊆₂ Γ₁ (τ ∷ Γ₂) = drop (drop-⊆₂ Γ₁ Γ₂)
