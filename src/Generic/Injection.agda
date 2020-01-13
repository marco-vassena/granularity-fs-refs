-- Partial injective functions

module Generic.Injection where

import Function as F
open import Relation.Binary.PropositionalEquality
open import Data.Maybe as M
open import Generic.PMap

-- Injective only where the function is defined.
Injectiveᴾ : {A B : Set} → A ⇀ B → Set
Injectiveᴾ f = ∀ {x y} → Is-just (f x) → Is-just (f y) → f x ≡ f y → x ≡ y

record Injectionᴾ (A B : Set) : Set where
  field
    to        : A ⇀ B
    injectiveᴾ : Injectiveᴾ to

id : ∀ {A} → Injectionᴾ A A
id = record { to = just ; injectiveᴾ = λ { x₁ x₂ refl → refl} }

open import Data.Unit
open import Data.Empty
open import Relation.Nullary

⊥-is-just : {A : Set} → ¬ Is-just {A = A} nothing
⊥-is-just ()

_∘_ : ∀ {A B C : Set} → Injectionᴾ B C → Injectionᴾ A B → Injectionᴾ A C
_∘_ {A} {B} {C} f g =
  record { to = to′
         ; injectiveᴾ = inj }

  where open Injectionᴾ
        open import Category.Monad
        open import Level
        open RawMonad {zero} M.monad
        open import Relation.Binary.PropositionalEquality

        to′ : A ⇀ C
        to′ = (to g) >=> (to f)

        inj : Injectiveᴾ to′
        inj {x} {y} p₁ p₂ eq  with to g x | inspect (to g) x | to g y | inspect (to g) y
               | (injectiveᴾ g) (back (to f) (to g) p₁) (back (to f) (to g) p₂)
        inj {x} {y} p₁ p₂ eq | just x₁ | [ eq₁ ] | just x₂ | [ eq₂ ] | eq'
          with to f x₁ | inspect (to f) x₁ | to f x₂ | inspect (to f) x₂
        inj {x} {y} p₁ p₂ eq | just x₁ | [ eq₁ ] | just x₂ | [ eq₂ ] | eq' | a | [ eq₃ ] | b | [ eq₄ ]
          rewrite eq | eq₁ | eq₂ = eq' (cong just (injectiveᴾ f p₁ p₂ (trans eq₃ (sym eq₄))))
        inj {x} {y} p₁ p₂ eq | just x₁ | [ eq₁ ] | nothing | [ eq₂ ] | eq' rewrite eq₂ = ⊥-elim (⊥-is-just p₂)
        inj {x} {y} p₁ p₂ eq | nothing | [ eq₁ ] | b | [ eq₂ ] | eq' rewrite eq₁ = ⊥-elim (⊥-is-just p₁)
