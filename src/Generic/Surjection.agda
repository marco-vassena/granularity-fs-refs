-- {-# OPTIONS --allow-unsolved-metas #-}

module Generic.Surjection where

import Function as F
open import Relation.Binary.PropositionalEquality
open import Data.Maybe
open import Generic.PMap

-- f is the partial left-inverse of g if it inverts g where g x is defined
_LeftInverseOfᴾ_ : ∀ {A B} → A ⇀ B → B ⇀ A → Set
_LeftInverseOfᴾ_ f g = ∀ x → (p : Is-just (g x)) → f (to-witness p) ≡ just x


-- Partial right inverse
_RightInverseOfᴾ_ : ∀ {A B} → A ⇀ B → B ⇀ A → Set
f RightInverseOfᴾ g = g LeftInverseOfᴾ f

-- Surjective function
record Surjectiveᴾ {A B : Set} (to : A ⇀ B) : Set where
  field
    from             : B ⇀ A
    right-inverse-of : from RightInverseOfᴾ to

-- The type of surjective function
record Surjectionᴾ (A B : Set) : Set where
  field
    to : A ⇀ B
    surjectiveᴾ : Surjectiveᴾ to

  right-inverse : RightInverseᴾ A B
  right-inverse = record
    { to              = from
    ; from            = to
    ; left-inverse-of = right-inverse-of
    }


id : ∀ {A} → Surjectionᴾ A A
id = record { to = just
            ; surjectiveᴾ = record
              { from = just
              ; right-inverse-of = λ { x (just _) → refl } }
            }

_∘_ : ∀ {A B C : Set} → Surjectionᴾ B C → Surjectionᴾ A B → Surjectionᴾ A C
f ∘ g = record { to = to g >=> to f
               ; surjectiveᴾ = record
                 { from = (from sf) >=> (from sg)
                 ; right-inverse-of = rio } }
  where open Surjectionᴾ
        open import Category.Monad
        open import Level
        open RawMonad {zero} monad
        sf = (surjectiveᴾ f)
        sg = (surjectiveᴾ g)
        open Surjectiveᴾ
        -- open module S₁ = Surjectiveᴾ (surjectiveᴾ f)
        -- open module S₂ = Surjectiveᴾ (surjectiveᴾ g)

        rio : (from sf >=> from sg) RightInverseOfᴾ (to g >=> to f)
        rio x p = {!!}

-- Use EqReasoning. See the proof already made and adapt it.

 -- with from sf x | inspect (from sf) x
 --        rio x p | just x₁ | [ eq ] with to g (to-witness p) | inspect (to g) (to-witness p)
 --        rio x p | just x₁ | [ eq ] | just x₂ | eq' = {!!}
 --        rio x p | just x₁ | [ eq ] | nothing | [ eq' ] = {!!}
 --        rio x p | nothing | [ eq ] = {!!}

-- (to g (to-witness p)) | inspect (to g) (to-witness p)
--         ... | a | [ eq₁ ] = {!!}

 -- back (from sg) (from sf) p
 --        rio x p | a | [ eq₁ ] | r with (to f (to-witness r)) | inspect (to f) (to-witness r)
 --        ... | b | [ eq₂ ] with right-inverse-of sf x r
 --        rio x p | just x₁ | [ eq₁ ] | r | b | [ eq₂ ] | eq₃ = {!!}
 --        rio x p | nothing | [ eq₁ ] | r | b | [ eq₂ ] | eq₃ = {!!}

 -- with to g (to-witness p)
 --                | inspect (to g) (to-witness p)
 --                | from sf x | inspect (from sf) x | back (from sg) (from sf) p = ?
        -- ... | a | [ eq₁ ] | r | [ eq₂ ] | q = ?


-- with S₁.right-inverse-of x q
--         rio x p | just x₁ | [ eq₁ ] | r | [ eq₂ ] | q = {!!}
--         rio x p | nothing | [ eq₂ ] | r | [ eq₂ ] | q = {!!}

--  |  | S₁.right-inverse-of x (back S₂.from S₁.from p)
--         ... | a | r | eq = {!  !}
