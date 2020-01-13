module Generic.LeftInverse where

-- import Function as F
open import Relation.Binary.PropositionalEquality as P
open import Data.Maybe hiding (Eq)
open import Generic.PMap hiding (_∈_) renaming (_∈′_ to _∈_)
open import Relation.Binary
-- import Relation.Binary.EqReasoning as EqReasoning
open import Generic.Injection hiding (id ; _∘_)
open import Data.Product
-- open import Function.Equality as Eq
--   using (_⟶_; _⟨$⟩_) renaming (_∘_ to _⟪∘⟫_)


-- f is the partial left-inverse of g if it inverts g where g x is defined
_LeftInverseOfᴾ_ : ∀ {A B} → A ⇀ B → B ⇀ A → Set
_LeftInverseOfᴾ_ f g = ∀ x y → (x , y) ∈ f → (y , x) ∈ g


-- Partial right inverse
_RightInverseOfᴾ_ : ∀ {A B} → A ⇀ B → B ⇀ A → Set
f RightInverseOfᴾ g = g LeftInverseOfᴾ f

-- The set of all left inverses.
record LeftInverse (A : Set) (B : Set) : Set  where
  field
    to              : A ⇀ B
    from            : B ⇀ A
    left-inverse-of : from LeftInverseOfᴾ to

  open ≡-Reasoning {A = A}

  injectiveᴾ : Injectiveᴾ to
  injectiveᴾ {x} {y} a b eq =
    begin
      x ≡⟨ {!left-inverse-of ? ?!} ⟩
      to-witness {!b!} ≡⟨ {!!} ⟩
      y ∎

 -- begin
 --    x                    ≈⟨ F.sym ? ⟩ -- (left-inverse-of x)
 --    ?  ≈⟨ Eq.cong from eq ⟩ -- (to y)
 --    from ?  ≈⟨ left-inverse-of y ⟩ -- (to y)
 --    y                    ∎

  injection : Injectionᴾ A B
  injection = record { to = to; injectiveᴾ = injectiveᴾ }

  -- equivalence : Equivalence From To
  -- equivalence = record
  --   { to   = to
  --   ; from = from
  --   }

  to-from : ∀ {x y} → to x ≡ just y → from y ≡ just x
  to-from {x} {y} to-x≈y = {!!}
-- begin
--     from ⟨$⟩ y           ≈⟨ Eq.cong from (T.sym to-x≈y) ⟩
--     from ⟨$⟩ (to ⟨$⟩ x)  ≈⟨ left-inverse-of x ⟩
--     x                    ∎

-- The set of all right inverses between two setoids.

RightInverse : (A B : Set) → Set
RightInverse A B = LeftInverse A B

-- The set of all left inverses from one set to another. (Read A ↞ B
-- as "surjection from B to A".)

infix 3 _↞_

_↞_ : Set → Set → Set
A ↞ B = LeftInverse A B

-- Identity and composition.

id : ∀ {A : Set} → LeftInverse A A
id {A} = {!!}
-- record
--   { to              = Eq.id
--   ; from            = Eq.id
--   ; left-inverse-of = λ _ → Setoid.refl A
--   }

-- infixr 9 _∘_

-- _∘_ : ∀ {f₁ f₂ m₁ m₂ t₁ t₂}
--         {F : Setoid f₁ f₂} {M : Setoid m₁ m₂} {T : Setoid t₁ t₂} →
--       LeftInverse M T → LeftInverse F M → LeftInverse F T
-- _∘_ {F = F} f g = record
--   { to              = to   f ⟪∘⟫ to   g
--   ; from            = from g ⟪∘⟫ from f
--   ; left-inverse-of = λ x → begin
--       from g ⟨$⟩ (from f ⟨$⟩ (to f ⟨$⟩ (to g ⟨$⟩ x)))  ≈⟨ Eq.cong (from g) (left-inverse-of f (to g ⟨$⟩ x)) ⟩
--       from g ⟨$⟩ (to g ⟨$⟩ x)                          ≈⟨ left-inverse-of g x ⟩
--       x                                                ∎
--   }
--   where
--   open LeftInverse
--   open EqReasoning F
