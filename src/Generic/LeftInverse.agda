{-# OPTIONS --allow-unsolved-metas #-}

module Generic.LeftInverse where

-- import Function as F
open import Relation.Binary.PropositionalEquality as P
open import Data.Maybe hiding (Eq)
open import Generic.PMap
open import Relation.Binary
-- import Relation.Binary.EqReasoning as EqReasoning
open import Generic.Injection hiding (id ; _∘_)
open import Data.Product
-- open import Function.Equality as Eq
--   using (_⟶_; _⟨$⟩_) renaming (_∘_ to _⟪∘⟫_)


-- f is the partial left-inverse of g if it inverts g where g x is defined
_LeftInverseOfᴾ_ : ∀ {A B} → A ⇀ B → B ⇀ A → Set
_LeftInverseOfᴾ_ f g = ∀ {x y} → (x , y) ∈ f → (y , x) ∈ g


-- Partial right inverse
_RightInverseOfᴾ_ : ∀ {A B} → A ⇀ B → B ⇀ A → Set
f RightInverseOfᴾ g = g LeftInverseOfᴾ f

-- The set of all left inverses.
record LeftInverseᴾ (A : Set) (B : Set) : Set  where
  field
    to              : A ⇀ B
    from            : B ⇀ A
    left-inverse-of : from LeftInverseOfᴾ to

--    from′ :

  -- fromᴿ : ∀ (a : A) → a ∈ᴿ from → B
  -- fromᴿ a (b , _) = b

  -- fromᴰ : ∀ (b : B) → b ∈ᴰ from → A
  -- fromᴰ b (a , _) = a

  -- from′′ : ∀ (b : B) → b ∈ᴿ to → A
  -- from′′ b (a , eq) = a


  -- fromᴿ : ∀ (b : B) → (x : b ∈ᴿ to) → Σ A (λ a → a ≡ proj₁ x)
  -- fromᴿ b (a , just refl eq ) = (a , refl)

  -- lemma-from′ : ∀ {b : B} (x : b ∈ᴿ to) → just (from′′ b x) ≡ from b
  -- lemma-from′ {b} (a' , g) with from b | inspect from b
  -- lemma-from′ {b} (a' , just {a' = a'''} x x₁) | a'' | [ eq ] = {!!}


  -- toᴰ : ∀ (a : A) → a ∈ᴰ to → B
  -- toᴰ a (b , eq) = {!!}

  -- ∈-≡₂ : ∀ {a : A} {b b' : B} {f} → (a , b) ∈ f → b ≡ b' → (a , b') ∈ f
  -- ∈-≡₂ x refl = x

  -- from∘to≡id : ∀ {a : A} (x : a ∈ᴰ to) (y : toᴰ a x ∈ᴿ to) → a ≡ proj₁ (fromᴿ (toᴰ a x) y)
  -- from∘to≡id (proj₃ , just refl x₁) (proj₅ , just refl x₃) = {!!}


  -- from∘to≡id : ∀ {a : A} (x : a ∈ᴰ to) (y : to′′ a x ∈ᴿ to) → a ≡ from′′ (to′′ a x) y
  -- from∘to≡id {a} x y = {!!}
-- with to a | inspect to a | from′′ (to′′ a x) y | inspect (from′′ (to′′ a x)) y
--   from∘to≡id {a} (b' , eq') (b'' , eq'') | just x | [ eq ] | r | [ eq''' ] = {!!}
--   from∘to≡id {a} (b' , eq') (b'' , eq'') | nothing | [ eq ] | r | [ eq''' ] = {!!}
  -- from∘to≡id {a} (.x , refl) (a' , eq') | just x | [ eq ] | r with to a'
  -- from∘to≡id {a} (.x , refl) (a' , eq') | just x | [ eq ] | r | just x₁ = {!!}
  -- from∘to≡id {a} (.x , refl) (a' , ()) | just x | [ eq ] | r | nothing -- need injectivity ?
  -- from∘to≡id {a} (proj₃ , ()) y | nothing | r | _

--  unjust : ∀ {A B} {a₁ a₂ b₁ b₂} →

  ∈-from : ∀ {a : A} {b : B} → (b , a) ∈ from → (a , b) ∈ to
  ∈-from x = left-inverse-of x

  open ≡-Reasoning {A = A}

  -- left-inverse-of′ : ∀ {a b} → (b , a) ∈ from → (x : b ∈ᴿ to) → a ≡ from′′ b x
  -- left-inverse-of′ {a} {b} (just {a' = a₂} x' y') (a₁ , just {a' = a₃} x y) =
  --   begin
  --     a ≡⟨ {!!} ⟩
  --     {!!} ≡⟨ {!!} ⟩
  --     from′′ b (a₁ , just x y) ∎


  injectiveᴾ : Injectiveᴾ to
  injectiveᴾ {a₁} {a₂} {b₁} {b₂} ∈₁ ∈₂ eq =
    let b₁' = {!!} -- (toᴰ a₁ (∈-∈ᴰ {p = to} ∈₁))
        ∈₁' = left-inverse-of {!∈₁!} -- ∈-∈ᴿ {!∈₂!}
        x = {!!} in -- fromᴿ b₁' ∈₁'  in
    begin
      a₁ ≡⟨ just-injective {!!} ⟩
--      proj₁ (fromᴿ (toᴰ a₁ (∈-∈ᴰ {p = to} ∈₁)) (∈-∈ᴿ (∈-≡₂ ∈₂ (sym eq)))) ≡⟨ sym {!left-inverse-of ?!} ⟩
      {!!} ≡⟨ {!!} ⟩
      a₂ ∎

  -- injective : Injective to
  -- injective {x} {y} eq = begin
  --   x                    ≈⟨ F.sym (left-inverse-of x) ⟩
  --   from ⟨$⟩ (to ⟨$⟩ x)  ≈⟨ Eq.cong from eq ⟩
  --   from ⟨$⟩ (to ⟨$⟩ y)  ≈⟨ left-inverse-of y ⟩
  --   y                    ∎

  -- injection : Injectionᴾ A B
  -- injection = record { to = to; injectiveᴾ = injectiveᴾ }

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

RightInverseᴾ : (A B : Set) → Set
RightInverseᴾ A B = LeftInverseᴾ A B

-- The set of all left inverses from one set to another. (Read A ↞ B
-- as "surjection from B to A".)

infix 3 _↞_

_↞_ : Set → Set → Set
A ↞ B = LeftInverseᴾ A B

-- Identity and composition.

id : ∀ {A : Set} → LeftInverseᴾ A A
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
