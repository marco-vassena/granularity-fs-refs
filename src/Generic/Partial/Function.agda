module Generic.Partial.Function where

open import Data.Product
open import Data.Empty
open import Data.Unit
open import Data.Maybe
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as E hiding ([_])
open import Category.Monad

-- If and only if
_⇔_ : ∀ (A B : Set) → Set
A ⇔ B = (A → B) × (B → A)

infixl 1 _⇔_

-- Partial Map
_⇀_ : Set → Set → Set
A ⇀ B = A → Maybe B

infix 1 _⇀_

-- _>=>_ : ∀ {A B C} → (B ⇀ C) → (A ⇀ B) → (A ⇀ C)
-- f >=> g = (λ x → g x >>= f)

open import Level
open RawMonad {zero} monad

-- TODO: probably not needed.
Back : ∀ {A B C} (f : B ⇀ C) (g : A ⇀ B) → Set
Back {A} f g = ∀ (x : A) → Is-just ((g >=> f) x) → Is-just (g x)

back : ∀ {A B C} (f : B ⇀ C) (g : A ⇀ B) (x : A) → Is-just ((g >=> f) x) → Is-just (g x)
back f g x p with g x
back f g x p | just x₁ = just tt
back f g x () | nothing

-- back₂ : ∀ {A B C x} (f : B ⇀ C) (g : A ⇀ B) → Is-just ((g >=> f) x) → Is-just (f {!!})
-- back₂ {x = x} f g p = {!!}
-- with f x
-- back₂ f g p | just x₁ = just tt
-- back₂ f g () | nothing

-- Empty Map
∅ : ∀ {A B} → A ⇀ B
∅ _ = nothing

-- Disjoint partial maps.  Maps f and g are disjoint, written f # g iff
-- values that are defined in f are not defined in g and viceversa.
-- Notice that only an implication in one direction is needed
-- (later we show that _#_ is symmetric).
_#_ : ∀ {A B} (f g : A ⇀ B) → Set
f # g = ∀ a → Is-just (f a) → Is-nothing (g a)

infixr 2 _#_

just-or-nothing : ∀ {A : Set} → (x : Maybe A) → Is-just x → ¬ (Is-nothing x)
just-or-nothing .(just _) (just px) (just ⊥) = ⊥

-- Lemmas
⊥-is-nothing-just : ∀ {A : Set} {x : A} → ¬ Is-nothing (just x)
⊥-is-nothing-just (just ())

is-just-nothing : ∀ {A : Set} {y : A} (x : Maybe A) → (Is-just x → Is-nothing (just y)) → x ≡ nothing
is-just-nothing {y = y} (just x) f = ⊥-elim (⊥-is-nothing-just (f (just tt)))
is-just-nothing nothing f = refl

-- Disjointness is symmetric.
sym-# : ∀ {A B} {f g : A ⇀ B} → f # g → g # f
sym-# {f = f} {g} p a with f a | g a | p a
sym-# {f = f} {g} p a | just x | just x₁ | f#g = ⊥-elim (⊥-is-nothing-just (f#g (just tt)))
sym-# {f = f} {g} p a | just x | nothing | f#g = λ ()
sym-# {f = f} {g} p a | nothing | ga | f#g = λ _ → nothing

data Graph {A : Set} {B : Set} (f : A ⇀ B) (a : A) : B → Set where
  just : ∀ {b a'} → a ≡ a' → f a' ≡ just b → Graph f a b

-- Proof that a maps to b in the partial map.
_∈_ : ∀ {A B} → A × B → A ⇀ B → Set
(a , b) ∈ p = p a ≡ just b

infixr 4 _∈_

_∈ᴰ_ : ∀ {A B} → A → A ⇀ B → Set
a ∈ᴰ p = Is-just (p a)

-- Proof that a is undefined in the map
_∉ᴰ_ : ∀ {A B} → A → A ⇀ B → Set
a ∉ᴰ p = Is-nothing (p a)

infixr 4 _∉ᴰ_

∈ᴰ-∈ : ∀ {A B} {a : A} {p : A ⇀ B} → a ∈ᴰ p → ∃ (λ b → (a , b) ∈ p)
∈ᴰ-∈ {a = a} {p} x with p a
∈ᴰ-∈ {a = a} {p} (just px) | .(just _) = _ , refl

≡-∉ : ∀ {A B} a (p : A ⇀ B) → p a ≡ nothing → a ∉ᴰ p
≡-∉ _ _ eq rewrite eq = nothing

≡-∈ᴰ : ∀ {A B} a b (p : A ⇀ B) → p a ≡ just b → a ∈ᴰ p
≡-∈ᴰ _ _ _ eq rewrite eq = just tt

∈-just : ∀ {A B} a b (p : A ⇀ B) → (a , b) ∈ p → Is-just (p a)
∈-just a b p eq rewrite eq = just tt

∈-or-∉ : ∀ {A B} {a : A} {b : B} {p : A ⇀ B} →
           (a , b) ∈ p → ¬ (a ∉ᴰ p)
∈-or-∉ {a = a} {b} {p} x y = just-or-nothing (p a) (∈-just a b p x) y

-- TODO: it seems we have too many representations ... clean it up!

--------------------------------------------------------------------------------

open import Level
open import Category.Monad
open RawMonadPlus {zero} {M = Maybe} monadPlus hiding (∅)

-- Pointwise version of parallel composition (_∣_) for readability
_∣′_ : ∀ {A B} → A ⇀ B → A ⇀ B → A ⇀ B
f ∣′ g = λ a → f a ∣ g a

_LeftInverseOfᴾ_ : ∀ {A B} → A ⇀ B → B ⇀ A → Set
_LeftInverseOfᴾ_ f g = ∀ {x y} → (x , y) ∈ f → (y , x) ∈ g

_RightInverseOfᴾ_ : ∀ {A B} → A ⇀ B → B ⇀ A → Set
_RightInverseOfᴾ_ f g = g LeftInverseOfᴾ f

_InverseOfᴾ_ : ∀ {A B} → A ⇀ B → B ⇀ A → Set
_InverseOfᴾ_ f g = ∀ {x y} → (x , y) ∈ f ⇔ (y , x) ∈ g

-- Disjoint invert partial maps compose and remain inverse.
inverse-compose  : ∀ {A B : Set} {f₁ f₂ : A ⇀ B} {g₁ g₂ : B ⇀ A} →
          f₁ LeftInverseOfᴾ g₁ → f₂ LeftInverseOfᴾ g₂ →
          f₁ # f₂ → g₁ # g₂ →
          (f₁ ∣′ f₂) LeftInverseOfᴾ (g₁ ∣′ g₂)
inverse-compose {_} {_} {f₁} {f₂} {g₁} {g₂} inv₁ inv₂ #₁ #₂ {a} {b} eq
  with f₁ a | f₂ a | g₁ b | g₂ b | inv₁ {a} {b} | inv₂ {a} {b} | #₁ a | #₂ b
... | just x | ma₂ | mb₁ | mb₂ | eq₁ | eq₂ | p₁ | p₂
  rewrite eq₁ eq = refl
... | nothing | ma₂ | mb₁ | mb₂ | eq₁ | eq₂ | p₁ | p₂
  rewrite eq₂ eq | is-just-nothing mb₁ p₂ = refl

--------------------------------------------------------------------------------

-- Shorthand
DecEq : (A : Set) → Set
DecEq A = Decidable (_≡_ {A = A})

module Util {A B : Set} {{ _≟ᴬ_ : DecEq A }}  where

  -- Update partial map
  _[_↦_] : A ⇀ B → A → B → A ⇀ B
  _[_↦_] f a b a' with a ≟ᴬ a'
  _[_↦_] f a b .a | yes refl = just b
  _[_↦_] f a b a' | no ¬p = f a

  infixr 3 _[_↦_]

  -- Singleton pmap
  _↦_ : A → B →  A ⇀ B
  a ↦ b = ∅ [ a ↦ b ]

  infixr 1 _↦_

  -- Does not seem is ever used
  -- Only one mapping
  -- only-one : ∀ a b a' b' → (a' , b') ∈ (a ↦ b) → a' ≡ a × b' ≡ b
  -- only-one a b a' b' x with a ≟ᴬ a'
  -- only-one a b .a .b refl | yes refl = refl , refl
  -- only-one a b a' b' () | no ¬p

  trivial : ∀ x y → (x , y) ∈ (x ↦ y)
  trivial x y with x ≟ᴬ x
  trivial x y | yes refl = refl
  trivial x y | no ¬p = ⊥-elim (¬p refl)

  -- TODO: needed?
  -- back↦ : ∀ x' x y → x' ∈ (x ↦ y) → x' ≡ x
  -- back↦ x' x y p with x ≟ᴬ x'
  -- back↦ _ _ _ p  | yes refl = refl
  -- back↦ _ _ _ () | no ¬p

  -- Not in the domain implies disjointness
  ∉-# : ∀ {a : A} {b : B} → (f : A ⇀ B) → a ∉ᴰ f → f # (a ↦ b)
  ∉-# {a} f x a' y  with a ≟ᴬ a'
  ∉-# {a} {b} f x a' y | no ¬p = nothing
  ∉-# {a} {b} f x a' y | yes p = ⊥-elim (aux (cong f p) x y)
    where aux : f a ≡ f a' → Is-nothing (f a) → ¬ (Is-just (f a'))
          aux eq x y with f a | f a'
          aux eq (just px) y | .(just _) | b' = px
          aux () nothing (just px) | .nothing | .(just _)

open Util public

-- Syntactic sugar when the DecEq instance is not found automatically
_⟨_⟩↦_ : ∀ {A B : Set} →  A → DecEq A → B → A ⇀ B
_⟨_⟩↦_ {A} {B} a _≟_  b = a P₁.↦ b
  where module P₁ = Util {A} {B} {{_≟_}}

left-inverse-of-↦ : ∀ {A B} {{_≟ᴬ_ : DecEq A}}  {{_≟ᴮ_ : DecEq B}} {a b} →
                    (a ⟨ _≟ᴬ_ ⟩↦ b) LeftInverseOfᴾ (b ⟨ _≟ᴮ_ ⟩↦ a)
left-inverse-of-↦ {{_≟ᴬ_}} {{_≟ᴮ_}} {a} {b} {a'} {b'} x with a ≟ᴬ a' | b ≟ᴮ b'
left-inverse-of-↦  x | yes refl | yes refl = refl
left-inverse-of-↦ refl | yes refl | no ¬p = ⊥-elim (¬p refl)
left-inverse-of-↦ () | no ¬p | _

right-inverse-of-↦ : ∀ {A B} {{_≟ᴬ_ : DecEq A}}  {{_≟ᴮ_ : DecEq B}} {a b} →
                     (a ⟨ _≟ᴬ_ ⟩↦ b) RightInverseOfᴾ (b ⟨ _≟ᴮ_ ⟩↦ a)
right-inverse-of-↦ {{_≟ᴬ_}} {{_≟ᴮ_}} = left-inverse-of-↦
  where instance _ = _≟ᴬ_
        instance _ = _≟ᴮ_

inverse-of-↦ : ∀ {A B : Set} {{_≟ᴬ_ : DecEq A}}  {{_≟ᴮ_ : DecEq B}} {a : A} {b : B} →
                 (b ⟨ _≟ᴮ_ ⟩↦ a) InverseOfᴾ (a ⟨ _≟ᴬ_ ⟩↦ b)
inverse-of-↦ {A} {B} {{_≟ᴬ_}}  {{_≟ᴮ_}} {a} {b} = left-inverse-of-↦ , right-inverse-of-↦
  where instance _ = _≟ᴬ_
        instance _ = _≟ᴮ_

--------------------------------------------------------------------------------

-- Partial Identity for Fin n
open import Data.Nat

module Id (n : ℕ) where

  open import Data.Nat.Properties

  idᴾ : ℕ ⇀ ℕ
  idᴾ m with m <? n
  idᴾ m | yes p = just m
  idᴾ m | no ¬p = nothing

  -- TODO: better name
  lemma : ∀ {x y} → (x , y) ∈ idᴾ → x ≡ y × y < n
  lemma {x} {y} ∈ with x <? n
  lemma {x} {.x} refl | yes p = refl , p
  lemma {x} {y} () | no ¬p

  idᴾ-≡ : ∀ {x y} → (x , y) ∈ idᴾ → x ≡ y
  idᴾ-≡ p = proj₁ (lemma p)

  idᴾ-<ᴿ : ∀ {x y} → (x , y) ∈ idᴾ → y < n
  idᴾ-<ᴿ p = proj₂ (lemma p)

  idᴾ-<ᴰ : ∀ {x y} → (x , y) ∈ idᴾ → x < n
  idᴾ-<ᴰ p with lemma p
  ... | x≡y , y<n rewrite x≡y = y<n

  step-idᴾ : ∀ {x} → x < n → idᴾ x ≡ just x
  step-idᴾ {x} x<n with x <? n
  step-idᴾ {x} x<n | yes p = refl
  step-idᴾ {x} x<n | no x≮n = ⊥-elim (x≮n x<n)

  inv : idᴾ LeftInverseOfᴾ idᴾ
  inv {x} {y} p =
    let x≡y , y<n = lemma p in
      trans (step-idᴾ y<n) (sym (cong just x≡y))

-------------------------------------------------------------------------------
