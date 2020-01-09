module Generic.PMap where

open import Data.Product
open import Data.Empty
open import Data.Unit
open import Data.Maybe
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality hiding ([_])

-- If and only if
_⇔_ : ∀ (A B : Set) → Set
A ⇔ B = (A → B) × (B → A)

infixl 1 _⇔_

-- Partial Map
_⇀_ : Set → Set → Set
A ⇀ B = A → Maybe B

infix 1 _⇀_

-- Empty Map
∅ : ∀ {A B} → A ⇀ B
∅ _ = nothing

-- Disjoint partial maps
-- TODO: rename to # because it is symmetric
_▻ᴾ_ : ∀ {A B} (f g : A ⇀ B) → Set
f ▻ᴾ g = ∀ a → Is-just (f a) → Is-nothing (g a)

_#_ : ∀ {A B} (f g : A ⇀ B) → Set
f # g = ∀ a → Is-just (f a) → Is-nothing (g a)

infixr 2 _#_

-- Lemmas
⊥-is-nothing-just : ∀ {A : Set} {x : A} → ¬ Is-nothing (just x)
⊥-is-nothing-just (just ())

is-just-nothing : ∀ {A : Set} {y : A} (x : Maybe A) → (Is-just x → Is-nothing (just y)) → x ≡ nothing
is-just-nothing {y = y} (just x) f = ⊥-elim (⊥-is-nothing-just (f (just tt)))
is-just-nothing nothing f = refl

sym-# : ∀ {A B} {f g : A ⇀ B} → f # g → g # f
sym-# {f = f} {g} p a with f a | g a | p a
sym-# {f = f} {g} p a | just x | just x₁ | f#g = ⊥-elim (⊥-is-nothing-just (f#g (just tt)))
sym-# {f = f} {g} p a | just x | nothing | f#g = λ ()
sym-# {f = f} {g} p a | nothing | ga | f#g = λ _ → nothing

-- Proof that a maps to b in the partial map.
_∈_ : ∀ {A B} → A × B → A ⇀ B → Set
(a , b) ∈ p = p a ≡ just b

infixr 4 _∈_

_∉_ : ∀ {A B} → A → A ⇀ B → Set
a ∉ p = Is-nothing (p a)

-- Shorthand
DecEq : (A : Set) → Set
DecEq A = Decidable (_≡_ {A = A})

-- TODO: make decidability top level? maybe just open this module
module PMapUtil {A B : Set} {{ _≟ᴬ_ : DecEq A }}  where

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

  -- Only one mapping
  only-one : ∀ a b a' b' → (a' , b') ∈ (a ↦ b) → a' ≡ a × b' ≡ b
  only-one a b a' b' x with a ≟ᴬ a'
  only-one a b .a .b refl | yes refl = refl , refl
  only-one a b a' b' () | no ¬p

  -- Not in the domain implies disjointness
  ∉-# : ∀ {a : A} {b : B} → (f : A ⇀ B) → a ∉ f → f # (a ↦ b)
  ∉-# {a} f x a' y  with a ≟ᴬ a'
  ∉-# {a} {b} f x a' y | no ¬p = nothing
  ∉-# {a} {b} f x a' y | yes p = ⊥-elim (aux (cong f p) x y)
    where aux : f a ≡ f a' → Is-nothing (f a) → ¬ (Is-just (f a'))
          aux eq x y with f a | f a'
          aux eq (just px) y | .(just _) | b' = px
          aux () nothing (just px) | .nothing | .(just _)

open PMapUtil public

-- Syntactic sugar when the DecEq instance is not found automatically
_-⟨_⟩→_ : ∀ {A B : Set} →  A → DecEq A → B → A ⇀ B
_-⟨_⟩→_ {A} {B} a _≟_  b = a P.↦ b
  where module P = PMapUtil {A} {B} {{_≟_}}
