{-# OPTIONS --allow-unsolved-metas #-}

module Generic.Bijection where

open import Generic.PMap
open import Data.Empty
open import Data.Unit hiding (_≟_)
open import Data.Product as P
open import Data.Maybe
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

-- If and only if
_⇔_ : ∀ (A B : Set) → Set
A ⇔ B = (A → B) × (B → A)

infixl 1 _⇔_

-- A bijection is a pair of partial maps between two sets, where these
-- maps are each other inverse.
--
--TODO: this could actually be stronger, but maybe is enough for now.
record Bij (A B : Set) : Set where
  field  to : A ⇀ B
         back : B ⇀ A
         bij : ∀ {a b} → (to a ≡ just b) ⇔ (back b ≡ just a)

-- might have to add the proof about bijection here

-- Homogeneous Bijection
Bijᴴ : (A : Set) → Set
Bijᴴ A = Bij A A

-- A pair of values from A and B are in the bijection iff they are
-- mutually related under their respective mapping.
_↔_∈_ : ∀ {A B} → A → B → Bij A B → Set
a ↔ b ∈ β =  (a ↦ b ∈ᴾ to) × (b ↦ a ∈ᴾ back)
  where open Bij β

_∈_ : ∀ {A B} → A × B → Bij A B → Set
(a , b) ∈ β = a ↔ b ∈ β

-- Empty bijection
∅ : ∀ {A B} → Bij A B
∅ = record { to = λ _ → nothing ;
             back = λ _ → nothing ;
             bij = (λ ()) , λ () }

-- Reverse bijection
flip : ∀ {A B} → Bij A B → Bij B A
flip β = record { to = back ; back = to ; bij = swap bij}
  where open Bij β

flip↔ : ∀ {A B β} {a : A} {b : B} → a ↔ b ∈ β → b ↔ a ∈ (flip β)
flip↔ ( eq₁ , eq₂ ) = eq₂ , eq₁

-- β₁ ▻ β₂ denotes that β₂ is disjoint from β₁, i.e., β₂ doesn't
-- relate elements already related in β₁.
_▻_ : ∀ {A} → (β₁ β₂ : Bijᴴ A) → Set
_▻_ {A} β₁ β₂ = disjoint B₁.to B₂.to × disjoint B₁.back B₂.back
  where module B₁ = Bij β₁
        module B₂ = Bij β₂
        disjoint : (f g : A → Maybe A) → Set
        disjoint f g = ∀ a → Is-just (f a) → Is-nothing (g a)

⊥-just-is-nothing : ∀ {A : Set} {x : A} → ¬ Is-nothing (just x)
⊥-just-is-nothing (just ())

foo : ∀ {A : Set} {y : A} (x : Maybe A) → (Is-just x → Is-nothing (just y)) → x ≡ nothing
foo {y = y} (just x) f = ⊥-elim (⊥-just-is-nothing (f (just tt)))
foo nothing f = refl

-- Composition of homogeneous bijections
_∘_ : ∀ {A} → (β₁ β₂ : Bijᴴ A) {{β₁▻β₂ : β₁ ▻ β₂}} → Bijᴴ A
_∘_ {A} β₁ β₂ {{ to-▻ , back-▻ }} =
  record { to   = λ x → B₁.to x ∣ B₂.to x ;
           back = λ x → B₁.back x ∣ B₂.back x ;
           bij = p₁ , {!!} }
  where module B₁ = Bij β₁
        module B₂ = Bij β₂
        open import Category.Monad
        open RawMonadPlus monadPlus
        p₁ : ∀ {a b} → (B₁.to a ∣ B₂.to a) ≡ just b → (B₁.back b ∣ B₂.back b) ≡ just a
        p₁ {a} {b} eq₁
          with B₁.to a | B₂.to a | B₁.back b | B₂.back b | B₁.bij {a} {b} | B₂.bij {a} {b} | to-▻ a | back-▻ b
        p₁ {a} {b} eq₁ | just a₁ | just a₂ | _ | _ | _ | _ | f | g = ⊥-elim (⊥-just-is-nothing (f (just _)))
        p₁ {a} {b} eq₁ | just a₁ | nothing | mb₁ | mb₂ | peq₁ | peq₂ | f | g
          rewrite proj₁ peq₁ eq₁ = refl
        p₁ {a} {b} eq₁ | nothing | ma₂ | mb₁ | mb₂ | peq₁ | peq₂ | f | g
          rewrite proj₁ peq₂ eq₁ | foo mb₁ g = refl

-- with
-- B₁.back b | proj₁ (B₁.bij {a} {b})
--         p₁ {a} {b} x | just a' | y = {!proj₂ (B₁.bij {a} {b})!}
--         p₁ {a} {b} x | nothing | y = {!proj₁ (B₁.bij {a} {b})!}

module Ops {A B : Set}
  {{ _≟ᴬ_ : Decidable (_≡_ {A = A}) }}
  {{ _≟ᴮ_ : Decidable (_≡_ {A = B}) }} where

  module AB = PMapUtil A B {{_≟ᴬ_}}
  module BA = PMapUtil B A {{_≟ᴮ_}}

  -- TODO: it doesn't seem this op for now. We will need it to add
  -- single entries.

  -- Actually, we can define this in terms of Bijection composition (see above)

  -- Add a new mapping to the bijection.
  -- TODO: should we assume/require that they are not in the mapping already?
  -- I won't add it until it comes out in the proof
  _⋃_ : A × B → Bij A B → Bij A B
  (a , b) ⋃ β = record { to = to AB.[ a ↦ b ]ᴾ ;
                         back = back BA.[ b ↦ a ]ᴾ ;
                         bij = {!!} }
    where open Bij β

module AddressBij where

  open import Data.Nat

  -- A bijection between addresses (natural numbers)
  Bijᴬ : Set
  Bijᴬ = Bijᴴ ℕ

  instance
    _≟ᴺ_ : (n₁ n₂ : ℕ) → Dec (n₁ ≡ n₂)
    _≟ᴺ_ = _≟_

  open Ops {ℕ} {ℕ} {{_≟ᴺ_}} public

  -- Identity bijection
  ι : Bijᴬ
  ι = record { to = just ; back = just ; bij = sym , sym}
