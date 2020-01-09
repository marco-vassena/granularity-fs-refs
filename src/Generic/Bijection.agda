{-# OPTIONS --allow-unsolved-metas #-}

-- TODO: split generic bij from homogeneous in two modules
-- Generic bij requires decidability (to create singleton bijs)


module Generic.Bijection where

open import Generic.PMap renaming (∅ to ∅ᴾ ; _#_ to _#ᴾ_ ; _∈_ to _∈ᴾ_)
open import Data.Empty
open import Data.Unit hiding (_≟_)
open import Data.Product as P
open import Data.Maybe
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Category.Monad
open import Level
open RawMonadPlus {zero} {M = Maybe} monadPlus hiding (∅)

-- TODO: rename isB to ↔
-- Bijection property
IsB : ∀ {A B} (f : A ⇀ B) (g : B ⇀ A) → Set
IsB f g = ∀ {a b} → (a , b) ∈ᴾ f ⇔ (b , a) ∈ᴾ g

_↔_ : ∀ {A B} (f : A ⇀ B) (g : B ⇀ A) → Set
f ↔ g = IsB f g

-- A bijection is a pair of partial maps between two sets, where these
-- maps are each other inverse.
record Bij (A B : Set) : Set where
  field  to : A ⇀ B
         back : B ⇀ A
         isB : IsB to back

sym-IsB : ∀ {A B : Set} {f : A ⇀ B} {g : B ⇀ A} →
            IsB f g → IsB g f
sym-IsB x = swap x

symᴮ : ∀ {A B} → Bij A B → Bij B A
symᴮ β = record { to = B.back ; back = B.to ; isB = sym-IsB B.isB }
  where module B = Bij β

-- Homogeneous Bijection
Bijᴴ : (A : Set) → Set
Bijᴴ A = Bij A A

-- A pair of values from A and B are in the bijection iff they are
-- mutually related under their respective mapping.
-- TODO: could be pair here to
_↔_∈_ : ∀ {A B} → A → B → Bij A B → Set
a ↔ b ∈ β =  (a , b) ∈ᴾ to × (b , a) ∈ᴾ back
  where open Bij β

-- _∈_ : ∀ {A B} → A × B → Bij A B → Set
-- (a , b) ∈ β = a ↔ b ∈ β

-- Empty bijection
∅ : ∀ {A B} → Bij A B
∅ = record { to = λ _ → nothing ;
             back = λ _ → nothing ;
             isB = (λ ()) , λ () }

-- Reverse bijection
flip : ∀ {A B} → Bij A B → Bij B A
flip β = record { to = back ; back = to ; isB = swap isB}
  where open Bij β

flip↔ : ∀ {A B β} {a : A} {b : B} → a ↔ b ∈ β → b ↔ a ∈ (flip β)
flip↔ ( eq₁ , eq₂ ) = eq₂ , eq₁

-- Rename to # (symmetric)
-- β₁ ▻ β₂ denotes that β₂ is disjoint from β₁, i.e., β₂ doesn't
-- relate elements already related in β₁.
_▻_ : ∀ {A B} → (β₁ β₂ : Bij A B) → Set
_▻_ {A} β₁ β₂ = B₁.to ▻ᴾ B₂.to × B₁.back ▻ᴾ B₂.back
  where module B₁ = Bij β₁
        module B₂ = Bij β₂

-- TODO: use ↦_∈
-- Partial maps remain related under composition
IsB-∣ : ∀ {A : Set} (f₁ g₁ f₂ g₂ : A ⇀ A) → Set
IsB-∣ f₁ g₁ f₂ g₂ = ∀ {a b} → (f₁ a ∣ f₂ a) ≡ just b → (g₁ b ∣ g₂ b) ≡ just a

isB-∣ : ∀ {A : Set} {f₁ g₁ f₂ g₂ : A ⇀ A} →
          IsB f₁ g₁ → IsB f₂ g₂ →
          f₁ ▻ᴾ f₂ → g₁ ▻ᴾ g₂ →
          IsB-∣ f₁ g₁ f₂ g₂
isB-∣ {_} {f₁} {g₁} {f₂} {g₂} isB₁ isB₂ ▻₁ ▻₂ {a} {b} eq
  with f₁ a | f₂ a | g₁ b | g₂ b | isB₁ {a} {b} | isB₂ {a} {b} | ▻₁ a | ▻₂ b
... | just x | ma₂ | mb₁ | mb₂ | peq₁ | peq₂ | p₁ | p₂
  rewrite proj₁ peq₁ eq = refl
... | nothing | ma₂ | mb₁ | mb₂ | peq₁ | peq₂ | p₁ | p₂
  rewrite proj₁ peq₂ eq | is-just-nothing mb₁ p₂ = refl

-- Property that denotes that the composition of two bijections is a
-- bijection.
IsB-∘ : ∀ {A} (β₁ β₂ : Bijᴴ A) → Set
IsB-∘ β₁ β₂ = IsB (λ x → B₁.to x ∣ B₂.to x) (λ x → B₁.back x ∣ B₂.back x)
  where module B₁ = Bij β₁
        module B₂ = Bij β₂

-- If two bijections are disjoint, then their composition is a
-- bijection.
isB-∘ : ∀ {A} (β₁ β₂ : Bijᴴ A) → β₁ ▻ β₂ → IsB-∘ β₁ β₂
isB-∘ {A} β₁ β₂ (to-▻ , back-▻)
  = isB-∣ {A} {B₁.to} {B₁.back} {B₂.to} {B₂.back} B₁.isB B₂.isB to-▻ back-▻ ,
    isB-∣ {_} {B₁.back} {B₁.to} {B₂.back} {B₂.to} B₁′.isB B₂′.isB back-▻ to-▻
  where module B₁ = Bij β₁
        module B₂ = Bij β₂
        module B₁′ = Bij (symᴮ β₁)
        module B₂′ = Bij (symᴮ β₂)

_∘′_ : ∀ {A B} → (β₁ β₂ : Bij A B) {{β₁▻β₂ : β₁ ▻ β₂}} → Bij A  B
β₁ ∘′ β₂ = record { to = λ x → B₁.to x ∣ B₂.to x ;
                    back = λ x → B₁.back x ∣ B₂.back x ;
                    isB = {!!} }
  where module B₁ = Bij β₁
        module B₂ = Bij β₂


-- TODO we can compose non-homogeneous bijection right? yes, see above
-- Are bijections defined over two or one type? We can have the more general thing with 2 types.
-- Composition of homogeneous bijections
_∘_ : ∀ {A} → (β₁ β₂ : Bijᴴ A) {{β₁▻β₂ : β₁ ▻ β₂}} → Bijᴴ A
_∘_ {A} β₁ β₂ {{ to-▻ , back-▻ }} =
  record { to   = λ x → B₁.to x ∣ B₂.to x ;
           back = λ x → B₁.back x ∣ B₂.back x ;
           isB = isB-∘ β₁ β₂ (to-▻ , back-▻) }
  where module B₁ = Bij β₁
        module B₂ = Bij β₂

-- Adding one entry to the bijection is a special case of composition.
-- TODO: better symbol? we use # for disjoint, let's use ▻ instead
-- (this operation is *not* symmetric).
_#_ : ∀ {A} → Bijᴴ A → A × A → Bijᴴ A
β # x = {!β ∘ ?!}


module Ops {A B : Set}
  {{ _≟ᴬ_ : Decidable (_≡_ {A = A}) }}
  {{ _≟ᴮ_ : Decidable (_≡_ {A = B}) }} where

  instance _ = _≟ᴬ_
  instance _ = _≟ᴮ_

  module A = PMapUtil {A} {B} {{_≟ᴬ_}}
  module B = PMapUtil {B} {A} {{_≟ᴮ_}}

  aux : ∀ {A B} {{_≟ᴬ_ : DecEq A}}  {{_≟ᴮ_ : DecEq B}} a b {a' b'} →
           let f = a -⟨ _≟ᴬ_ ⟩→ b
               g = b -⟨ _≟ᴮ_ ⟩→ a in (a' , b') ∈ᴾ f → (b' , a') ∈ᴾ g
  aux {{_≟ᴬ_}} {{_≟ᴮ_}} a b {a'} {b'} x with a ≟ᴬ a' | b ≟ᴮ b'
  aux {{_≟ᴬ_ = _≟ᴬ_}} {{_≟ᴮ_}} a b {.a} {.b} x | yes refl | yes refl = refl
  aux {{_≟ᴬ_ = _≟ᴬ_}} {{_≟ᴮ_}} a b {.a} {.b} refl | yes refl | no ¬p = ⊥-elim (¬p refl)
  aux {{_≟ᴬ_ = _≟ᴬ_}} {{_≟ᴮ_}} a b {a'} {b'} () | no ¬p | c

  isB↔ : ∀ (a : A) (b : B) → IsB (a ↦ b) (b ↦ a)
  isB↔ a b {a'} {b'} = aux a b , aux b a

  -- Singleton bijection
  ⟨_↔_⟩ : A → B → Bij A B
  ⟨ a ↔ b ⟩ = record { to = a ↦ b ; back = b ↦ a ; isB = isB↔ a b }

  -- Add a single pair to a bijection
  _▻′_ : (β : Bij A B) (x : A × B) →
         let (a , b) = x in
           {{∉ᴬ : a ∉ Bij.to β}}
           {{∉ᴮ : b ∉ Bij.back β}} → Bij A B
  _▻′_ β (a , b) {{ ∉ᴬ }} {{ ∉ᴮ }} = β ∘′ ⟨ a ↔ b ⟩
    where instance _ : β ▻ ⟨ a ↔ b ⟩
                   _ = ∉-# (Bij.to β) ∉ᴬ , ∉-# (Bij.back β) ∉ᴮ

module AddressBij where

  open import Data.Nat

  -- A bijection between addresses (natural numbers)
  Bijᴬ : Set
  Bijᴬ = Bijᴴ ℕ

  instance
    _≟ᴺ_ : (n₁ n₂ : ℕ) → Dec (n₁ ≡ n₂)
    _≟ᴺ_ = _≟_

  -- TODO remove
  -- open Ops {ℕ} {ℕ} {{_≟ᴺ_}} public

  -- Identity bijection
  ι : Bijᴬ
  ι = record { to = just ; back = just ; isB = sym , sym}
