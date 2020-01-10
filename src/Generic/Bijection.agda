-- {-# OPTIONS --allow-unsolved-metas #-}

module Generic.Bijection where

open import Generic.PMap renaming (∅ to ∅ᴾ ; _#_ to _#ᴾ_ ; _∈_ to _∈ᴾ_)
open import Generic.PMap using (_⇔_) public
open import Data.Empty
open import Data.Unit hiding (_≟_)
open import Data.Sum
open import Data.Product as P hiding (swap)
open import Data.Maybe as MB
open import Relation.Nullary
open import Relation.Binary
open import Category.Monad
open import Level
open import Relation.Binary.PropositionalEquality as E hiding (sym ; trans)
open RawMonadPlus {zero} {M = Maybe} monadPlus hiding (∅)

-- The bijection property
_↔_ : ∀ {A B} (f : A ⇀ B) (g : B ⇀ A) → Set
f ↔ g = ∀ {a b} → (a , b) ∈ᴾ f ⇔ (b , a) ∈ᴾ g

-- I don't think that we need it in both directions!  The bijection
-- property should give us that there is only one pre-image for each
-- image.

id  : ∀ {A} → just {A = A} ↔ just
id = E.sym , E.sym

sym  : ∀ {A B} {f : A ⇀ B} {g : B ⇀ A} →
         f ↔ g → g ↔ f
sym x = P.swap x

open import Relation.Binary.PropositionalEquality hiding (sym)

-- A bijection is a pair of partial maps between two sets, where these
-- maps are each other inverse.
record Bij (A B : Set) : Set where
  field  to : A ⇀ B
         back : B ⇀ A
         isB : to ↔ back

-- Identity bijection
ι : ∀ {A} → Bij A A
ι = record { to = just ; back = just ; isB = id}

-- TODO: remove, same as flip
-- swap : ∀ {A B} → Bij A B → Bij B A
-- swap β = record { to = B.back ; back = B.to ; isB = Prop.sym B.isB }
--   where module B = Bij β

-- A pair of values from A and B are in the bijection iff they are
-- mutually related under their respective mapping.
-- TODO: could be pair here to
_↔_∈_ : ∀ {A B} → A → B → Bij A B → Set
a ↔ b ∈ β =  (a , b) ∈ᴾ to × (b , a) ∈ᴾ back
  where open Bij β

-- With a pair
-- _∈_ : ∀ {A B} → A × B → Bij A B → Set
-- (a , b) ∈ β = a ↔ b ∈ β

-- Empty bijection
∅ : ∀ {A B} → Bij A B
∅ = record { to = λ _ → nothing ;
             back = λ _ → nothing ;
             isB = (λ ()) , λ () }

-- Reverse bijection
flip : ∀ {A B} → Bij A B → Bij B A
flip β = record { to = back ; back = to ; isB = sym isB}
  where open Bij β

flip↔ : ∀ {A B} {β : Bij A B} {a b} → a ↔ b ∈ β → b ↔ a ∈ (flip β)
flip↔ = P.swap

-- Disjoint bijections.
-- β₁ # β₂ denotes that β₂ is disjoint from β₁, i.e., the
-- maps of β₁ and β₂ are respectively disjoint.
_#_ : ∀ {A B} → (β₁ β₂ : Bij A B) → Set
_#_ {A} β₁ β₂ = (B₁.to #ᴾ B₂.to) × (B₁.back #ᴾ B₂.back)
  where module B₁ = Bij β₁
        module B₂ = Bij β₂

-- Property that denotes that the composition of two bijections is a
-- bijection.
IsB-∘ : ∀ {A B} (β₁ β₂ : Bij A B) → Set
IsB-∘ β₁ β₂ = (B₁.to ∣′ B₂.to) ↔ (B₁.back ∣′ B₂.back)
  where module B₁ = Bij β₁
        module B₂ = Bij β₂

-- If two bijections are disjoint, then their composition is a
-- bijection.
isB-∘ : ∀ {A B} (β₁ β₂ : Bij A B) → β₁ # β₂ → IsB-∘ β₁ β₂
isB-∘ {A} β₁ β₂ (to-# , back-#)
  = inverse-compose (proj₁ B₁.isB) (proj₁ B₂.isB) to-# back-# ,
    inverse-compose (proj₁ B₁′.isB) (proj₁ B₂′.isB) back-# to-#
  where module B₁ = Bij β₁
        module B₂ = Bij β₂
        module B₁′ = Bij (flip β₁)
        module B₂′ = Bij (flip β₂)

-- Composition of disjoint bijections
_∘_ : ∀ {A B} → (β₁ β₂ : Bij A B) {{β₁#β₂ : β₁ # β₂}} → Bij A B
_∘_ {A} β₁ β₂ {{ to-# , back-# }} =
  record { to   = B₁.to ∣′ B₂.to ;
           back = B₁.back ∣′ B₂.back ;
           isB = isB-∘ β₁ β₂ (to-# , back-#) }
  where module B₁ = Bij β₁
        module B₂ = Bij β₂

module Ops {A B : Set}
  {{ _≟ᴬ_ : Decidable (_≡_ {A = A}) }}
  {{ _≟ᴮ_ : Decidable (_≡_ {A = B}) }} where

  -- These declarations just make agda aware of the decidable instances.
  instance _ = _≟ᴬ_
  instance _ = _≟ᴮ_

  -- When agda cannot figure out what instancies to use, we use qualified bindings.
  module A = Util {A} {B} {{_≟ᴬ_}}
  module B = Util {B} {A} {{_≟ᴮ_}}

  -- Lemma defined with explicit instances so that we can reuse it for module A and B.
  aux : ∀ {A B} {{_≟ᴬ_ : DecEq A}}  {{_≟ᴮ_ : DecEq B}} a b {a' b'} →
           let f = a -⟨ _≟ᴬ_ ⟩→ b
               g = b -⟨ _≟ᴮ_ ⟩→ a in (a' , b') ∈ᴾ f → (b' , a') ∈ᴾ g
  aux {{_≟ᴬ_}} {{_≟ᴮ_}} a b {a'} {b'} x with a ≟ᴬ a' | b ≟ᴮ b'
  aux {{_≟ᴬ_ = _≟ᴬ_}} {{_≟ᴮ_}} a b {.a} {.b} x | yes refl | yes refl = refl
  aux {{_≟ᴬ_ = _≟ᴬ_}} {{_≟ᴮ_}} a b {.a} {.b} refl | yes refl | no ¬p = ⊥-elim (¬p refl)
  aux {{_≟ᴬ_ = _≟ᴬ_}} {{_≟ᴮ_}} a b {a'} {b'} () | no ¬p | c

  isB↔ : ∀ (a : A) (b : B) → (a ↦ b) ↔ (b ↦ a)
  isB↔ a b {a'} {b'} = aux a b , aux b a

  -- Singleton bijection
  ⟨_↔_⟩ : A → B → Bij A B
  ⟨ a ↔ b ⟩ = record { to = a ↦ b ; back = b ↦ a ; isB = isB↔ a b }

  -- Add a single pair to the right of a bijection
  _▻_ : (β : Bij A B) (x : A × B) →
         let (a , b) = x in
           {{∉ᴬ : a ∉ Bij.to β}}
           {{∉ᴮ : b ∉ Bij.back β}} → Bij A B
  _▻_ β (a , b) {{ ∉ᴬ }} {{ ∉ᴮ }} = β ∘ ⟨ a ↔ b ⟩
    where instance _ : β # ⟨ a ↔ b ⟩
                   _ = ∉-# (Bij.to β) ∉ᴬ , ∉-# (Bij.back β) ∉ᴮ

  -- Add a single pair to the left of a bijection
  _◅_ : (x : A × B) (β : Bij A B) →
         let (a , b) = x in
           {{∉ᴬ : a ∉ Bij.to β}}
           {{∉ᴮ : b ∉ Bij.back β}} → Bij A B
  _◅_ (a , b) β {{ ∉ᴬ }} {{ ∉ᴮ }} = ⟨ a ↔ b ⟩ ∘ β
    where instance _ : ⟨ a ↔ b ⟩ # β
                   _ = sym-# (∉-# (Bij.to β) ∉ᴬ) , sym-# (∉-# (Bij.back β) ∉ᴮ)


  split↔ : ∀ {β₁ β₂ : Bij A B} {{β₁#β₂ : β₁ # β₂}} {a b} → a ↔ b ∈ (β₁ ∘ β₂) → a ↔ b ∈ β₁ ⊎ a ↔ b ∈ β₂
  split↔ = {!!}

-- TODO: maybe no need to export aux.
open Ops public

module AddressBij where

  open import Data.Nat
  open import Data.Fin

  -- A finite bijection between addresses (natural numbers) with ranges.
  Bijᴬ : (n m : ℕ) → Set
  Bijᴬ n m = Bij (Fin n) (Fin m)

  ⌜_⌝¹ : ∀ {n m} → Bijᴬ n m → Bijᴬ (ℕ.suc n) (ℕ.suc m)
  ⌜ β ⌝¹ = {!!}

  instance
-- : (n₁ n₂ : ℕ) → Dec (n₁ ≡ n₂)
--     _ = _≟_

    -- We can always "strenghten" Fin values to have the same type.
    _≟ᶠ_ : {n : ℕ} (x y : Fin n) → Dec (x ≡ y)
    Fin.zero ≟ᶠ Fin.zero = yes refl
    Fin.zero ≟ᶠ Fin.suc y = no (λ ())
    Fin.suc x ≟ᶠ Fin.zero = no (λ ())
    Fin.suc x ≟ᶠ Fin.suc y with x ≟ᶠ y
    Fin.suc x ≟ᶠ Fin.suc .x | yes refl = yes refl
    Fin.suc x ≟ᶠ Fin.suc y | no ¬p = no (λ { refl → ¬p refl })

  -- Identity for n addresses
  ιᴬ : (n : ℕ) → Bijᴬ n n

  foo : ∀ {n} → fromℕ n ∉ (Bij.to ⌜ ιᴬ n ⌝¹)

  ιᴬ ℕ.zero = ∅
  ιᴬ (ℕ.suc n) = _◅_ (n' , n') β {{p₁}} {{p₂}}  -- ( (ℕ.suc n , ℕ.suc n)) ◅ {!ιᴬ n!}
    where  n' = fromℕ n
           β : Bij (Fin (ℕ.suc n)) (Fin (ℕ.suc n))
           β = ⌜ ιᴬ n ⌝¹
           instance
             p₁ : n' ∉ (Bij.to β)
             p₁ = foo

             p₂ : n' ∉ (Bij.back β)
             p₂ =  {!!} -- (fromℕ n) ∉ (Bij.back β)

  foo {ℕ.zero} with Bij.to ⌜ ιᴬ ℕ.zero ⌝¹ (fromℕ ℕ.zero)
  ... | r = {!!}
  foo {ℕ.suc n} = {!!}
