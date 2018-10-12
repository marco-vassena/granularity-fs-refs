-- In this module we give a simple instantion of the 2-points lattice,
-- 𝑳 = {Low, High}, where High ⋤ Low is the only disallowed flow.  We
-- define the label set, the can-flow-to relation, join and meet
-- operations.
--
-- We then proof that this structure is a Lattice according to the
-- definition given in module Lattice.

module Lattice.TwoPoint where

open import Lattice using (Lattice ; IsLattice)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality hiding (isPreorder)
open import Data.Empty

-- Low and High labels.
data Label : Set where
 Low : Label
 High : Label

-- Decidable equality over Label
_≟_ : (l₁ l₂ : Label) -> Dec (l₁ ≡ l₂)
Low ≟ Low = yes refl
Low ≟ High = no (λ ())
High ≟ Low = no (λ ())
High ≟ High = yes refl

-- Join
_⊔_ : Label → Label → Label
Low ⊔ ℓ₂ = ℓ₂
High ⊔ ℓ₂ = High

infixr 5 _⊔_

-- Meet
_⊓_ : Label → Label → Label
Low ⊓ y = Low
High ⊓ y = y

infixr 5 _⊓_

-- Flow-to relation over Labels.
data _⊑_ : Label -> Label -> Set where
 L⊑ : ∀ (l : Label) -> Low ⊑ l
 H⊑H : High ⊑ High

-- High is the top of the lattice.
_⊑H : ∀ (ℓ : Label) → ℓ ⊑ High
Low ⊑H = L⊑ High
High ⊑H = H⊑H

-- ⊑ is decidable.
_⊑?_ : (l₁ l₂ : Label) -> Dec (l₁ ⊑ l₂)
Low ⊑? l₂ = yes (L⊑ l₂)
High ⊑? Low = no (λ ())
High ⊑? High = yes H⊑H

-- ⊑ is reflexive.
refl-⊑ : ∀ {l} -> l ⊑ l
refl-⊑ {Low} = L⊑ Low
refl-⊑ {High} = H⊑H

-- ⊑ is antisymmetric.
antisym-⊑ : ∀ {x y} → x ⊑ y → y ⊑ x → x ≡ y
antisym-⊑ (L⊑ .Low) (L⊑ .Low) = refl
antisym-⊑ H⊑H b = refl

-- ⊑ is transitive.
trans-⊑ : ∀ {l₁ l₂ l₃} -> l₁ ⊑ l₂ -> l₂ ⊑ l₃ -> l₁ ⊑ l₃
trans-⊑ (L⊑ .Low) (L⊑ l₃) = L⊑ l₃
trans-⊑ (L⊑ .High) H⊑H = L⊑ High
trans-⊑ H⊑H H⊑H = H⊑H

--------------------------------------------------------------------------------
-- Algebraic properties of join _⊔_

sym-⊔ : ∀ (ℓ₁ ℓ₂ : Label) → (ℓ₁ ⊔ ℓ₂) ≡ (ℓ₂ ⊔ ℓ₁)
sym-⊔ Low Low = refl
sym-⊔ Low High = refl
sym-⊔ High Low = refl
sym-⊔ High High = refl

assoc-⊔ : ∀ ℓ₁ ℓ₂ ℓ₃ → (ℓ₁ ⊔ ℓ₂) ⊔ ℓ₃ ≡ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃
assoc-⊔ Low ℓ₂ ℓ₃ = refl
assoc-⊔ High ℓ₂ ℓ₃ = refl

--------------------------------------------------------------------------------
-- Algebraic properties of meet _⊓_

sym-⊓ : ∀ (ℓ₁ ℓ₂ : Label) → (ℓ₁ ⊓ ℓ₂) ≡ (ℓ₂ ⊓ ℓ₁)
sym-⊓ Low Low = refl
sym-⊓ Low High = refl
sym-⊓ High Low = refl
sym-⊓ High High = refl

assoc-⊓ : ∀ ℓ₁ ℓ₂ ℓ₃ → (ℓ₁ ⊓ ℓ₂) ⊓ ℓ₃ ≡ ℓ₁ ⊓ ℓ₂ ⊓ ℓ₃
assoc-⊓ Low ℓ₂ ℓ₃ = refl
assoc-⊓ High ℓ₂ ℓ₃ = refl

--------------------------------------------------------------------------------
-- Ordering properties of ⊑ and ⊔

join-⊑₁ : ∀ ℓ₁ ℓ₂ → ℓ₁ ⊑ (ℓ₁ ⊔ ℓ₂)
join-⊑₁ Low ℓ₂ = L⊑ ℓ₂
join-⊑₁ High ℓ₂ = H⊑H

join-⊑₂ : ∀ ℓ₁ ℓ₂ → ℓ₂ ⊑ (ℓ₁ ⊔ ℓ₂)
join-⊑₂ x y with join-⊑₁ y x
... | p rewrite sym-⊔ x y = p

join-⊑₃ : ∀ x y z → x ⊑ z → y ⊑ z → (x ⊔ y) ⊑ z
join-⊑₃ .Low y z (L⊑ .z) b = b
join-⊑₃ .High y .High H⊑H b = H⊑H

--------------------------------------------------------------------------------
-- Ordering properties of ⊑ and ⊓

meet-⊑₁ : ∀ x y → (x ⊓ y) ⊑ x
meet-⊑₁ Low y = L⊑ Low
meet-⊑₁ High y = y ⊑H

meet-⊑₂ : ∀ x y → (x ⊓ y) ⊑ y
meet-⊑₂ Low y = L⊑ y
meet-⊑₂ High y = refl-⊑

meet-⊑₃ : ∀ x y z → z ⊑ x → z ⊑ y → z ⊑ (x ⊓ y)
meet-⊑₃ x y .Low (L⊑ .x) b = L⊑ (x ⊓ y)
meet-⊑₃ .High y .High H⊑H b = b

--------------------------------------------------------------------------------
-- Lattice instance

open import Relation.Binary
import Relation.Binary.Lattice as R
open import Data.Product
import Algebra.Structures as A
open import Algebra.FunctionProperties (_≡_ {A = Label})

supremum : R.Supremum _⊑_ _⊔_
supremum x y = join-⊑₁ x y , join-⊑₂ x y , join-⊑₃ x y

infimum : R.Infimum _⊑_ _⊓_
infimum = λ x y → meet-⊑₁ x y , meet-⊑₂ x y , meet-⊑₃ x y

isPreorder : IsPreorder _≡_ _⊑_
isPreorder =
  record { isEquivalence = isEquivalence
         ; reflexive =  λ { refl → refl-⊑ }
         ; trans = trans-⊑ }

isPartialOrder : IsPartialOrder _≡_ _⊑_
isPartialOrder =
  record { isPreorder = isPreorder
         ; antisym = antisym-⊑ }

isDecPartialOrder : IsDecPartialOrder _≡_ _⊑_
isDecPartialOrder =
  record { isPartialOrder = isPartialOrder
         ; _≟_ = _≟_
         ; _≤?_ = _⊑?_ }

⊔-absorbs-⊓ : _⊔_ Absorbs _⊓_
⊔-absorbs-⊓ Low y = refl
⊔-absorbs-⊓ High y = refl

⊓-absorbs-⊔ : _⊓_ Absorbs _⊔_
⊓-absorbs-⊔ Low y = refl
⊓-absorbs-⊔ High y = refl

absorptive : Absorptive _⊔_ _⊓_
absorptive = ⊔-absorbs-⊓ , ⊓-absorbs-⊔

isLattice : A.IsLattice _≡_ _⊔_ _⊓_
isLattice = record
              { isEquivalence = isEquivalence
              ; ∨-comm = sym-⊔
              ; ∨-assoc = assoc-⊔ -- λ x y z → sym (assoc-⊔ x y z)
              ; ∨-cong = λ { refl refl → refl }
              ; ∧-comm = sym-⊓
              ; ∧-assoc = assoc-⊓
              ; ∧-cong = λ { refl refl → refl }
              ; absorptive = absorptive
              }

isSecLattice : IsLattice _⊑_ _⊔_ _⊓_
isSecLattice = record
              { supremum = supremum
              ; infimum = infimum
              ; isDecPartialOrder = isDecPartialOrder
              ; isLattice = isLattice
              }

-- 𝑳² is the 2-point lattice, where High ⋤ Low is the only disallowed
-- flow.
instance
  𝑳² : Lattice
  𝑳² = record
            { Carrier = Label
            ; _≤_ = _⊑_
            ; _∨_ = _⊔_
            ; _∧_ = _⊓_
            ; isSecurityLattice = isSecLattice
            }
