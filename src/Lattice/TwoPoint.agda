-- In this module we give a simple instantion of the 2-points lattice,
-- ð³ = {Low, High}, where High â¤ Low is the only disallowed flow.  We
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
_â_ : (lâ lâ : Label) -> Dec (lâ â¡ lâ)
Low â Low = yes refl
Low â High = no (Î» ())
High â Low = no (Î» ())
High â High = yes refl

-- Join
_â_ : Label â Label â Label
Low â ââ = ââ
High â ââ = High

infixr 5 _â_

-- Meet
_â_ : Label â Label â Label
Low â y = Low
High â y = y

infixr 5 _â_

-- Flow-to relation over Labels.
data _â_ : Label -> Label -> Set where
 Lâ : â (l : Label) -> Low â l
 HâH : High â High

-- High is the top of the lattice.
_âH : â (â : Label) â â â High
Low âH = Lâ High
High âH = HâH

-- â is decidable.
_â?_ : (lâ lâ : Label) -> Dec (lâ â lâ)
Low â? lâ = yes (Lâ lâ)
High â? Low = no (Î» ())
High â? High = yes HâH

-- â is reflexive.
refl-â : â {l} -> l â l
refl-â {Low} = Lâ Low
refl-â {High} = HâH

-- â is antisymmetric.
antisym-â : â {x y} â x â y â y â x â x â¡ y
antisym-â (Lâ .Low) (Lâ .Low) = refl
antisym-â HâH b = refl

-- â is transitive.
trans-â : â {lâ lâ lâ} -> lâ â lâ -> lâ â lâ -> lâ â lâ
trans-â (Lâ .Low) (Lâ lâ) = Lâ lâ
trans-â (Lâ .High) HâH = Lâ High
trans-â HâH HâH = HâH

--------------------------------------------------------------------------------
-- Algebraic properties of join _â_

sym-â : â (ââ ââ : Label) â (ââ â ââ) â¡ (ââ â ââ)
sym-â Low Low = refl
sym-â Low High = refl
sym-â High Low = refl
sym-â High High = refl

assoc-â : â ââ ââ ââ â (ââ â ââ) â ââ â¡ ââ â ââ â ââ
assoc-â Low ââ ââ = refl
assoc-â High ââ ââ = refl

--------------------------------------------------------------------------------
-- Algebraic properties of meet _â_

sym-â : â (ââ ââ : Label) â (ââ â ââ) â¡ (ââ â ââ)
sym-â Low Low = refl
sym-â Low High = refl
sym-â High Low = refl
sym-â High High = refl

assoc-â : â ââ ââ ââ â (ââ â ââ) â ââ â¡ ââ â ââ â ââ
assoc-â Low ââ ââ = refl
assoc-â High ââ ââ = refl

--------------------------------------------------------------------------------
-- Ordering properties of â and â

join-ââ : â ââ ââ â ââ â (ââ â ââ)
join-ââ Low ââ = Lâ ââ
join-ââ High ââ = HâH

join-ââ : â ââ ââ â ââ â (ââ â ââ)
join-ââ x y with join-ââ y x
... | p rewrite sym-â x y = p

join-ââ : â x y z â x â z â y â z â (x â y) â z
join-ââ .Low y z (Lâ .z) b = b
join-ââ .High y .High HâH b = HâH

--------------------------------------------------------------------------------
-- Ordering properties of â and â

meet-ââ : â x y â (x â y) â x
meet-ââ Low y = Lâ Low
meet-ââ High y = y âH

meet-ââ : â x y â (x â y) â y
meet-ââ Low y = Lâ y
meet-ââ High y = refl-â

meet-ââ : â x y z â z â x â z â y â z â (x â y)
meet-ââ x y .Low (Lâ .x) b = Lâ (x â y)
meet-ââ .High y .High HâH b = b

--------------------------------------------------------------------------------
-- Lattice instance

open import Relation.Binary
import Relation.Binary.Lattice as R
open import Data.Product
import Algebra.Structures as A
open import Algebra.FunctionProperties (_â¡_ {A = Label})

supremum : R.Supremum _â_ _â_
supremum x y = join-ââ x y , join-ââ x y , join-ââ x y

infimum : R.Infimum _â_ _â_
infimum = Î» x y â meet-ââ x y , meet-ââ x y , meet-ââ x y

isPreorder : IsPreorder _â¡_ _â_
isPreorder =
  record { isEquivalence = isEquivalence
         ; reflexive =  Î» { refl â refl-â }
         ; trans = trans-â }

isPartialOrder : IsPartialOrder _â¡_ _â_
isPartialOrder =
  record { isPreorder = isPreorder
         ; antisym = antisym-â }

isDecPartialOrder : IsDecPartialOrder _â¡_ _â_
isDecPartialOrder =
  record { isPartialOrder = isPartialOrder
         ; _â_ = _â_
         ; _â¤?_ = _â?_ }

â-absorbs-â : _â_ Absorbs _â_
â-absorbs-â Low y = refl
â-absorbs-â High y = refl

â-absorbs-â : _â_ Absorbs _â_
â-absorbs-â Low y = refl
â-absorbs-â High y = refl

absorptive : Absorptive _â_ _â_
absorptive = â-absorbs-â , â-absorbs-â

isLattice : A.IsLattice _â¡_ _â_ _â_
isLattice = record
              { isEquivalence = isEquivalence
              ; â¨-comm = sym-â
              ; â¨-assoc = assoc-â -- Î» x y z â sym (assoc-â x y z)
              ; â¨-cong = Î» { refl refl â refl }
              ; â§-comm = sym-â
              ; â§-assoc = assoc-â
              ; â§-cong = Î» { refl refl â refl }
              ; absorptive = absorptive
              }

isSecLattice : IsLattice _â_ _â_ _â_
isSecLattice = record
              { supremum = supremum
              ; infimum = infimum
              ; isDecPartialOrder = isDecPartialOrder
              ; isLattice = isLattice
              }

-- ð³Â² is the 2-point lattice, where High â¤ Low is the only disallowed
-- flow.
instance
  ð³Â² : Lattice
  ð³Â² = record
            { Carrier = Label
            ; _â¤_ = _â_
            ; _â¨_ = _â_
            ; _â§_ = _â_
            ; isSecurityLattice = isSecLattice
            }
