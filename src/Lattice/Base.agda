-- The following Definition of security lattice includes both the
-- standard definition based on partially-ordered sets
-- (Relation.Binary.Lattice) and the standard algebraic definition
-- (Algebra.Structures). It should be possible to relax
-- SecurityLattice to require only one of them (those definitions are
-- equivalent), but this result is not part of the standard library
-- and beyond our scope.  Additionally the security lattice requires
-- decidable equality and ordering.

module Lattice.Base where

open import Relation.Binary
open import Relation.Binary.Lattice
open import Relation.Binary.PropositionalEquality
open import Algebra.FunctionProperties
import Algebra.Structures as S
open import Level

-- Lattice interface.
record IsSecurityLattice {a ℓ₁ ℓ₂} {A : Set a}
                 (_≈_ : Rel A ℓ₁) -- The underlying equality.
                 (_≤_ : Rel A ℓ₂) -- The partial order.
                 (_∨_ : Op₂ A)    -- The join operation.
                 (_∧_ : Op₂ A)    -- The meet operation.
                 : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where

  field
    supremum       : Supremum _≤_ _∨_              -- Order properties (join)
    infimum        : Infimum _≤_ _∧_               -- Order properties (meet)
    isDecPartialOrder : IsDecPartialOrder _≈_ _≤_  -- Decidable partial order
    isLattice : S.IsLattice _≈_ _∨_ _∧_            -- Algebraic properties

  open IsDecPartialOrder isDecPartialOrder public

  isJoinSemilattice : IsJoinSemilattice _≈_ _≤_ _∨_
  isJoinSemilattice = record
    { isPartialOrder = isPartialOrder
    ; supremum       = supremum
    }

  isMeetSemilattice : IsMeetSemilattice _≈_ _≤_ _∧_
  isMeetSemilattice = record
    { isPartialOrder = isPartialOrder
    ; infimum        = infimum
    }

  open S.IsLattice isLattice
    using ( ∨-comm
          ; ∨-assoc
          ; ∨-cong
          ; ∧-comm
          ; ∧-assoc
          ; ∧-cong
          ; absorptive ) public

-- Generic security lattice.
record SecurityLattice c ℓ : Set (suc (c ⊔ ℓ)) where
  infix  4 _≤_
  infixr 6 _∨_
  infixr 7 _∧_
  field
    Carrier   : Set c
    _≤_       : Rel Carrier ℓ  -- The partial order.
    _∨_       : Op₂ Carrier     -- The join operation.
    _∧_       : Op₂ Carrier     -- The meet operation.
    -- Here we restrict ourselves to propositional equality.
    -- This is just for convenience.
    isSecurityLattice : IsSecurityLattice _≡_ _≤_ _∨_ _∧_

  open IsSecurityLattice isSecurityLattice hiding (refl  ; trans) public
