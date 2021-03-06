module Generic.Calculus where

open import Data.List
open import Generic.Context using (Ctx)
open import Relation.Binary
open import Level
open import Lattice
open import Generic.Bijection

-- TODO: why is this here?
-- A simple flag to distinguish flow-insensitive (I) and
-- flow-sensitive (S) references
data Flow : Set where
  I S : Flow

-- A generic record for security calculi with well-typed syntax and
-- big-step semantics.
record Calculus {{π³ : Lattice}} : Setβ where
  field Ty : Set
        Input : Ctx Ty β Set
        IConf : Ctx Ty β Ty β Set
        FConf : Ty β Set
        Iβ¨_β© : Ty β Ty -- Generic type preservation in the semantics
        _ββ¨_β©_ : β {Ξ Ο} β IConf Ξ Iβ¨ Ο β© β Input Ξ β FConf Ο β Set
        Valid-Inputs : β {Ξ} {Ο} β IConf Ξ Ο β Input Ξ β  Set

        -- Low-equivalence
        _βα΄±β¨_,_β©_ : β {Ξ} β Input Ξ β Label β Bij β Input Ξ β Set
        _βα΄΅β¨_,_β©_ : β {Ξ Ο} β IConf Ξ Ο β Label β Bij β IConf Ξ Ο β Set
        _βαΆ β¨_,_β©_ : β {Ο} β FConf Ο β Label β Bij β FConf Ο β Set

-- TODO: here we could make the statement simpler (e.g., empty
-- memory/store, only boolean inputs, no assumptions about validity)
-- but this seems just more boring work.

-- Generic Termination-Insensitive Non-Interferencee property (TINI).
TINI : β {{π³ : Lattice}} β Calculus β Set
TINI πͺ = β {Ο Ξ ΞΈβ ΞΈβ A Ξ²} {cβ cβ : IConf Ξ Iβ¨ Ο β©} {cβ' cβ' : FConf Ο} β
              Valid-Inputs cβ ΞΈβ β
              Valid-Inputs cβ ΞΈβ β
              cβ ββ¨ ΞΈβ β© cβ' β
              cβ ββ¨ ΞΈβ β© cβ' β
              cβ βα΄΅β¨ A , Ξ² β© cβ β
              ΞΈβ βα΄±β¨ A , Ξ² β© ΞΈβ β
              β (Ξ» Ξ²' β Ξ² β Ξ²' Γ cβ' βαΆ β¨ A , Ξ²' β© cβ')
     where open Calculus πͺ
           open import Data.Product using (_Γ_ ; β)
