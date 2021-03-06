open import Lattice

module Generic.Store.Base {{ð³ : Lattice}} (Ty : Set) (Value : Ty â Set) where

open import Data.Nat hiding (_â_)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
import Level as L

open import Generic.Memory Ty Value public

-- A store is a mapping from labels to labeled memories.
Store : Set
Store = (â : Label) â Memory â

-- Î£ [ â â¦ M ]Ë¢ updates store Î£ with â âabeâed memory M.
_[_â¦_]Ë¢ : Store -> (â : Label) -> Memory â -> Store
_[_â¦_]Ë¢  Î£ â M â' with â â â'
_[_â¦_]Ë¢ Î£ â M .â | yes refl = M
_[_â¦_]Ë¢ Î£ â M â' | no Â¬p = Î£ â'

-- Empty store
â : Store
â _ = []

-- Function extensionality (used for low-equivalence of stores)
postulate store-â¡ : Extensionality L.zero L.zero
