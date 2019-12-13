module FG.Types where

open import Generic.Calculus using (Flow; S; I) public

-- Types τ
data Ty : Set where
  unit : Ty                      -- Unit type
  _×_ : Ty → Ty → Ty             -- Pair
  _+_ : Ty → Ty → Ty             -- Sum
  _➔_ : (τ₁ t₂ : Ty) → Ty        -- Function
  𝓛 : Ty                        -- Label
  Ref : Flow → Ty → Ty           -- Labeled mutable reference
  Id : Ty → Ty                   -- Identity type (needed for injectivity)

infixr 3 _➔_
infixr 3 _×_
infixr 3 _+_

Bool : Ty
Bool = unit + unit

-- Context (list of types)
open import Generic.Context Ty public
