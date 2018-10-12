module FG.Types where

-- Types τ
data Ty : Set where
  unit : Ty                      -- Unit type
  _×_ : Ty → Ty → Ty             -- Pair
  _+_ : Ty → Ty → Ty             -- Sum
  _➔_ : (τ₁ t₂ : Ty) → Ty        -- Function
  𝓛 : Ty                        -- Label
  Ref : Ty → Ty                  -- Labeled mutable reference
  Id : Ty → Ty                   -- Identity type (needed for injectivity)

infixr 3 _➔_
infixr 3 _×_
infixr 3 _+_

-- Context (list of types)
open import Generic.Context Ty public
