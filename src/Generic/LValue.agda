open import Lattice

module Generic.LValue {{𝑳 : Lattice}} (Ty : Set) (Value : Ty → Set) where

-- A generic wrapper interface for labeled values
record HasLabel : Set where
  field F : Ty → Ty -- Restrict the type to labeled values
        value : ∀ {τ} → Value (F τ) → Value τ
        label : ∀ {τ} → Value (F τ) → Label
