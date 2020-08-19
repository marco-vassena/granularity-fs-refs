module Generic.ValidEquivalence (A : Set) (F : A → Set) where

open import Data.Nat
open import Generic.Bijection
open IProps A F
open import Generic.Valid A F

record IsValidEquivalence (R : Relᴮ) : Set₁ where
  field ∥_∥ : ∀ {a} → F a → ℕ
        isValid : IsValid ∥_∥
        isEquiv : IsEquivalenceᴮ R ∥_∥

  open IsValid isValid public
  open IsEquivalenceᴮ isEquiv public
