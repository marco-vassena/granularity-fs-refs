-- Generic typing context.

module Generic.Context (Ty : Set) where

open import Generic.Context.Base Ty as B using (
    Ctx
  ; _∷_
  ; []
  ; _++_
  ; _∈_
  ; here
  ; there
  ; _⊆_
  ; base
  ; cons
  ; drop
  ; refl-⊆
  ; drop-⊆₂
  ) public
