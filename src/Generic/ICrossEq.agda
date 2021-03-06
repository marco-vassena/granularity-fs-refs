-- Indexed cross equivalence

open import Generic.CrossEq

module Generic.ICrossEq
  {Tyβ : Set} {Tyβ : Set}
  (Label : Set)
  (π» : CEq Tyβ Tyβ) where

open CEq π» renaming (_ββ_ to _ββα΅_ ; β¦_β§ to β¦_β§α΅ ; refl-ββ to refl-ββα΅)
open import Relation.Binary.PropositionalEquality

record ICEq (Valueβ : Tyβ β Set) (Valueβ : Tyβ β Set) : Setβ where
  field
    β¦_β§ : β {Οβ} β Valueβ Οβ β Label β Valueβ β¦ Οβ β§α΅
    _βββ¨_,_β©_ : β {Οβ Οβ} β Valueβ Οβ β Label β Οβ ββα΅ Οβ  β Valueβ Οβ β Set
    -- ix-ββ : β {Οβ Οβ β} {vβ : Valueβ Οβ} {vβ : Valueβ Οβ} β
    --            vβ βββ¨ β β© vβ β Οβ ββα΅ Οβ
    refl-βββ¨_β© : β {Οβ} pc (v : Valueβ Οβ) β (β¦ v β§ pc) βββ¨ pc , refl-ββα΅ _  β© v

  _βββ¨_β©_ :  β {Οβ Οβ} {{Οβ : Οβ ββα΅ Οβ}} β Valueβ Οβ β Label β Valueβ Οβ β Set
  _βββ¨_β©_ {{Οβ}} vβ β vβ = vβ βββ¨ β , Οβ β© vβ


  -- where
    -- where
    --   instance _ = refl-ββα΅
