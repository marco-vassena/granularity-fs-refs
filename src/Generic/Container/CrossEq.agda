import Lattice as L

open import Generic.CrossEq
import Generic.ICrossEq as G

module Generic.Container.CrossEq
  {{π³ : L.Lattice}}
  {Tyβ : Set} {Tyβ : Set}
  (π» : CEq Tyβ Tyβ)
  (Label : Set)
  {Valueβ : Tyβ β Set} {Valueβ : Tyβ β Set}
  (π½ : G.ICEq Label π» Valueβ Valueβ)
  where

open CEq π» renaming ( _ββ_ to _ββα΅_
                    ; β¦_β§ to β¦_β§α΅
                    ; refl-ββ to refl-ββα΅)
open import Generic.ICrossEq Label π»

open ICEq π½ renaming ( _βββ¨_β©_ to _βββ¨_β©β±½_
                     ; _βββ¨_,_β©_ to _βββ¨_,_β©β±½_
                     ; β¦_β§ to β¦_β§β±½)

import Generic.Container

open import Generic.Container Label Tyβ Valueβ as S
open import Generic.Container Label Tyβ Valueβ as T

data _ββ_ {β} : T.Container β β S.Container β β Set where
  nil : T.[] ββ S.[]
  cons : β {Cβ Cβ Οβ Οβ} {vβ : Valueβ Οβ} {vβ : Valueβ Οβ} β
           (Οβ : Οβ ββα΅ Οβ) β vβ βββ¨ β , Οβ β©β±½ vβ β Cβ ββ Cβ β (vβ T.β· Cβ) ββ (vβ S.β· Cβ)

open import Generic.Container.Convert Label {Tyβ} {Tyβ} {Valueβ} {Valueβ}  β¦_β§α΅ β¦_β§β±½
  renaming (βͺ_β«αΆ to β¦_β§αΆ)

refl-ββ : β {β} β (C : S.Container β) β β¦ C β§αΆ ββ C
refl-ββ S.[] = nil
refl-ββ (v S.β· M) = cons _ (refl-βββ¨ _ β© v) (refl-ββ M)


-- Extending related memories with related values gives related memoryes.
new-ββ : β {β Ο} {M : T.Container β} {M' : S.Container β} {vβ : Valueβ Ο} {vβ : Valueβ β¦ Ο β§α΅} β
        let instance _ = refl-ββα΅ Ο in
           M ββ M' β
           vβ βββ¨ β β©β±½ vβ β
           (M T.β·α΄Ώ vβ) ββ (M' S.β·α΄Ώ vβ)
new-ββ nil vβ = cons _ vβ nil
new-ββ (cons Οβ vβ' Mβ) vβ = cons Οβ vβ' (new-ββ Mβ vβ)

open import Relation.Binary.PropositionalEquality
open import Data.Product renaming (_,_ to _β§_)

β₯_β₯-ββ : β {β} {C : T.Container β} {C' : S.Container β} β C ββ C' β T.β₯ C β₯ β‘ S.β₯ C' β₯
β₯ nil β₯-ββ = refl
β₯ cons _ _ Cβ β₯-ββ rewrite β₯ Cβ β₯-ββ = refl

lookup-ββ : β {n β Ο} {vβ : Valueβ Ο} {C : T.Container β} {C' : S.Container β} β
                 n S.β¦ vβ β C' β
                 C ββ C' β
                 Ξ£ (Valueβ β¦ Ο β§α΅) (Ξ» vβ β (n T.β¦ vβ β C) Γ (vβ βββ¨ β , refl-ββα΅ _ β©β±½ vβ))
lookup-ββ S.Here (cons Οβ vβ _) with β Οβ  β
... | refl rewrite !-ββ Οβ (refl-ββα΅ _) =  _ β§ T.Here β§ vβ
lookup-ββ (S.There ββ) (cons _ _ Cβ) with lookup-ββ ββ Cβ
... | _ β§ ββ β§ vβ = _ β§ T.There ββ β§ vβ

unlift-β¦_β§β  : β {n β Οβ} {vβ : Valueβ Οβ} {C' : S.Container β} β
               n T.β¦ vβ β β¦ C' β§αΆ β
               β¦ C' β§αΆ ββ C' β
               β (Ξ» Οβ β Ξ£ ( (Valueβ Οβ) Γ (Οβ β‘ β¦ Οβ β§α΅) )
                 (Ξ» { (vβ β§ refl)  β (n S.β¦ vβ β C') Γ vβ β‘ β¦ vβ β§β±½ β } ))
unlift-β¦_β§β () nil
unlift-β¦_β§β T.Here (cons {vβ = vβ} Οβ x xβ) = _ β§ (vβ β§ refl) β§ S.Here β§ refl
unlift-β¦_β§β (T.There ββ) (cons Οβ x Cβ) with unlift-β¦ ββ β§β Cβ
... | Ο β§ (vβ β§ refl) β§ βββ² β§ refl =  Ο β§ (vβ β§ refl) β§ (S.There βββ²) β§ refl

write-ββ : β {n β Ο} {vβ : Valueβ Ο} {vβ : Valueβ β¦ Ο β§α΅} {Cβ : T.Container β} {Cβ Cβ' : S.Container β} β
             vβ βββ¨ β , refl-ββα΅ _ β©β±½ vβ β
             Cβ' S.β Cβ [ n β¦ vβ ] β
             Cβ ββ Cβ β
             β (Ξ» Cβ' β Cβ' T.β Cβ [ n β¦ vβ ] Γ Cβ' ββ Cβ')
write-ββ vββ² S.Here (cons Οβ vβ Cβ) with β Οβ  β
... | refl rewrite !-ββ Οβ (refl-ββα΅ _) = _ β§ T.Here β§ (cons _ vββ² Cβ)
write-ββ vββ² (S.There Cβ) (cons _ vβ Cβ) with write-ββ vββ² Cβ Cβ
... | _ β§ ββ β§ Cββ² = _ β§ T.There ββ β§ cons _ vβ Cββ²
