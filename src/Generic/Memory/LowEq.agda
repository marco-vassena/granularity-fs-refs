open import Lattice
open import Relation.Binary
open import Generic.Bijection hiding (_â¦_)

module Generic.Memory.LowEq
  {Ty : Set}
  {Value : Ty â Set}
  {{ð³ : Lattice}}
  (_ââ¨_â©â±½_ : IProps.Relá´® Ty Value)
  (A : Label) where

open import Generic.Memory Ty Value public
open import Data.Unit hiding (_â_ ; _â¤_)
open import Relation.Nullary

data Memory-âá´¹ {â} (Î² : Bij) : Memory â â Memory â â Set where
  [] : Memory-âá´¹ Î² [] []
  _â·_ : â {Ï Mâ Mâ} {vâ vâ : Value Ï} â
          (vââvâ : vâ ââ¨ Î² â©â±½ vâ) (MââMâ : Memory-âá´¹ Î² Mâ Mâ) â
          Memory-âá´¹ Î² (vâ â· Mâ) (vâ â· Mâ)

-- Pointwise low-equivalence (for observable memories)
_ââ¨_â©á´¹_ : â {â} â Memory â â Bij â Memory â â Set
Mâ ââ¨ Î² â©á´¹ Mâ = Memory-âá´¹ Î² Mâ Mâ


-- Any pair of non-observable memories are related, otherwise they are related pointwise
_ââ¨_,_â©á´¹_ : â {â} â Memory â â Bij â Dec (â â A) â Memory â â Set
Mâ ââ¨ Î² , yes p â©á´¹ Mâ = Mâ ââ¨ Î² â©á´¹ Mâ
Mâ ââ¨ _ , no Â¬p â©á´¹ Mâ = â¤

_ââ¨_â©á´¹â²_ : â {â} â Memory â â Bij â Memory â â Set
Mâ ââ¨ Î² â©á´¹â² Mâ = Mâ ââ¨ Î² , _ â? A â©á´¹ Mâ

â_âá´¹ : â {â Î²} {Mâ Mâ : Memory â} â Mâ ââ¨ Î² â©á´¹ Mâ â Mâ ââ¨ Î² , â â? A â©á´¹ Mâ
â_âá´¹ {â} MââMâ with â â? A
... | yes ââA = MââMâ
... | no ââ¤A = tt

-- module V = IProps Ty Value

-- open import Data.Nat
open import Generic.ValidEquivalence Ty Value

module âá´¹-Props
  (ð½ : IsValidEquivalence _ââ¨_â©â±½_)
  -- (Validâ±½ : â {Ï} â â â Value Ï â Set)
  -- (valid-â¤ : â {Ï n} (v : Value Ï) â Validâ±½ n v â V.Dom ð½ v â¤ n)
  where

  open import Generic.Value.LowEq {Ty} {Value} _ââ¨_â©â±½_

  open IsValidEquivalence ð½ renaming
    ( â¥_â¥ to â£_â£â±½
    ; reflá´® to refl-ââ±½
    ; symá´® to sym-ââ±½
    ; transá´® to trans-ââ±½
    ; wkená´® to wken-ââ±½
    ; Valid to Validâ±½
    )


  open IProps.IsEquivalenceá´® -- Label ?
  open import Data.Nat using (â ; _â¤_ ; _<_ ; sâ¤s ; zâ¤n) renaming (_â_ to _âá´º_)
  open import Data.Nat.Properties

  â£_â£á´¹ : â {â} â Memory â â â
  â£ [] â£á´¹ = 0
  â£ v â· M â£á´¹ = â£ v â£â±½ âá´º â£ M â£á´¹

  infixl 1 â£_â£á´¹

  module âá´¹-Equivalence where

    open IProps Label Memory
    open import Generic.Memory.Valid isValid
    open import Data.Product

    wken-âá´¹ : Wkená´® _ââ¨_â©á´¹_
    wken-âá´¹ nâ¤m [] = []
    wken-âá´¹ nâ¤m (vââvâ â· MââMâ) = wken-ââ±½ nâ¤m vââvâ â· wken-âá´¹ nâ¤m MââMâ

    -- Reflexive
    refl-âá´¹ :  â {â n} {M : Memory â} {{validá´¹ : Validá´¹ n M}} â M ââ¨ Î¹ n â©á´¹ M
    refl-âá´¹ {M = []} {{validá´¹}} = []
    refl-âá´¹ {M = x â· M} {{validá´¹}} = ââ±½ â· refl-âá´¹ {M = M} {{ tail-validá´¹ validá´¹ }}
      where ââ±½ = wken-ââ±½ (Î¹-â (valid-â¤ _ (validá´¹ Here))) refl-ââ±½

    -- Symmetric
    sym-âá´¹ : Symmetricá´®  _ââ¨_â©á´¹_
    sym-âá´¹ [] = []
    sym-âá´¹ (vââvâ â· MââMâ) = sym-ââ±½ vââvâ â· sym-âá´¹ MââMâ

    -- Transitive
    trans-âá´¹ : Transitiveá´® _ââ¨_â©á´¹_ -- {â} â {Mâ Mâ Mâ : Memory â} â Mâ âá´¹ Mâ â Mâ âá´¹ Mâ â Mâ âá´¹ Mâ
    trans-âá´¹ [] [] = []
    trans-âá´¹ (vââvâ â· MââMâ) (vââvâ â· MââMâ) = trans-ââ±½ vââvâ vââvâ â· trans-âá´¹ MââMâ MââMâ

    -- Does not hold because we have side-conditions on the domain
    -- âá´¹-isEquivalence : IsEquivalenceá´® _ââ¨_â©á´¹_
    -- âá´¹-isEquivalence =
    --   record { Dom = â£_â£á´¹
    --          ; wkená´® = wken-âá´¹
    --          ; reflá´® = refl-âá´¹
    --          ; symá´® = sym-âá´¹
    --          ; transá´® = trans-âá´¹ }

  open âá´¹-Equivalence public

  --------------------------------------------------------------------------------

  module âá´¹â²-Equivalence  where

  open IProps Label Memory
  open import Generic.Memory.Valid isValid

  wken-âá´¹â² : Wkená´® _ââ¨_â©á´¹â²_
  wken-âá´¹â² {a = â} nâ¤m x with â â? A
  wken-âá´¹â² {a} nâ¤m x | yes p = wken-âá´¹ nâ¤m x
  wken-âá´¹â² {a} nâ¤m x | no Â¬p = tt

  refl-âá´¹â² : â {â n} {M : Memory â} {{validá´¹ : Validá´¹ n M}} â M ââ¨ Î¹ n â©á´¹â² M
  refl-âá´¹â² {{validá´¹}} = â refl-âá´¹ {{ validá´¹ }} âá´¹

  sym-âá´¹â² : Symmetricá´®  _ââ¨_â©á´¹â²_
  sym-âá´¹â² {a = â} x with â â? A
  sym-âá´¹â² {a} x | yes p = sym-âá´¹ x
  sym-âá´¹â² {a} x | no Â¬p = tt

  trans-âá´¹â² : Transitiveá´®  _ââ¨_â©á´¹â²_
  trans-âá´¹â² {a = â} x y with â â? A
  trans-âá´¹â² {a} x y | yes p = trans-âá´¹ x y
  trans-âá´¹â² {a} x y | no Â¬p = tt

  -- âá´¹â²-isEquivalence : IsEquivalenceá´® _ââ¨_â©á´¹â²_
  -- âá´¹â²-isEquivalence =
  --   record { Dom = â£_â£á´¹
  --          ; wkená´® = wken-âá´¹â²
  --          ; reflá´® = refl-âá´¹â²
  --          ; symá´® = sym-âá´¹â²
  --          ; transá´® = trans-âá´¹â² }

  -- open âá´¹â²-Equivalence public


  -- Not sure if this API is better, but they don't fix exactly our Equivalenceá´® definitions
  -- refl-ââ¨_â©á´¹ : â {â} {M : Memory â} (x : Dec (â â A)) â M ââ¨ Î¹ â£ M â£á´¹ , x â©á´¹ M
  -- refl-ââ¨ yes p â©á´¹ = refl-âá´¹
  -- refl-ââ¨ no Â¬p â©á´¹ = tt

  sym-ââ¨_â©á´¹ : â {â Î²} {Mâ Mâ : Memory â} (x : Dec (â â A)) â Mâ ââ¨ Î² , x â©á´¹ Mâ â Mâ ââ¨ Î² â»Â¹ , x â©á´¹ Mâ
  sym-ââ¨ yes p â©á´¹ MââMâ = sym-âá´¹ MââMâ
  sym-ââ¨ no Â¬p â©á´¹ MââMâ = tt

  trans-ââ¨_â©á´¹ : â {â Î²â Î²â} {Mâ Mâ Mâ : Memory â} â (x : Dec (â â A)) â
                Mâ ââ¨ Î²â , x â©á´¹ Mâ â Mâ ââ¨ Î²â , x â©á´¹ Mâ â Mâ ââ¨ Î²â â Î²â , x â©á´¹ Mâ
  trans-ââ¨ yes p â©á´¹ MââMâ MââMâ = trans-âá´¹ MââMâ MââMâ
  trans-ââ¨ no Â¬p â©á´¹ MââMâ MââMâ = tt

    -- ââ¨_â©á´¹-isEquivalence : â {â} (x : Dec (â â A)) â IsEquivalence (Î» (Mâ Mâ : Memory â) â Mâ ââ¨ x â©á´¹ Mâ)
    -- ââ¨ x â©á´¹-isEquivalence = record { refl = refl-ââ¨ x â©á´¹ ; sym = sym-ââ¨ x â©á´¹ ; trans = trans-ââ¨ x â©á´¹ }

--   open ââ¨_â©á´¹-Equivalence public

  --------------------------------------------------------------------------------
  open import Relation.Binary.PropositionalEquality

  -- Low memories have the same length
  â¥_â¥-â¡ : â {â Î²} {Mâ Mâ : Memory â} â Mâ ââ¨ Î² â©á´¹ Mâ â â¥ Mâ â¥á´¹ â¡ â¥ Mâ â¥á´¹
  â¥ [] â¥-â¡ = refl
  â¥ x â· MââMâ â¥-â¡ rewrite â¥ MââMâ â¥-â¡ = refl

  new-âá´¹ : â {Ï â Î²} {Mâ Mâ : Memory â} {vâ vâ : Value Ï} â
                Mâ ââ¨ Î² â©á´¹ Mâ â vâ ââ¨ Î² â©â±½ vâ â (snocá´¹ Mâ vâ) ââ¨ Î² â©á´¹ (snocá´¹ Mâ vâ)
  new-âá´¹ [] vââvâ = vââvâ â· []
  new-âá´¹ (vââvâ' â· MââMâ) vââvâ = vââvâ' â· (new-âá´¹ MââMâ vââvâ)

  update-âá´¹ : â {â Ï n Î²} {Mâ Mâ' Mâ Mâ' : Memory â} {vâ vâ : Value Ï} â
                Mâ ââ¨ Î² â©á´¹ Mâ â
                vâ ââ¨ Î² â©â±½ vâ â
                Mâ' â Mâ [ n â¦ vâ ]á´¹ â
                Mâ' â Mâ [ n â¦ vâ ]á´¹ â
                Mâ' ââ¨ Î² â©á´¹ Mâ'
  update-âá´¹ (_ â· MââMâ) vââvâ Here Here = vââvâ â· MââMâ
  update-âá´¹ (vââvâ' â· MââMâ) vââvâ (There uâ) (There uâ) = vââvâ' â· update-âá´¹ MââMâ vââvâ uâ uâ

  read-âá´¹ : â {â Ï n Î²} {Mâ Mâ : Memory â} {vâ vâ : Value Ï} â
              Mâ ââ¨ Î² â©á´¹ Mâ â
              n â¦ vâ âá´¹ Mâ â
              n â¦ vâ âá´¹ Mâ â
              vâ ââ¨ Î² â©â±½ vâ
  read-âá´¹ (vââvâ â· _) Here Here = vââvâ
  read-âá´¹ (_ â· MââMâ) (There râ) (There râ) = read-âá´¹ MââMâ râ râ

  --------------------------------------------------------------------------------
