open import Lattice

module FG {{ð³ : Lattice}} where

-- Types and context
open import FG.Types public

-- Well-typed Syntax
open import FG.Syntax public

-- Big-step semantics
open import FG.Semantics public

-- References are valid
open import FG.Valid public

-- Bijections
open import Generic.Bijection hiding (id)

--------------------------------------------------------------------------------
-- Top-level low-equivalence bindings that explicitly take the
-- adversary security level

_âá´µâ¨_,_â©_ : â {Ï Î} â IConf Î Ï â Label â Bij â IConf Î Ï â Set
câ âá´µâ¨ A , Î² â© câ = câ ââ¨ Î² â©á´µ câ
  where open import FG.LowEq A

_âá¶â¨_,_â©_ : â {Ï} â FConf Ï â Label â Bij â FConf Ï â Set
câ âá¶â¨ A , Î² â© câ = câ ââ¨ Î² â©á¶ câ
  where open import FG.LowEq A

_ââ±½â¨_,_â©_ : â {Ï} â Value Ï â Label â Bij â Value Ï â Set
vâ ââ±½â¨ A , Î² â© vâ = vâ ââ¨ Î² â©â±½ vâ
  where open import FG.LowEq A

_âá´¿â¨_,_â©_ : â {Ï} â Raw Ï â Label â Bij â Raw Ï â Set
râ âá´¿â¨ A , Î² â© râ = râ ââ¨ Î² â©á´¿ râ
  where open import FG.LowEq A

_âá´±â¨_,_â©_ : â {Î} â Env Î â Label â Bij â Env Î â Set
râ âá´±â¨ A , Î² â© râ = râ ââ¨ Î² â©á´± râ
  where open import FG.LowEq A

_âá´¹â¨_,_â©_ : â {â} â Memory â â Label â Bij â Memory â â Set
Mâ âá´¹â¨ A , Î² â© Mâ = Mâ ââ¨ Î² , _ â? A â©á´¹ Mâ
  where open import FG.LowEq A

_âË¢â¨_,_â©_ : Store â Label â Bij â Store â Set
Î£â âË¢â¨ A , Î² â© Î£â = Î£â ââ¨ Î² â©Ë¢ Î£â
  where open import FG.LowEq A

_âá´´â¨_,_â©_ : Heap â Label â Bij â Heap â Set
Î¼â âá´´â¨ A , Î² â© Î¼â = Î¼â ââ¨ Î² â©á´´ Î¼â
  where open import FG.LowEq A

_âá´¾â¨_,_â©_ : PState â Label â Bij â PState â Set
pâ âá´¾â¨ A , Î² â© pâ = pâ ââ¨ Î² â©á´¾ pâ
  where open import FG.LowEq A

--------------------------------------------------------------------------------
-- Calculus record

open import Generic.Calculus
open import Function
open import Data.Product renaming (_Ã_ to _â§_)
open import Relation.Binary.PropositionalEquality

Î»^FG : Calculus
Î»^FG = record
         { Ty = Ty
         ; Input = Î» Î â (Env Î) â§ Label
         ; IConf = IConf
         ; FConf = FConf
         ; Valid-Inputs = Î» { c (Î¸ , â) â Valid-Inputs c Î¸ }
         ; Iâ¨_â© = id
         ; _ââ¨_â©_ = Î» { c (Î¸ , pc) c' â c ââ¨ Î¸ , pc â© c' }
         ; _âá´±â¨_,_â©_ = Î» { (Î¸â , pcâ) A Î² (Î¸â , pcâ) â Î¸â âá´±â¨ A , Î² â© Î¸â â§ pcâ â¡ pcâ}
         ; _âá´µâ¨_,_â©_ = _âá´µâ¨_,_â©_
         ; _âá¶ â¨_,_â©_ = _âá¶â¨_,_â©_
         }

Î»^FG-TINI : TINI Î»^FG
Î»^FG-TINI {A = A} isVâ isVâ cââ cââ cââcâ (Î¸ââÎ¸â , refl)
  = tini {{ isVâ }} {{ isVâ }} cââ cââ cââcâ Î¸ââÎ¸â
  where open import FG.Security A
        open Calculus Î»^FG
