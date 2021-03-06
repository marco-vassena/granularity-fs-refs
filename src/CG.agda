open import Lattice

module CG {{ð³ : Lattice}} where

-- Types and context
open import CG.Types public

-- Well-typed Syntax
open import CG.Syntax public

-- Big-step semantics
open import CG.Semantics public

-- References are valid
open import CG.Valid public

-- Bijections
open import Generic.Bijection

--------------------------------------------------------------------------------
-- Top-level L-equivalence bindings that explicitly take the attacker
-- security level.

_âá´µâ¨_,_â©_ : â {Ï Î} â EConf Î Ï â Label â Bij â EConf Î Ï â Set
câ âá´µâ¨ A , Î² â© câ = câ ââ¨ Î² â©á´µ câ
  where open import CG.LowEq A

_ââ±½â¨_,_â©_ : â {Ï} â Value Ï â Label â Bij â Value Ï â Set
vâ ââ±½â¨ A , Î² â© vâ = vâ ââ¨ Î² â©â±½ vâ
  where open import CG.LowEq A

_âá´±â¨_,_â©_ : â {Î} â Env Î â Label â Bij â Env Î â Set
râ âá´±â¨ A , Î² â© râ = râ ââ¨ Î² â©á´± râ
  where open import CG.LowEq A

_âá¶â¨_,_â©_ : â {Ï} â FConf Ï â Label â Bij â FConf Ï â Set
câ âá¶â¨ A , Î² â© câ = câ ââ¨ Î² â©á¶ câ
  where open import CG.LowEq A

_âá´¹â¨_,_â©_ : â {â} â Memory â â Label â Bij â Memory â â Set
Mâ âá´¹â¨ A , Î² â© Mâ = Mâ ââ¨ Î² , _ â? A â©á´¹ Mâ
  where open import CG.LowEq A

_âË¢â¨_,_â©_ : Store â Label â Bij â Store â Set
Î£â âË¢â¨ A , Î² â© Î£â = Î£â ââ¨ Î² â©Ë¢ Î£â
  where open import CG.LowEq A

_âá´´â¨_,_â©_ : Heap â Label â Bij â Heap â Set
Î¼â âá´´â¨ A , Î² â© Î¼â = Î¼â ââ¨ Î² â©á´´ Î¼â
  where open import CG.LowEq A

_âá´¾â¨_,_â©_ : PState â Label â Bij â PState â Set
pâ âá´¾â¨ A , Î² â© pâ = pâ ââ¨ Î² â©á´¾ pâ
  where open import CG.LowEq A

--------------------------------------------------------------------------------
-- Calculus record

open import Generic.Calculus
open import CG.Valid

Î»^CG : Calculus
Î»^CG = record
         { Ty = Ty
         ; Input = Env
         ; IConf = EConf
         ; FConf = FConf
         ; Valid-Inputs = Valid-Inputs
         ; Iâ¨_â© = LIO
         ; _ââ¨_â©_ = _âá¶ â¨_â©_
         ; _âá´±â¨_,_â©_ = _âá´±â¨_,_â©_
         ; _âá´µâ¨_,_â©_ = _âá´µâ¨_,_â©_
         ; _âá¶ â¨_,_â©_ = _âá¶â¨_,_â©_
         }

CG-TINI : TINI Î»^CG
CG-TINI {A = A} isVâ isVâ = tiniá¶  {{isVâ}} {{isVâ}}
  where open import CG.Security A
