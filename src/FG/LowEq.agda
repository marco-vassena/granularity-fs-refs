-- This module defines a L-equivalence relation for all the categoris
-- of the calculus.  L-equivalence relates terms that are
-- indistinguishabile to an attacker at security level L.
--
-- This module is parametric in the security lattice ð³ = (ð, â) and in
-- the attacker's security A â ð.

-- {-# OPTIONS --allow-unsolved-metas #-}

open import Lattice

module FG.LowEq {{ð³ : Lattice}} (A : Label) where

open import FG.Types renaming (_â_ to _âáµ_ ; _â_ to _âáµ_)
open import FG.Syntax
open import Data.Empty
open import Data.Nat using (â ; _â¤_ ; _<_ ; sâ¤s ; zâ¤n) renaming (_â_ to _âá´º_)
open import Data.Nat.Properties
open import Data.Fin hiding (_â¤_ ; _<_)
open import Function as F
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Generic.Bijection renaming (_â_ to _âá´®_)
open import Data.Product as P renaming (_,_ to â¨_,_â©)
open import FG.Valid

mutual

  -- Labeled values
  data _ââ¨_â©â±½_ {Ï} : Value Ï â Bij â Value Ï â Set where
    Valueá´¸ : â {râ râ â Î²} â (ââA : â â A) (râ : râ ââ¨ Î² â©á´¿ râ) â (râ ^ â) ââ¨ Î² â©â±½ (râ ^ â)
    Valueá´´ : â {râ râ ââ ââ Î²} â (âââ¤A : ââ â¤ A) (âââ¤A : ââ â¤ A) â (râ ^ ââ) ââ¨ Î² â©â±½ (râ ^ ââ)

  -- Raw values
  data _ââ¨_â©á´¿_ : â {Ï} â Raw Ï â Bij â Raw Ï â Set where

    Unit : â {Î²} â ï¼ï¼ ââ¨ Î² â©á´¿ ï¼ï¼

    Lbl : â {Î²} â â â â â ââ¨ Î² â©á´¿ â â â

    Inl : â {Î²} {Ïâ Ïâ} {vâ vâ : Value Ïâ} â
          vâ ââ¨ Î² â©â±½ vâ â
          inl {Ïâ = Ïâ} vâ ââ¨ Î² â©á´¿ inl vâ

    Inr : â {Î²} {Ïâ Ïâ} {vâ vâ : Value Ïâ} â
            vâ ââ¨ Î² â©â±½ vâ â
            inr {Ïâ = Ïâ} vâ ââ¨ Î² â©á´¿ inr vâ

    Pair : â {Î²} {Ïâ Ïâ} {vâ vâ' : Value Ïâ} {vâ vâ' : Value Ïâ} â
             vâ ââ¨ Î² â©â±½ vâ' â
             vâ ââ¨ Î² â©â±½ vâ' â
             â¨ vâ , vâ â©  ââ¨ Î² â©á´¿ â¨ vâ' , vâ' â©

    Fun : â {Î²} {Ï' Ï Î} {e : Expr (Ï' â· Î) Ï}
            {Î¸â : Env Î} {Î¸â : Env Î} â
            Î¸â ââ¨ Î² â©á´± Î¸â â
            â¨ e , Î¸â â©á¶ ââ¨ Î² â©á´¿ â¨ e , Î¸â â©á¶

    -- Flow-insensitive refs
    Ref-Iá´¸ : â {Î²} {â Ï n} â
               (ââA : â â A) â -- â¨ n , m â© âáµ Î² â -- We should not need the bijection anymore
               Refá´µ {Ï = Ï} â n ââ¨ Î² â©á´¿ Refá´µ â n

    Ref-Iá´´ : â {Î²} {ââ ââ nâ nâ Ï} â
               (âââ¤A : ââ â¤ A) (âââ¤A : ââ â¤ A) â
               Refá´µ {Ï = Ï} ââ nâ ââ¨ Î² â©á´¿ Refá´µ ââ nâ

    -- Flow-sensitive refs
    Ref-S : â {Ï n m Î²} â â¨ n , m â© âáµ Î² â
              RefË¢ {Ï = Ï} n ââ¨ Î² â©á´¿ RefË¢ m

    Id : â {Î²} {Ï} {vâ vâ : Value Ï} â
           vâ ââ¨ Î² â©â±½ vâ â
           Id vâ ââ¨ Î² â©á´¿ Id vâ

  -- Environments.
  data _ââ¨_â©á´±_  : â {Î} â Env Î â Bij â Env Î â Set where
    [] : â {Î²} â [] ââ¨ Î² â©á´± []
    _â·_ : â {Ï Î Î²} {vâ vâ : Value Ï} {Î¸â Î¸â : Env Î} â
             (ââ±½ : vâ ââ¨ Î² â©â±½ vâ) â
             (âá´± : Î¸â ââ¨ Î² â©á´± Î¸â) â
             (vâ â· Î¸â) ââ¨ Î² â©á´± (vâ â· Î¸â)

-- Shorthands
Ref-Iá´¸â² : â {Ï â nâ nâ} {Î² : Bij} â â â A â nâ â¡ nâ â Refá´µ {Ï = Ï} â nâ ââ¨ Î² â©á´¿ Refá´µ â nâ
Ref-Iá´¸â² ââA refl = Ref-Iá´¸ ââA

Trueá´¸ : â {â} {Î² : Bij} â â â A â true â ââ¨ Î² â©á´¿ true â
Trueá´¸ ââA = Inl (Valueá´¸ ââA Unit)

Falseá´¸ : â {â} {Î² : Bij} â â â A â false â ââ¨ Î² â©á´¿ false â
Falseá´¸ ââA = Inr (Valueá´¸ ââA Unit)

-- Lemma
ââ±½-â : â {Ï Î²} {vâ vâ : Value Ï} (pc : Label) â
                   let râ ^ ââ = vâ
                       râ ^ ââ = vâ in
                       vâ ââ¨ Î² â©â±½ vâ â (râ ^ (pc â ââ)) ââ¨ Î² â©â±½ (râ ^ (pc â ââ))
ââ±½-â {vâ = râ ^ â} pc (Valueá´¸ x xâ) with (pc â â) â? A
... | yes p = Valueá´¸ p xâ
... | no Â¬p = Valueá´´ Â¬p Â¬p
ââ±½-â pc (Valueá´´ x xâ) = Valueá´´ (trans-â¤ (join-ââ _ _) x) (trans-â¤ (join-ââ _ _) xâ)

--------------------------------------------------------------------------------
-- Lemmas on L-equivalent environments.

-- Lookup in L-equivalent envs gives L-equivalent values
lookup-ââ±½ : â {Ï Î Î¸â Î¸â Î²} â (ÏâÎ : Ï âáµ Î) â
              Î¸â ââ¨ Î² â©á´± Î¸â â (Î¸â !! ÏâÎ) ââ¨ Î² â©â±½ (Î¸â !! ÏâÎ)
lookup-ââ±½ here (vââvâ â· Î¸ââÎ¸â) = vââvâ
lookup-ââ±½ (there ÏâÎ) (vââvâ â· Î¸ââÎ¸â) = lookup-ââ±½ ÏâÎ Î¸ââÎ¸â


-- Slicing L-equivalent envs gives gives L-equivalent envs.
slice-âá´± : â {Îâ Îâ Î²} {Î¸â Î¸â : Env Îâ} â
                 Î¸â ââ¨ Î² â©á´± Î¸â â
                 (ÎââÎâ : Îâ âáµ Îâ) â
                 slice Î¸â ÎââÎâ ââ¨ Î² â©á´± slice Î¸â ÎââÎâ
slice-âá´± [] base = []
slice-âá´± (vââvâ â· Î¸ââÎ¸â) (cons p) = vââvâ â· slice-âá´± Î¸ââÎ¸â p
slice-âá´± (vââvâ â· Î¸ââÎ¸â) (drop p) = slice-âá´± Î¸ââÎ¸â p

--------------------------------------------------------------------------------

-- Subsumed by the above
-- -- Derive L-equivalence for heaps
-- open import Generic.Heap.LowEq {Ty} {Value} _ââ¨_â©â±½_ A public -- TODO: using just that?

-- -- Derive L-equivalence for stores,
-- open import Generic.Store.LowEq {Ty} {Raw} _ââ¨_â©á´¿_ A public -- TODO: using just that?

--------------------------------------------------------------------------------
-- TODO: these should either not be needed anymore or moved to HLowEq (e.g., â_â ; âá¶-â)
-- This seems to be needed in the FG2CG translation.
open import Generic.Value.HLowEq {Ty} {Value} _ââ¨_â©â±½_ public

label-of-ââ±½ : â {Ï Î²} {vâ vâ : Value Ï} â vâ ââ¨ Î² â©â±½ vâ â
                let (râ ^ ââ) = vâ
                    (râ ^ ââ) = vâ in (â ââ â ^ ââ) ââ¨ Î² â©â±½ (â ââ â ^ ââ)
label-of-ââ±½ (Valueá´¸ x xâ) = Valueá´¸ x (Lbl _)
label-of-ââ±½ (Valueá´´ x xâ) = Valueá´´ x xâ

extract-âá´¿ : â {Ï Î²} {vâ vâ : Value Ï} â vâ ââ¨ Î² â©â±½ vâ â
               let râ ^ ââ = vâ
                   râ ^ ââ = vâ in ââ â A â râ ââ¨ Î² â©á´¿ râ
extract-âá´¿ (Valueá´¸ ââA râ) ââ = râ
extract-âá´¿ (Valueá´´ âââ¤A âââ¤A) ââ = â¥-elim (âââ¤A ââ)

-- Lift low-equivalence to configurations
open Conf

-- Derive L-equivalence relation for stores and heaps.
open import Generic.PState.LowEq {Ty} {Ty} {Raw} {Value} _ââ¨_â©á´¿_ _ââ¨_â©â±½_ A public

record _ââ¨_,_â©á´¬_ {V : Set} (câ : Conf V) (R : V  â V â Set) (Î² : Bij) (câ : Conf V) : Set where
  constructor â¨_,_â©
  field
    pstate-âá´¾ : â¨ store câ , heap câ â© ââ¨ Î² â©á´¾ â¨ store câ , heap câ â©
    term-â : R (term câ) (term câ)

  open _ââ¨_â©á´¾_ pstate-âá´¾ public

open _ââ¨_,_â©á´¬_ {{ ... }}

-- L-Equivalence for initial configurations.  For terms we do not use
-- the bijection but simply require syntactic equivalence.
_ââ¨_â©á´µ_ : â {Î Ï} â IConf Î Ï â Bij â IConf Î Ï â Set
câ ââ¨ Î² â©á´µ câ = câ ââ¨ _â¡_ , Î² â©á´¬ câ

-- Final configurations.
_ââ¨_â©á¶_ : â {Ï} â FConf Ï â Bij â FConf Ï â Set
câ ââ¨ Î² â©á¶ câ = câ ââ¨ _ââ¨ Î² â©â±½_ , Î² â©á´¬ câ

--------------------------------------------------------------------------------
-- Properties: L-equivalence for raw, labeled values, and environment is an
-- equivalence relation, where reflexivity is defined over the domain
-- of terms.  Notice that this is not the case for heaps because the
-- domain and the range of the bijection must be included in the
-- address space of the heap itself, therefore reflexivity holds only
-- for valid heaps free of dangling references.

open import Generic.Bijection

private module R = IProps Ty Raw
private module V = IProps Ty Value
private module E = IProps Ctx Env

mutual

  wken-ââ±½ : V.Wkená´® _ââ¨_â©â±½_
  wken-ââ±½ Î²âÎ²' (Valueá´¸ ââA râ) = Valueá´¸ ââA (wken-âá´¿ Î²âÎ²' râ)
  wken-ââ±½ Î²âÎ²' (Valueá´´ âââ¤A âââ¤A) = Valueá´´ âââ¤A âââ¤A

  wken-âá´± : E.Wkená´® _ââ¨_â©á´±_
  wken-âá´± Î²âÎ²' [] = []
  wken-âá´± Î²âÎ²' (ââ±½ â· âá´±) = wken-ââ±½ Î²âÎ²' ââ±½ â· wken-âá´± Î²âÎ²' âá´±

  wken-âá´¿ : R.Wkená´® _ââ¨_â©á´¿_
  wken-âá´¿ Î²âÎ²' Unit = Unit
  wken-âá´¿ Î²âÎ²' (Lbl â) = Lbl â
  wken-âá´¿ Î²âÎ²' (Inl x) = Inl (wken-ââ±½ Î²âÎ²' x)
  wken-âá´¿ Î²âÎ²' (Inr x) = Inr (wken-ââ±½ Î²âÎ²' x)
  wken-âá´¿ Î²âÎ²' (Pair x y) = Pair (wken-ââ±½ Î²âÎ²' x) (wken-ââ±½ Î²âÎ²' y)
  wken-âá´¿ Î²âÎ²' (Fun x) = Fun (wken-âá´± Î²âÎ²' x)
  wken-âá´¿ Î²âÎ²' (Ref-Iá´¸ ââA) = Ref-Iá´¸ ââA
  wken-âá´¿ Î²âÎ²' (Ref-Iá´´ âââ¤A âââ¤A) = Ref-Iá´´ âââ¤A âââ¤A
  wken-âá´¿ Î²âÎ²' (Ref-S âá´®) = Ref-S (bij-â Î²âÎ²' âá´®)
  wken-âá´¿ Î²âÎ²' (Id x) = Id (wken-ââ±½ Î²âÎ²' x)

--------------------------------------------------------------------------------

  -- Reflexive
  refl-ââ±½ : V.Reflexiveá´® _ââ¨_â©â±½_ â¥_â¥â±½
  refl-ââ±½ {x = r ^ â} with â â? A
  refl-ââ±½ {x = r ^ â} | yes ââA = Valueá´¸ ââA refl-âá´¿
  refl-ââ±½ {x = r ^ â} | no ââ¤A = Valueá´´ ââ¤A ââ¤A

  refl-âá´¿ : R.Reflexiveá´® _ââ¨_â©á´¿_ â¥_â¥á´¿
  refl-âá´¿ {x = ï¼ï¼} = Unit
  refl-âá´¿ {x = â¨ _ , Î¸ â©á¶} = Fun refl-âá´±
  refl-âá´¿ {x = (inl v)} = Inl refl-ââ±½
  refl-âá´¿ {x = (inr v)} = Inr refl-ââ±½
  refl-âá´¿ {x = â¨ vâ , vâ â©} = Pair ââ ââ
    where ââ = wken-ââ±½ (Î¹-â (mâ¤mân â¥ vâ â¥â±½ â¥ vâ â¥â±½)) refl-ââ±½
          ââ = wken-ââ±½ (Î¹-â (nâ¤mân â¥ vâ â¥â±½ â¥ vâ â¥â±½)) refl-ââ±½
  refl-âá´¿ {x = (Refá´µ â n)} with â â? A
  ... | yes ââA = Ref-Iá´¸ ââA
  ... | no ââ¤A = Ref-Iá´´ ââ¤A ââ¤A
  refl-âá´¿ {x = (RefË¢ n)} = Ref-S (Î¹-â (sâ¤s â¤-refl))
  refl-âá´¿ {x = â â â} = Lbl â
  refl-âá´¿ {x = (Id v)} = Id refl-ââ±½

  refl-âá´± : E.Reflexiveá´® _ââ¨_â©á´±_ â¥_â¥á´±
  refl-âá´± {x = []} = []
  refl-âá´± {x = (v â· Î¸)} = ââ â· ââ
    where ââ = wken-ââ±½ (Î¹-â (mâ¤mân â¥ v â¥â±½ â¥ Î¸ â¥á´±)) refl-ââ±½
          ââ = wken-âá´± (Î¹-â (nâ¤mân â¥ v â¥â±½ â¥ Î¸ â¥á´±)) refl-âá´±

----------------------------------------------------------------------------------

  -- Symmetric
  sym-ââ±½ : V.Symmetricá´® _ââ¨_â©â±½_
  sym-ââ±½ (Valueá´¸ ââA râ) = Valueá´¸ ââA (sym-âá´¿ râ)
  sym-ââ±½ (Valueá´´ âââ¤A âââ¤A) = Valueá´´ âââ¤A âââ¤A

  sym-âá´¿ : R.Symmetricá´® _ââ¨_â©á´¿_
  sym-âá´¿ Unit = Unit
  sym-âá´¿ (Lbl â) = Lbl â
  sym-âá´¿ (Inl x) = Inl (sym-ââ±½ x)
  sym-âá´¿ (Inr x) = Inr (sym-ââ±½ x)
  sym-âá´¿ (Pair x y) = Pair (sym-ââ±½ x) (sym-ââ±½ y)
  sym-âá´¿ (Fun x) = Fun (sym-âá´± x)
  sym-âá´¿ {Î² = Î²} (Ref-Iá´¸ ââA) = Ref-Iá´¸ ââA
  sym-âá´¿ (Ref-Iá´´ âââ¤A âââ¤A) = Ref-Iá´´ âââ¤A âââ¤A
  sym-âá´¿ {Î² = Î²} (Ref-S x) = Ref-S (Bijectioná´¾.right-inverse-of Î² x)
  sym-âá´¿ (Id x) = Id (sym-ââ±½ x)

  sym-âá´± : E.Symmetricá´® _ââ¨_â©á´±_
  sym-âá´± [] = []
  sym-âá´± (ââ±½ â· âá´±) = sym-ââ±½ ââ±½ â· sym-âá´± âá´±

  -- Transitive
  trans-âá´¿ : R.Transitiveá´® _ââ¨_â©á´¿_
  trans-âá´¿ Unit Unit = Unit
  trans-âá´¿ (Lbl â) (Lbl .â) = Lbl â
  trans-âá´¿ (Inl x) (Inl y) = Inl (trans-ââ±½ x y)
  trans-âá´¿ (Inr x) (Inr y) = Inr (trans-ââ±½ x y)
  trans-âá´¿ (Pair xâ yâ) (Pair xâ yâ) = Pair (trans-ââ±½ xâ xâ) (trans-ââ±½ yâ yâ)
  trans-âá´¿ (Fun x) (Fun y) = Fun (trans-âá´± x y)
  trans-âá´¿ {Î²â = Î²â} {Î²â} (Ref-Iá´¸ ââA) (Ref-Iá´¸ ââAâ)
    = Ref-Iá´¸ ââAâ
  trans-âá´¿ (Ref-Iá´¸ ââA) (Ref-Iá´´ âââ¤A âââ¤A) = â¥-elim (âââ¤A ââA)
  trans-âá´¿ (Ref-Iá´´ âââ¤A âââ¤A) (Ref-Iá´¸ ââA) = â¥-elim (âââ¤A ââA)
  trans-âá´¿ (Ref-Iá´´ âââ¤A âââ¤A) (Ref-Iá´´ âââ¤Aâ âââ¤Aâ) = Ref-Iá´´ âââ¤A âââ¤Aâ
  trans-âá´¿ {Î²â = Î²â} {Î²â} (Ref-S x) (Ref-S y)
    = Ref-S (join-âáµ {Î²â = Î²â} {Î²â} x y)
  trans-âá´¿ (Id x) (Id y) = Id (trans-ââ±½ x y)

  trans-ââ±½ : V.Transitiveá´® _ââ¨_â©â±½_
  trans-ââ±½ (Valueá´¸ ââA râ) (Valueá´¸ ââAâ rââ) = Valueá´¸ ââAâ (trans-âá´¿ râ rââ)
  trans-ââ±½ (Valueá´¸ ââA râ) (Valueá´´ âââ¤A âââ¤A) = â¥-elim (âââ¤A ââA)
  trans-ââ±½ (Valueá´´ âââ¤A âââ¤A) (Valueá´¸ ââA râ) = â¥-elim (âââ¤A ââA)
  trans-ââ±½ (Valueá´´ âââ¤A âââ¤A) (Valueá´´ âââ¤Aâ âââ¤Aâ) = Valueá´´ âââ¤A âââ¤Aâ

  trans-âá´± : E.Transitiveá´® _ââ¨_â©á´±_
  trans-âá´± [] [] = []
  trans-âá´± (ââ±½â â· âá´±â) (ââ±½â â· âá´±â) = trans-ââ±½ ââ±½â ââ±½â â· trans-âá´± âá´±â âá´±â

--------------------------------------------------------------------------------

open import Generic.Bijection

-- Why do we need this?
isEquivâ±½ : V.IsEquivalenceá´® _ââ¨_â©â±½_ â¥_â¥â±½
isEquivâ±½ = record { reflá´® = refl-ââ±½
           ; wkená´® = wken-ââ±½
           ; symá´® = sym-ââ±½
           ; transá´® = trans-ââ±½ }

isEquivá´¿ : R.IsEquivalenceá´® _ââ¨_â©á´¿_ â¥_â¥á´¿
isEquivá´¿ = record { reflá´® = refl-âá´¿
           ; wkená´® = wken-âá´¿
           ; symá´® = sym-âá´¿
           ; transá´® = trans-âá´¿ }

isEquivá´± : E.IsEquivalenceá´® _ââ¨_â©á´±_  â¥_â¥á´±
isEquivá´± = record { reflá´® = refl-âá´±
           ; wkená´® = wken-âá´±
           ; symá´® = sym-âá´±
           ; transá´® = trans-âá´± }

-- Why this?
import Generic.ValidEquivalence as G
open G Ty

ð¹ : IsValidEquivalence Raw _ââ¨_â©á´¿_
ð¹ = record { â¥_â¥ = â¥_â¥á´¿ ; isValid = isValidá´¿ ; isEquiv = isEquivá´¿ }

ð½ : IsValidEquivalence Value _ââ¨_â©â±½_
ð½ = record { â¥_â¥ = â¥_â¥â±½ ; isValid = isValidâ±½ ; isEquiv = isEquivâ±½ }

ð¬ : G.IsValidEquivalence Ctx Env _ââ¨_â©á´±_
ð¬ = record { â¥_â¥ = â¥_â¥á´± ; isValid = isValidá´± ; isEquiv = isEquivá´± }

open âá´¾-Props ð¹ ð½ public
