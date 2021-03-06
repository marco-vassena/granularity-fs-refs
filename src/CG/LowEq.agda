-- This module defines a L-equivalence relation for all the categoris
-- of the calculus.  L-equivalence relates terms that are
-- indistinguishabile to an attacker at security level L.
--
-- This module is parametric in the security lattice π³ = (π, β) and in
-- the attacker's security A β π.

open import Lattice

module CG.LowEq {{π³ : Lattice}} (A : Label) where

open import CG.Types renaming (_β_ to _βα΅_ ; _β_ to _βα΅_)
open import CG.Syntax
open import Data.Nat renaming (_β_ to _βα΄Ί_)
open import Data.Nat.Properties
open import Data.Empty
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Generic.Bijection
open import Data.Product renaming (_,_ to β¨_,_β©)
open import CG.Valid

mutual

  -- Values
  data _ββ¨_β©β±½_ : β {Ο} β Value Ο β Bij β Value Ο β Set where

    Unit : β {Ξ²} β οΌοΌ ββ¨ Ξ² β©β±½ οΌοΌ

    Lbl : β {Ξ²} β β β β β ββ¨ Ξ² β©β±½ β β β

    Inl : β {Οβ Οβ Ξ²} {vβ vβ : Value Οβ} β
            vβ ββ¨ Ξ² β©β±½ vβ β
            inl {Οβ = Οβ} vβ ββ¨ Ξ² β©β±½ inl vβ

    Inr : β {Οβ Οβ Ξ²} {vβ vβ : Value Οβ} β
            vβ ββ¨ Ξ² β©β±½ vβ β
            inr {Οβ = Οβ} vβ ββ¨ Ξ² β©β±½ inr vβ

    Pair : β {Οβ Οβ Ξ²} {vβ vβ' : Value Οβ} {vβ vβ' : Value Οβ} β
             vβ ββ¨ Ξ² β©β±½ vβ' β
             vβ ββ¨ Ξ² β©β±½ vβ' β
             β¨ vβ , vβ β©  ββ¨ Ξ² β©β±½ β¨ vβ' , vβ' β©

    Fun : β {Ο' Ο Ξ Ξ²} {e : Expr (Ο' β· Ξ) Ο} {ΞΈβ ΞΈβ : Env Ξ} β
                ΞΈβ ββ¨ Ξ² β©α΄± ΞΈβ β
                β¨ e , ΞΈβ β©αΆ ββ¨ Ξ² β©β±½ β¨ e , ΞΈβ β©αΆ

    Thunkβ² : β {Ο Ξ Ξ²} {t : Thunk Ξ (LIO Ο)} {ΞΈβ ΞΈβ : Env Ξ} β
               ΞΈβ ββ¨ Ξ² β©α΄± ΞΈβ β
               β¨ t , ΞΈβ β©α΅ ββ¨ Ξ² β©β±½ β¨ t , ΞΈβ β©α΅

    Labeledα΄Έ : β {β Ο Ξ²} {vβ vβ : Value Ο} β
                 β β A β
                 vβ ββ¨ Ξ² β©β±½ vβ β
                 Labeled β vβ ββ¨ Ξ² β©β±½ Labeled β vβ

    Labeledα΄΄ : β {Ο ββ ββ Ξ²} {vβ vβ : Value Ο} β
                 ββ β€ A β
                 ββ β€ A β
                 Labeled ββ vβ ββ¨ Ξ² β©β±½ Labeled ββ vβ

    Ref-Iα΄Έ : β {β Ο Ξ²} β (ββA : β β A) (n : β) β
             Refα΄΅ {Ο = Ο} β n ββ¨ Ξ² β©β±½ Refα΄΅ β n

    Ref-Iα΄΄ : β {ββ ββ nβ nβ Ο Ξ²} β
             (βββ€A : ββ β€ A) (βββ€A : ββ β€ A) β
             Refα΄΅ {Ο = Ο} ββ nβ ββ¨ Ξ² β©β±½ Refα΄΅ ββ nβ

    Ref-S : β {n m Ο Ξ²} β β¨ n , m β© βα΅ Ξ² β
              RefΛ’ {Ο = Ο} n ββ¨ Ξ² β©β±½ RefΛ’ m

  -- Environment
  data _ββ¨_β©α΄±_  : β {Ξ} β Env Ξ β Bij β Env Ξ β Set where
    [] : β {Ξ²} β [] ββ¨ Ξ² β©α΄± []
    _β·_ : β {Ο Ξ Ξ²} {vβ vβ : Value Ο} {ΞΈβ : Env Ξ} {ΞΈβ : Env Ξ} β
            (vβ ββ¨ Ξ² β©β±½ vβ) β
            (ΞΈβ ββ¨ Ξ² β©α΄± ΞΈβ) β
            (vβ β· ΞΈβ) ββ¨ Ξ² β©α΄± (vβ β· ΞΈβ)

-- Shorthand
Refα΄Έβ² : β {Ο β nβ nβ Ξ²} β β β A β nβ β‘ nβ β Refα΄΅ {Ο = Ο} β nβ ββ¨ Ξ² β©β±½ Refα΄΅ β nβ
Refα΄Έβ² ββA refl = Ref-Iα΄Έ ββA _

--------------------------------------------------------------------------------

-- Heap labeled values
_ββ¨_β©α΄Έ_ : β {Ο} β LValue Ο β Bij β LValue Ο β Set
β¨ vβ , ββ β© ββ¨ Ξ² β©α΄Έ β¨ vβ , ββ β© = Labeled ββ vβ ββ¨ Ξ² β©β±½ Labeled ββ vβ

--------------------------------------------------------------------------------
-- Lemmas on L-equivalent environments.

-- Lookup in L-equivalent envs gives L-equivalent values
lookup-ββ±½ : β {Ο Ξ ΞΈβ ΞΈβ Ξ²} β (ΟβΞ : Ο βα΅ Ξ) β
              ΞΈβ ββ¨ Ξ² β©α΄± ΞΈβ β (ΞΈβ !! ΟβΞ) ββ¨ Ξ² β©β±½ (ΞΈβ !! ΟβΞ)
lookup-ββ±½ here (vββvβ β· ΞΈββΞΈβ) = vββvβ
lookup-ββ±½ (there ΟβΞ) (vββvβ β· ΞΈββΞΈβ) = lookup-ββ±½ ΟβΞ ΞΈββΞΈβ

-- Slicing L-equivalent envs gives gives L-equivalent envs.
slice-βα΄± : β {Ξβ Ξβ Ξ²} {ΞΈβ ΞΈβ : Env Ξβ} β
                 ΞΈβ ββ¨ Ξ² β©α΄± ΞΈβ β
                 (ΞββΞβ : Ξβ βα΅ Ξβ) β
                 slice ΞΈβ ΞββΞβ ββ¨ Ξ² β©α΄± slice ΞΈβ ΞββΞβ
slice-βα΄± [] base = []
slice-βα΄± (vββvβ β· ΞΈββΞΈβ) (cons p) = vββvβ β· slice-βα΄± ΞΈββΞΈβ p
slice-βα΄± (vββvβ β· ΞΈββΞΈβ) (drop p) = slice-βα΄± ΞΈββΞΈβ p

--------------------------------------------------------------------------------

-- Derive low-equivalence for stores and memories.
open import Generic.PState.LowEq {Ty} {Ty} {Value} {LValue} _ββ¨_β©β±½_ _ββ¨_β©α΄Έ_ A public

open Conf

-- Generic relation between configurations
record _ββ¨_β©α΄¬_ {F : Ctx β Ty β Set} {Ξ} {Ο} (cβ : Conf F Ξ Ο ) (Ξ² : Bij) (cβ : Conf F Ξ Ο) : Set where
  constructor β¨_,_,_β©
  field
    pstate-βα΄Ύ : β¨ store cβ , heap cβ β© ββ¨ Ξ² β©α΄Ύ β¨ store cβ , heap cβ β©
    pc-β‘ : pc cβ β‘ pc cβ
    term-β‘ : term cβ β‘ term cβ

  open _ββ¨_β©α΄Ύ_ pstate-βα΄Ύ public

-- Initial Configuration (Expr)
_ββ¨_β©α΄΅_ : β {Ξ Ο} β EConf Ξ Ο β Bij β EConf Ξ Ο β Set
cβ ββ¨ Ξ² β©α΄΅ cβ = cβ ββ¨ Ξ² β©α΄¬ cβ

-- Initial Configuration (Thunk)
_ββ¨_β©α΅_ : β {Ξ Ο} β TConf Ξ Ο β Bij β TConf Ξ Ο β Set
cβ ββ¨ Ξ² β©α΅ cβ = cβ ββ¨ Ξ² β©α΄¬ cβ

-- Final Configuration
data _ββ¨_β©αΆ_ {Ο} : FConf Ο β Bij β FConf Ο β Set where

  pcα΄Έ : β {Ξ£β Ξ£β ΞΌβ ΞΌβ vβ vβ pc Ξ²} β
          (βα΄Ύ : β¨ Ξ£β , ΞΌβ β© ββ¨ Ξ² β©α΄Ύ β¨ Ξ£β , ΞΌβ β©) (pcβA : pc β A) (vβ : vβ ββ¨ Ξ² β©β±½ vβ) β
          β¨ Ξ£β , ΞΌβ , pc , vβ β© ββ¨ Ξ² β©αΆ β¨ Ξ£β , ΞΌβ , pc , vβ β©

  pcα΄΄ : β {Ξ£β Ξ£β ΞΌβ ΞΌβ vβ vβ pcβ pcβ Ξ²} β
          (βα΄Ύ : β¨ Ξ£β , ΞΌβ β© ββ¨ Ξ² β©α΄Ύ β¨ Ξ£β , ΞΌβ β©) (pcββ€A : pcβ β€ A) (pcββ€A : pcβ β€ A) β
          β¨ Ξ£β , ΞΌβ , pcβ , vβ β© ββ¨ Ξ² β©αΆ β¨ Ξ£β , ΞΌβ , pcβ , vβ β©


βα΄Έ-β : β {Ο Ξ²} {vβ vβ : LValue Ο} (pc : Label) β
                   let β¨ vββ² , ββ β© = vβ
                       β¨ vββ² , ββ β© = vβ in
                       vβ ββ¨ Ξ² β©α΄Έ vβ β
                       β¨ vββ² , pc β ββ β© ββ¨ Ξ² β©α΄Έ β¨ vββ² , pc β ββ β©
βα΄Έ-β pc (Labeledα΄Έ {β} x βα΄Έ) with pc β β β? A
... | yes ββ =  Labeledα΄Έ ββ βα΄Έ
... | no β€β =  Labeledα΄΄ β€β β€β
βα΄Έ-β β (Labeledα΄΄ x xβ) = Labeledα΄΄ (join-β€β x) (join-β€β xβ)

label-of-βαΆ : β {Ο Ξ² Ξ£β Ξ£β ΞΌβ ΞΌβ pc} {vβ vβ : LValue Ο} β pc β A β
         let β¨ _ , ββ β© = vβ
             β¨ _ , ββ β© = vβ in
             β¨ Ξ£β , ΞΌβ β© ββ¨ Ξ² β©α΄Ύ β¨ Ξ£β , ΞΌβ β© β
             vβ ββ¨ Ξ² β©α΄Έ vβ β
             β¨ Ξ£β , ΞΌβ , pc β ββ , β ββ β β© ββ¨ Ξ² β©αΆ β¨ Ξ£β , ΞΌβ , pc β ββ , β ββ β β©
label-of-βαΆ pcβA βα΄Ύ (Labeledα΄Έ ββA _) = pcα΄Έ βα΄Ύ (join-β' pcβA ββA) (Lbl _)
label-of-βαΆ pcβA βα΄Ύ (Labeledα΄΄ β€β β€β) = pcα΄΄ βα΄Ύ (join-β€β β€β) (join-β€β β€β)

read-βαΆ : β {Ο Ξ² Ξ£β Ξ£β ΞΌβ ΞΌβ pc} {vβ vβ : LValue Ο} β pc β A β
         let β¨ vββ² , ββ β© = vβ
             β¨ vββ² , ββ β© = vβ in
             β¨ Ξ£β , ΞΌβ β© ββ¨ Ξ² β©α΄Ύ β¨ Ξ£β , ΞΌβ β© β
             vβ ββ¨ Ξ² β©α΄Έ vβ β
             β¨ Ξ£β , ΞΌβ , pc β ββ , vββ² β© ββ¨ Ξ² β©αΆ β¨ Ξ£β , ΞΌβ , pc β ββ , vββ² β©
read-βαΆ pcβA βα΄Ύ (Labeledα΄Έ ββA ββ±½) = pcα΄Έ βα΄Ύ (join-β' pcβA ββA) ββ±½
read-βαΆ pcβA βα΄Ύ (Labeledα΄΄ β€β β€β) = pcα΄΄ βα΄Ύ (join-β€β β€β) (join-β€β β€β)

--------------------------------------------------------------------------------
-- Properties: L-equivalence for values and environment is an
-- equivalence relation, where reflexivity is defined over the domain
-- of terms.  Notice that this is not the case for heaps because the
-- domain and the range of the bijection must be included in the
-- address space of the heap itself, therefore reflexivity holds only
-- for valid heaps free of dangling references.

private module V = IProps Ty Value
private module L = IProps Ty LValue
private module E = IProps Ctx Env

mutual

  wken-ββ±½ : V.Wkenα΄? _ββ¨_β©β±½_
  wken-ββ±½ ββ Unit = Unit
  wken-ββ±½ ββ (Lbl β) = Lbl β
  wken-ββ±½ ββ (Inl ββ±½) = Inl (wken-ββ±½ ββ ββ±½)
  wken-ββ±½ ββ (Inr ββ±½) = Inr (wken-ββ±½ ββ ββ±½)
  wken-ββ±½ ββ (Pair ββ±½ ββ±½β) = Pair (wken-ββ±½ ββ ββ±½) (wken-ββ±½ ββ ββ±½β)
  wken-ββ±½ ββ (Fun βα΄±) = Fun (wken-βα΄± ββ βα΄±)
  wken-ββ±½ ββ (Thunkβ² βα΄±) = Thunkβ² (wken-βα΄± ββ βα΄±)
  wken-ββ±½ ββ (Labeledα΄Έ x ββ±½) = Labeledα΄Έ x (wken-ββ±½ ββ ββ±½)
  wken-ββ±½ ββ (Labeledα΄΄ x xβ) = Labeledα΄΄ x xβ
  wken-ββ±½ ββ (Ref-Iα΄Έ ββA n) = Ref-Iα΄Έ ββA n
  wken-ββ±½ ββ (Ref-Iα΄΄ βββ€A βββ€A) = Ref-Iα΄΄ βββ€A βββ€A
  wken-ββ±½ ββ (Ref-S βα΄?) = Ref-S (bij-β ββ βα΄?)

  wken-βα΄± : E.Wkenα΄? _ββ¨_β©α΄±_
  wken-βα΄± ββ [] = []
  wken-βα΄± ββ (ββ±½ β· βα΄±) = wken-ββ±½ ββ ββ±½ β· wken-βα΄± ββ βα΄±

mutual

  -- Reflexive
  refl-ββ±½ : V.Reflexiveα΄? _ββ¨_β©β±½_ β₯_β₯β±½
  refl-ββ±½ {x = οΌοΌ} = Unit
  refl-ββ±½ {x = β¨ e , ΞΈ β©αΆ} = Fun refl-βα΄±
  refl-ββ±½ {x = β¨ t , ΞΈ β©α΅} = Thunkβ² refl-βα΄±
  refl-ββ±½ {x = inl v} = Inl refl-ββ±½
  refl-ββ±½ {x = inr v} = Inr refl-ββ±½
  refl-ββ±½ {x = β¨ vβ , vβ β©} = Pair ββ ββ
    where ββ = wken-ββ±½ (ΞΉ-β (mβ€mβn β₯ vβ β₯β±½ β₯ vβ β₯β±½)) refl-ββ±½
          ββ = wken-ββ±½ (ΞΉ-β (nβ€mβn β₯ vβ β₯β±½ β₯ vβ β₯β±½)) refl-ββ±½
  refl-ββ±½ {x = Labeled β v} with β β? A
  ... | yes p = Labeledα΄Έ p refl-ββ±½
  ... | no Β¬p = Labeledα΄΄ Β¬p Β¬p
  refl-ββ±½ {x = Refα΄΅ β n} with β β? A
  ... | yes p = Ref-Iα΄Έ p n
  ... | no Β¬p = Ref-Iα΄΄ Β¬p Β¬p
  refl-ββ±½ {x = β β β} = Lbl β
  refl-ββ±½ {x = RefΛ’ x} = Ref-S (ΞΉ-β (sβ€s β€-refl))

  refl-βα΄± : E.Reflexiveα΄? _ββ¨_β©α΄±_ β₯_β₯α΄±
  refl-βα΄± {x = []} = []
  refl-βα΄± {x = v β· ΞΈ} = ββ β· ββ
    where ββ = wken-ββ±½ (ΞΉ-β (mβ€mβn β₯ v β₯β±½ β₯ ΞΈ β₯α΄±)) refl-ββ±½
          ββ = wken-βα΄± (ΞΉ-β (nβ€mβn β₯ v β₯β±½ β₯ ΞΈ β₯α΄±)) refl-βα΄±

  -- Symmetric
  sym-ββ±½ : V.Symmetricα΄? _ββ¨_β©β±½_
  sym-ββ±½ Unit = Unit
  sym-ββ±½ (Lbl β) = Lbl β
  sym-ββ±½ (Inl vββvβ) = Inl (sym-ββ±½ vββvβ)
  sym-ββ±½ (Inr vββvβ) = Inr (sym-ββ±½ vββvβ)
  sym-ββ±½ (Pair vββvβ vββvβ') = Pair (sym-ββ±½ vββvβ) (sym-ββ±½ vββvβ')
  sym-ββ±½ (Fun ΞΈββΞΈβ) = Fun (sym-βα΄± ΞΈββΞΈβ)
  sym-ββ±½ (Thunkβ² ΞΈββΞΈβ) = Thunkβ² (sym-βα΄± ΞΈββΞΈβ)
  sym-ββ±½ (Labeledα΄Έ x vββvβ) = Labeledα΄Έ x (sym-ββ±½ vββvβ)
  sym-ββ±½ (Labeledα΄΄ x xβ) = Labeledα΄΄ xβ x
  sym-ββ±½ (Ref-Iα΄Έ ββA n) = Ref-Iα΄Έ ββA n
  sym-ββ±½ (Ref-Iα΄΄ βββ€A βββ€A) = Ref-Iα΄΄ βββ€A βββ€A
  sym-ββ±½ (Ref-S {Ξ² = Ξ²} x) = Ref-S (Bijectionα΄Ύ.right-inverse-of Ξ² x)

  sym-βα΄± :  E.Symmetricα΄? _ββ¨_β©α΄±_
  sym-βα΄± [] = []
  sym-βα΄± (vββvβ β· ΞΈββΞΈβ) = sym-ββ±½ vββvβ β· sym-βα΄± ΞΈββΞΈβ

  -- Transitive
  trans-ββ±½ : V.Transitiveα΄? _ββ¨_β©β±½_
  trans-ββ±½ Unit Unit = Unit
  trans-ββ±½ (Lbl β) (Lbl .β) = Lbl β
  trans-ββ±½ (Inl vββvβ) (Inl vββvβ) = Inl (trans-ββ±½ vββvβ vββvβ)
  trans-ββ±½ (Inr vββvβ) (Inr vββvβ) = Inr (trans-ββ±½ vββvβ vββvβ)
  trans-ββ±½ (Pair vββvβ vββvβ) (Pair vββvβ vββvβ) = Pair (trans-ββ±½ vββvβ vββvβ) (trans-ββ±½ vββvβ vββvβ)
  trans-ββ±½ (Fun ΞΈββΞΈβ) (Fun ΞΈββΞΈβ) = Fun (trans-βα΄± ΞΈββΞΈβ ΞΈββΞΈβ)
  trans-ββ±½ (Thunkβ² ΞΈββΞΈβ) (Thunkβ² ΞΈββΞΈβ) = Thunkβ² (trans-βα΄± ΞΈββΞΈβ ΞΈββΞΈβ)
  trans-ββ±½ (Labeledα΄Έ x vββvβ) (Labeledα΄Έ xβ vββvβ) = Labeledα΄Έ x (trans-ββ±½ vββvβ vββvβ)
  trans-ββ±½ (Labeledα΄Έ x vββvβ) (Labeledα΄΄ xβ xβ) = β₯-elim (xβ x)
  trans-ββ±½ (Labeledα΄΄ x xβ) (Labeledα΄Έ xβ vββvβ) = β₯-elim (xβ xβ)
  trans-ββ±½ (Labeledα΄΄ x xβ) (Labeledα΄΄ xβ xβ) = Labeledα΄΄ x xβ
  trans-ββ±½ (Ref-Iα΄Έ ββA n) (Ref-Iα΄Έ ββAβ .n) = Ref-Iα΄Έ ββAβ n
  trans-ββ±½ (Ref-Iα΄Έ ββA n) (Ref-Iα΄΄ βββ€A βββ€A) = β₯-elim (βββ€A ββA)
  trans-ββ±½ (Ref-Iα΄΄ βββ€A βββ€A) (Ref-Iα΄Έ ββA n) = β₯-elim (βββ€A ββA)
  trans-ββ±½ (Ref-Iα΄΄ βββ€A βββ€A) (Ref-Iα΄΄ βββ€Aβ βββ€Aβ) = Ref-Iα΄΄ βββ€A βββ€Aβ
  trans-ββ±½ (Ref-S {Ξ² = Ξ²β} x) (Ref-S {Ξ² = Ξ²β} y) = Ref-S (join-βα΅ {Ξ²β = Ξ²β} {Ξ²β} x y)

  trans-βα΄± : E.Transitiveα΄? _ββ¨_β©α΄±_
  trans-βα΄± [] [] = []
  trans-βα΄± (vββvβ β· ΞΈββΞΈβ) (vββvβ β· ΞΈββΞΈβ) = trans-ββ±½ vββvβ vββvβ β· trans-βα΄± ΞΈββΞΈβ ΞΈββΞΈβ

isEquivβ±½ : V.IsEquivalenceα΄? _ββ¨_β©β±½_ β₯_β₯β±½
isEquivβ±½ = record
           { reflα΄? = refl-ββ±½
           ; wkenα΄? = wken-ββ±½
           ; symα΄? = sym-ββ±½
           ; transα΄? = trans-ββ±½ }

isEquivα΄± : E.IsEquivalenceα΄? _ββ¨_β©α΄±_  β₯_β₯α΄±
isEquivα΄± = record
           { reflα΄? = refl-βα΄±
           ; wkenα΄? = wken-βα΄±
           ; symα΄? = sym-βα΄±
           ; transα΄? = trans-βα΄± }

isEquivα΄Έ : L.IsEquivalenceα΄? _ββ¨_β©α΄Έ_  β₯_β₯α΄Έ
isEquivα΄Έ = record
         { reflα΄? = refl-ββ±½
         ; wkenα΄? = wken-ββ±½
         ; symα΄? = sym-ββ±½
         ; transα΄? = trans-ββ±½ }

open import Generic.ValidEquivalence Ty

π½ : IsValidEquivalence Value _ββ¨_β©β±½_
π½ = record { β₯_β₯ = β₯_β₯β±½ ; isValid = isValidβ±½ ; isEquiv = isEquivβ±½ }

π³β² : IsValidEquivalence LValue _ββ¨_β©α΄Έ_
π³β² = record { β₯_β₯ = β₯_β₯α΄Έ ; isValid = isValidα΄Έ ; isEquiv = isEquivα΄Έ }

open βα΄Ύ-Props π½ π³β² public
