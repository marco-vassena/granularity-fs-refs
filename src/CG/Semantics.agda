-- Big-step semantics.

open import Lattice

module CG.Semantics {{π³ : Lattice}} where

open import CG.Types
open import CG.Syntax
open import Relation.Binary.PropositionalEquality
open import Data.Product hiding (_Γ_) renaming (_,_ to _^_)

mutual

  -- Pure big-step semantics of the core of CG
  --
  -- This definition expects a suitable mapping environment (ΞΈ : Env
  -- Ξ) that binds all the free variables in the expression (Expr Ξ Ο)
  -- and ensures type preservation by construction (same type Ο in
  -- Expr and Value).
  data PStep {Ξ} (ΞΈ : Env Ξ) : β {Ο} β Expr Ξ Ο β Value Ο β Set where

    Unit : PStep ΞΈ οΌοΌ οΌοΌ

    Lbl : (β : Label) β PStep ΞΈ  β β β  β β β

    Testβ : β {eβ eβ ββ ββ} β
              eβ βα΄Ύβ¨ ΞΈ β© β ββ β β
              eβ βα΄Ύβ¨ ΞΈ β© β ββ β β
              ββ β ββ β
              PStep ΞΈ (eβ β-? eβ) true

    Testβ : β {eβ eβ ββ ββ} β
              eβ βα΄Ύβ¨ ΞΈ β© β ββ β β
              eβ βα΄Ύβ¨ ΞΈ β© β ββ β β
              ββ β€ ββ β
              PStep ΞΈ (eβ β-? eβ) false

    Wken : β {Ο Ξ'} {e : Expr Ξ' Ο} {v : Value Ο} β
           (p : Ξ' β Ξ) β
           e βα΄Ύβ¨ slice ΞΈ p β© v β
           PStep ΞΈ (wken e p) v

    Var : β {Ο} (ΟβΞ : Ο β Ξ) β PStep ΞΈ (var ΟβΞ) (ΞΈ !! ΟβΞ)

    SThunk : β {Ο} {t : Thunk Ξ (LIO Ο)} β PStep ΞΈ β t βα΅ β¨ t , ΞΈ β©α΅

    Fun : β {Οβ Οβ} {e : Expr (Οβ β· Ξ) Οβ} β PStep ΞΈ (Ξ e) β¨ e , ΞΈ β©αΆ

    App : β {Οβ Οβ Ξ'} {ΞΈ' : Env Ξ'} {eβ : Expr Ξ (Οβ β Οβ)} {eβ : Expr Ξ Οβ}
            {e : Expr (Οβ β· Ξ') Οβ} {vβ : Value Οβ} {v : Value Οβ} β
            eβ βα΄Ύβ¨ ΞΈ β© β¨ e , ΞΈ' β©αΆ
          β eβ βα΄Ύβ¨ ΞΈ β© vβ
          β e βα΄Ύβ¨ vβ β· ΞΈ' β© v
          β PStep ΞΈ (eβ β eβ) v

    Inl : β {Οβ Οβ} {e : Expr Ξ Οβ} {v : Value Οβ} β
            e βα΄Ύβ¨ ΞΈ β© v β
            PStep ΞΈ (inl {Οβ = Οβ} e) (inl v)

    Inr : β {Οβ Οβ} {e : Expr Ξ Οβ} {v : Value Οβ} β
          e βα΄Ύβ¨ ΞΈ β© v β
          PStep ΞΈ (inr {Οβ = Οβ} e) (inr v)

    Caseβ : β {Ο Οβ Οβ} {e : Expr Ξ (Οβ + Οβ)} {eβ : Expr _ Ο} {eβ : Expr _ Ο}
              {v : Value Ο} {vβ : Value Οβ} β
            e βα΄Ύβ¨ ΞΈ β© (inl vβ) β
            eβ βα΄Ύβ¨ vβ β· ΞΈ β© v β
            PStep ΞΈ (case e eβ eβ) v

    Caseβ : β {Ο Οβ Οβ} {e : Expr Ξ (Οβ + Οβ)} {eβ : Expr _ Ο} {eβ : Expr _ Ο}
              {v : Value Ο} {vβ : Value Οβ} β
            e βα΄Ύβ¨ ΞΈ β© (inr vβ) β
            eβ βα΄Ύβ¨ vβ β· ΞΈ β© v  β
            PStep ΞΈ (case e eβ eβ) v

    Pair : β {Οβ Οβ} {eβ : Expr Ξ Οβ} {eβ : Expr Ξ Οβ} {vβ : Value Οβ} {vβ : Value Οβ} β
           eβ βα΄Ύβ¨ ΞΈ β© vβ β
           eβ βα΄Ύβ¨ ΞΈ β© vβ β
           PStep ΞΈ β¨ eβ , eβ β© β¨ vβ , vβ β©

    Fst : β {Οβ Οβ} {e : Expr _ (Οβ Γ Οβ)} {vβ : Value Οβ} {vβ : Value Οβ} β
            e βα΄Ύβ¨ ΞΈ β© β¨ vβ , vβ β© β PStep ΞΈ (fst e) vβ

    Snd : β {Οβ Οβ} {e : Expr _ (Οβ Γ Οβ)} {vβ : Value Οβ} {vβ : Value Οβ} β
            e βα΄Ύβ¨ ΞΈ β© β¨ vβ , vβ β© β PStep ΞΈ (snd e) vβ

  -- Pretty Syntax
  _βα΄Ύβ¨_β©_ : β {Ο Ξ} β Expr Ξ Ο β Env Ξ β Value Ο β Set
  e βα΄Ύβ¨ ΞΈ β© v = PStep ΞΈ e v

  infixr 3 _βα΄Ύβ¨_β©_

mutual

  -- Thunk semantics for LIO computations.
  data Step {Ξ} (ΞΈ : Env Ξ) : β {Ο} β TConf Ξ (LIO Ο) β FConf Ο β Set where

    Return : β {Ξ£ ΞΌ pc Ο} {e : Expr _ Ο} {v : Value Ο} β
               e βα΄Ύβ¨ ΞΈ β© v β
               Step ΞΈ β¨ Ξ£ , ΞΌ , pc , return e β© β¨ Ξ£ , ΞΌ , pc , v β©

    Bind : β {Ξ£ Ξ£' Ξ£'' ΞΌ ΞΌ' ΞΌ'' pc pc' pc'' Οβ Οβ v vβ} {eβ : Expr Ξ (LIO Οβ)} {eβ : Expr (Οβ β· Ξ) (LIO Οβ)}
           β β¨ Ξ£ , ΞΌ , pc , eβ β© βαΆ β¨ ΞΈ β© β¨ Ξ£' , ΞΌ' , pc' , vβ β©
           β β¨ Ξ£' , ΞΌ' , pc' , eβ β© βαΆ β¨ vβ β· ΞΈ β©  β¨ Ξ£'' , ΞΌ'' , pc'' , v β©
           β Step ΞΈ β¨ Ξ£ , ΞΌ , pc , bind eβ eβ β© β¨ Ξ£'' , ΞΌ'' , pc'' , v β©

    Unlabel : β {Ξ£ ΞΌ pc β β' Ο} {e : Expr _ (Labeled Ο)} {v : Value Ο} β
              e βα΄Ύβ¨ ΞΈ β© Labeled β v β
              (eq : β' β‘ pc β β) β
              Step ΞΈ β¨ Ξ£ , ΞΌ , pc , (unlabel e) β© β¨ Ξ£ , ΞΌ , β' , v β©

    ToLabeled : β {Ξ£ Ξ£' ΞΌ ΞΌ' pc pc' Ο v } {e : Expr _ (LIO Ο)}
                β β¨ Ξ£ , ΞΌ , pc , e β© βαΆ β¨ ΞΈ β© β¨ Ξ£' , ΞΌ' , pc' , v β©
                β Step ΞΈ β¨ Ξ£ , ΞΌ , pc , toLabeled e β©  β¨ Ξ£' , ΞΌ' , pc , Labeled pc' v β©

    LabelOf : β {Ξ£ ΞΌ pc β β' Ο} {e : Expr _ (Labeled Ο)} {v : Value Ο} β
                e βα΄Ύβ¨ ΞΈ β© Labeled β v β
                β' β‘ pc β β β
                Step ΞΈ β¨ Ξ£ , ΞΌ , pc , labelOf e β© β¨ Ξ£ , ΞΌ , β' , β β β β©

    GetLabel : β {Ξ£ ΞΌ pc} β Step ΞΈ β¨ Ξ£ , ΞΌ , pc , getLabel β© β¨ Ξ£ , ΞΌ , pc , β pc β β©

    Taint : β {Ξ£ ΞΌ pc pc' β} {e : Expr _ π} β
              e βα΄Ύβ¨ ΞΈ β© β β β β
              pc' β‘ pc β β β
              Step ΞΈ β¨ Ξ£ , ΞΌ , pc , (taint e) β© β¨ Ξ£ , ΞΌ , pc'  , οΌοΌ β©

  --------------------------------------------------------------------------------
  -- Flow Insensitive references

    New : β {Ξ£ ΞΌ pc β Ο} {e : Expr Ξ _} {v : Value Ο} β
          e βα΄Ύβ¨ ΞΈ β© (Labeled β v) β
          pc β β β
          let M = Ξ£ β in
          Step ΞΈ β¨ Ξ£ , ΞΌ , pc , new e β©  β¨ Ξ£ [ β β¦ snocα΄Ή M v ]Λ’ , ΞΌ , pc , Refα΄΅ β β₯ M β₯α΄Ή β©

    Read : β {Ξ£ ΞΌ pc β pc' n Ο} {e : Expr _ (Ref I Ο)} {v : Value Ο } β
           e βα΄Ύβ¨ ΞΈ β© Refα΄΅ β n β
           (nβM : n β¦ v βα΄Ή (Ξ£ β)) β
           (eq : pc' β‘ pc β β) β
           Step ΞΈ β¨ Ξ£ , ΞΌ , pc , ! e β©  β¨ Ξ£ , ΞΌ , pc' , v β©

    Write : β {Ξ£ ΞΌ pc β β' n Ο} {M' : Memory β} {eβ : Expr _ (Ref I Ο)} {eβ : Expr _ (Labeled Ο)} {vβ : Value Ο} β
             eβ βα΄Ύβ¨ ΞΈ β© Refα΄΅ β n β
             eβ βα΄Ύβ¨ ΞΈ β© Labeled β' vβ β
             pc β β β
             β' β β β
             (up : M' β (Ξ£ β) [ n β¦ vβ ]α΄Ή) β
             Step ΞΈ β¨ Ξ£ , ΞΌ , pc , eβ β eβ β© β¨ Ξ£ [ β β¦ M' ]Λ’ , ΞΌ , pc , οΌοΌ β©

    -- LabelOfRef does not raise the program counter because the
    -- reference is flow-insensitive (the label on the ref does not
    -- change).
    LabelOfRef : β {Ξ£ ΞΌ β pc pc' n Ο} {e : Expr _ (Ref I Ο)} β
                 e βα΄Ύβ¨ ΞΈ β© Refα΄΅ β n β
                 (eq : pc' β‘ pc β β) β
                 Step ΞΈ β¨ Ξ£ , ΞΌ , pc , labelOfRef e β© β¨ Ξ£ , ΞΌ , pc' , β β β β©

  --------------------------------------------------------------------------------
  -- Flow Sensitive references

    New-FS : β {Ξ£ ΞΌ pc β Ο} {e : Expr Ξ _} {v : Value Ο} β
             e βα΄Ύβ¨ ΞΈ β© (Labeled β v) β
             pc β β β
             Step ΞΈ β¨ Ξ£ , ΞΌ , pc , new e β©  β¨ Ξ£ , snocα΄΄ ΞΌ (v ^ β) , pc , RefΛ’ β₯ ΞΌ β₯α΄΄ β©

    Read-FS : β {Ξ£ ΞΌ pc β pc' n Ο} {e : Expr _ (Ref S Ο)} {v : Value Ο} β
              e βα΄Ύβ¨ ΞΈ β© RefΛ’ n β
              (nβΞΌ : n β¦ v ^ β βα΄΄ ΞΌ) β
              (eq : pc' β‘ pc β β) β
              Step ΞΈ β¨ Ξ£ , ΞΌ , pc , ! e β©  β¨ Ξ£ , ΞΌ , pc' , v β©

    Write-FS : β {Ξ£ ΞΌ ΞΌ' pc β β' β'' n Ο} {eβ : Expr _ (Ref S Ο)}
                 {eβ : Expr _ (Labeled Ο)} {vβ vβ' : Value Ο} β
             eβ βα΄Ύβ¨ ΞΈ β© RefΛ’ n β
             eβ βα΄Ύβ¨ ΞΈ β© Labeled β' vβ β
             (nβΞΌ : n β¦ vβ' ^ β βα΄΄ ΞΌ) β
             pc β β β
             (β'' β‘ pc β β') β
             (up : ΞΌ' β ΞΌ [ n β¦ vβ ^ β'' ]α΄΄) β
             Step ΞΈ β¨ Ξ£ , ΞΌ , pc , eβ β eβ β© β¨ Ξ£ , ΞΌ' , pc , οΌοΌ β©

    LabelOfRef-FS : β {Ξ£ ΞΌ β pc pc' n Ο} {e : Expr _ (Ref S Ο)} {v : Value Ο} β
                    e βα΄Ύβ¨ ΞΈ β© RefΛ’ n β
                    (nβΞΌ : n β¦ v ^ β βα΄΄ ΞΌ) β
                    (eq : pc' β‘ pc β β) β
                    Step ΞΈ β¨ Ξ£ , ΞΌ , pc , labelOfRef e β© β¨ Ξ£ , ΞΌ , pc' , β β β β©


  -- Pretty syntax.
  _ββ¨_β©_ : β {Ξ Ο} β TConf Ξ (LIO Ο) β Env Ξ β FConf Ο β Set
  cβ ββ¨ ΞΈ β© cβ = Step ΞΈ cβ cβ


  -- Forcing semantics for monadic expressions.
  data FStep {Ξ} (ΞΈ : Env Ξ) : β {Ο} β EConf Ξ (LIO Ο) β FConf Ο β Set where
    Force : β {Ο Ξ' pc pc' Ξ£ Ξ£' ΞΌ ΞΌ' v e} {t : Thunk Ξ' (LIO Ο)} {ΞΈ' : Env Ξ'}
            β e βα΄Ύβ¨ ΞΈ β© β¨ t , ΞΈ' β©α΅
            β β¨ Ξ£ , ΞΌ , pc , t β© ββ¨ ΞΈ' β© β¨ Ξ£' , ΞΌ' , pc' , v β©
            β FStep ΞΈ β¨ Ξ£ , ΞΌ , pc , e β© β¨ Ξ£' , ΞΌ' , pc' , v β©

  _βαΆ β¨_β©_ : β {Ξ Ο} β EConf Ξ (LIO Ο) β Env Ξ β FConf Ο β Set
  cβ βαΆ β¨ ΞΈ β© cβ = FStep ΞΈ cβ cβ

--------------------------------------------------------------------------------
-- The semantics only raises the program counter.

open Conf

mutual

  step-β : β {Ο Ξ cβ} {ΞΈ : Env Ξ} {cβ : TConf Ξ (LIO Ο)} β
             cβ ββ¨ ΞΈ β© cβ β
             (pc cβ) β (pc cβ)
  step-β (Return x) = refl-β
  step-β (Bind x xβ) = trans-β (stepαΆ -β x) (stepαΆ -β xβ)
  step-β (Unlabel x eq) rewrite eq = join-ββ _ _
  step-β (ToLabeled x) = refl-β
  step-β (LabelOf x eq) rewrite eq = join-ββ _ _
  step-β GetLabel = refl-β
  step-β (Taint xβ refl) = join-ββ _ _
  step-β (New a b) = refl-β
  step-β (Read x u refl) = join-ββ _ _
  step-β (Write x _ xβ _ _) = refl-β
  step-β (LabelOfRef x refl) = join-ββ _ _
  step-β (New-FS x xβ) = refl-β
  step-β (Read-FS x nβΞΌ refl) = join-ββ _ _
  step-β (Write-FS x xβ nβΞΌ xβ eq up) = refl-β
  step-β (LabelOfRef-FS x nβΞΌ refl) = join-ββ _ _

  stepαΆ -β : β {Ο Ξ cβ} {ΞΈ : Env Ξ} {cβ : EConf Ξ (LIO Ο)} β
              cβ βαΆ β¨ ΞΈ β© cβ β
              (pc cβ) β (pc cβ)

  stepαΆ -β (Force x xβ) = step-β xβ
