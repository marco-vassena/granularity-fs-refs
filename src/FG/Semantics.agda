-- Big-step semantics.

open import Lattice

module FG.Semantics {{π³ : Lattice}} where

open import FG.Types
open import FG.Syntax
open import Relation.Binary.PropositionalEquality

mutual

  -- Big-step operational semantics.
  --
  -- This definition expects a suitable mapping environment (ΞΈ : Env
  -- Ξ) that binds all the free variables in the program (IConf Ξ Ο)
  -- and ensures type preservation by construction (same type Ο in
  -- IConf and FConf).
  data Step {Ξ} (ΞΈ : Env Ξ) (pc : Label) : β {Ο} β IConf Ξ Ο β FConf Ο β Set where

    Var : β {Ξ£ ΞΌ Ο β'} (ΟβΞ : Ο β Ξ) β
          let v ^ β = (ΞΈ !! ΟβΞ) in
          β' β‘ (pc β β) β
          Step ΞΈ pc β¨ Ξ£ , ΞΌ , var ΟβΞ β© β¨ Ξ£ , ΞΌ , v ^ β' β©

    Unit : β {Ξ£ ΞΌ} β Step ΞΈ pc β¨ Ξ£ , ΞΌ , οΌοΌ β© β¨ Ξ£ , ΞΌ , οΌοΌ ^ pc β©

    Lbl : β {Ξ£ ΞΌ} (β : Label) β Step ΞΈ pc β¨ Ξ£ , ΞΌ , β β β β© β¨ Ξ£ , ΞΌ , β β β ^ pc β©

    Testβ : β {Ξ£β Ξ£β Ξ£β ΞΌβ ΞΌβ ΞΌβ eβ eβ β ββ ββ' ββ ββ'} β
              β¨ Ξ£β , ΞΌβ , eβ β© ββ¨ ΞΈ , pc β© β¨ Ξ£β , ΞΌβ , β ββ β ^ ββ' β© β
              β¨ Ξ£β , ΞΌβ , eβ β© ββ¨ ΞΈ , pc β© β¨ Ξ£β , ΞΌβ , β ββ β ^ ββ' β© β
              ββ β ββ β
              β β‘ ββ' β ββ' β
              Step ΞΈ pc β¨ Ξ£β , ΞΌβ , eβ β-? eβ β© β¨ Ξ£β , ΞΌβ , true pc ^ β β©

    Testβ : β {Ξ£β Ξ£β Ξ£β ΞΌβ ΞΌβ ΞΌβ eβ eβ β ββ ββ' ββ ββ'} β
              β¨ Ξ£β , ΞΌβ , eβ β© ββ¨ ΞΈ , pc β© β¨ Ξ£β , ΞΌβ , β ββ β ^ ββ' β© β
              β¨ Ξ£β , ΞΌβ , eβ β© ββ¨ ΞΈ , pc β© β¨ Ξ£β , ΞΌβ , β ββ β ^ ββ' β© β
              ββ β€ ββ β
              β β‘ ββ' β ββ' β
              Step ΞΈ pc β¨ Ξ£β , ΞΌβ , eβ β-? eβ β© β¨ Ξ£β , ΞΌβ , false pc ^ β β©

    Fun : β {Ξ£ ΞΌ Οβ Οβ} {e : Expr (Οβ β· Ξ) Οβ}  β Step ΞΈ pc β¨ Ξ£ , ΞΌ , Ξ e β© β¨ Ξ£ , ΞΌ , β¨ e , ΞΈ β©αΆ ^ pc β©

    App : β {Ξ£ Ξ£' Ξ£'' Ξ£''' ΞΌ ΞΌ' ΞΌ'' ΞΌ''' Ξ' ΞΈ' β β' Οβ Οβ}
            {eβ : Expr Ξ (Οβ β Οβ)} {e : Expr (Οβ β· Ξ') Οβ} β
             {eβ : Expr _ Οβ} {vβ : Value Οβ} {v : Value Οβ} β
             β¨ Ξ£ , ΞΌ , eβ β© ββ¨ ΞΈ , pc β© β¨ Ξ£' , ΞΌ' , β¨ e , ΞΈ' β©αΆ ^ β β© β
             β¨ Ξ£' , ΞΌ' , eβ β© ββ¨ ΞΈ , pc β© β¨ Ξ£'' , ΞΌ'' , vβ β© β
             β' β‘ pc β β β
             β¨ Ξ£'' , ΞΌ'' , e β© ββ¨ vβ β· ΞΈ' , β' β© β¨ Ξ£''' , ΞΌ''' , v β© β
             Step ΞΈ pc β¨ Ξ£ , ΞΌ , eβ β eβ β© β¨ Ξ£''' , ΞΌ''' , v β©

    Wken : β {Ξ£ Ξ£' ΞΌ ΞΌ' Ο Ξ'} {e : Expr Ξ' Ο} {v : Value Ο} β
           (p : Ξ' β Ξ) β β¨ Ξ£ , ΞΌ , e β© ββ¨ slice ΞΈ p , pc β© β¨ Ξ£' , ΞΌ' , v β© β
           Step ΞΈ pc β¨ Ξ£ , ΞΌ , wken e p β© β¨ Ξ£' , ΞΌ' , v β©

    Inl : β {Ξ£ Ξ£' ΞΌ ΞΌ' Οβ Οβ} {e : Expr _ Οβ} {v : Value Οβ}  β
            β¨ Ξ£ , ΞΌ , e β© ββ¨ ΞΈ , pc β© β¨ Ξ£' , ΞΌ' , v β© β
            Step ΞΈ pc β¨ Ξ£ , ΞΌ , inl {Οβ = Οβ} e β© β¨ Ξ£' , ΞΌ' , inl v ^ pc β©

    Inr : β {Ξ£ Ξ£' ΞΌ ΞΌ' Οβ Οβ} {e : Expr _ Οβ} {v : Value Οβ}  β
            β¨ Ξ£ , ΞΌ , e β© ββ¨ ΞΈ , pc β© β¨ Ξ£' , ΞΌ' , v β© β
            Step ΞΈ pc β¨ Ξ£ , ΞΌ , inr {Οβ = Οβ} e β© β¨ Ξ£' , ΞΌ' , inr v ^ pc β©

    Caseβ :  β {Ξ£ Ξ£' Ξ£'' ΞΌ ΞΌ' ΞΌ'' β β' Οβ Οβ Ο} {e : Expr _ (Οβ + Οβ)} {eβ : Expr _ Ο}  {eβ : Expr _ Ο}  β
             {vβ : Value Οβ} {v : Value Ο} β
             β¨ Ξ£ , ΞΌ , e β© ββ¨ ΞΈ , pc β© β¨ Ξ£' , ΞΌ' , inl vβ ^ β β© β
             β' β‘ pc β β β
             β¨ Ξ£' , ΞΌ' , eβ β© ββ¨ vβ β· ΞΈ , β' β© β¨ Ξ£'' , ΞΌ'' , v β© β
             Step ΞΈ pc β¨ Ξ£ , ΞΌ , case e eβ eβ β© β¨ Ξ£'' , ΞΌ'' , v β©

    Caseβ :  β {Ξ£ Ξ£' Ξ£'' ΞΌ ΞΌ' ΞΌ'' β β' Οβ Οβ Ο} {e : Expr _ (Οβ + Οβ)} {eβ : Expr _ Ο}  {eβ : Expr _ Ο}  β
             {vβ : Value Οβ} {v : Value Ο} β
             β¨ Ξ£ , ΞΌ , e β© ββ¨ ΞΈ , pc β© β¨ Ξ£' , ΞΌ' , inr vβ ^ β β© β
             β' β‘ pc β β β
             β¨ Ξ£' , ΞΌ' , eβ β© ββ¨ vβ β· ΞΈ , β' β© β¨ Ξ£'' , ΞΌ'' , v β© β
             Step ΞΈ pc β¨ Ξ£ , ΞΌ , case e eβ eβ β© β¨ Ξ£'' , ΞΌ'' , v β©


    Pair : β {Ξ£ Ξ£' Ξ£'' ΞΌ ΞΌ' ΞΌ'' Οβ Οβ} {eβ : Expr _ Οβ} {eβ : Expr _ Οβ} {vβ : Value Οβ} {vβ : Value Οβ} β
             β¨ Ξ£ , ΞΌ , eβ β© ββ¨ ΞΈ , pc β© β¨ Ξ£' , ΞΌ' , vβ β© β
             β¨ Ξ£' , ΞΌ' , eβ β© ββ¨ ΞΈ , pc β© β¨ Ξ£'' , ΞΌ'' , vβ β© β
             Step ΞΈ pc β¨ Ξ£ , ΞΌ , β¨ eβ , eβ β© β© β¨ Ξ£'' , ΞΌ'' , β¨ vβ , vβ β© ^ pc β©

    Fst : β {Ξ£ Ξ£' ΞΌ ΞΌ' Οβ Οβ β β'} {e : Expr _ (Οβ Γ Οβ)} {vβ : Value Οβ} {vβ : Value Οβ} β
             β¨ Ξ£ , ΞΌ , e β© ββ¨ ΞΈ , pc β© β¨ Ξ£' , ΞΌ' , β¨ vβ , vβ β© ^ β β© β
             let r ^ ββ = vβ in
             β' β‘ β β ββ β
            Step ΞΈ pc β¨ Ξ£ , ΞΌ , fst e β© β¨ Ξ£' , ΞΌ' , r ^ β' β©

    Snd : β {Ξ£ Ξ£' ΞΌ ΞΌ' Οβ Οβ β β'} {e : Expr _ (Οβ Γ Οβ)} {vβ : Value Οβ} {vβ : Value Οβ} β
             β¨ Ξ£ , ΞΌ , e β© ββ¨ ΞΈ , pc β© β¨ Ξ£' , ΞΌ' , β¨ vβ , vβ β© ^ β β© β
             let r ^ ββ = vβ in
             β' β‘ β β ββ β
             Step ΞΈ pc β¨ Ξ£ , ΞΌ , snd e β© β¨ Ξ£' , ΞΌ' , r ^ β' β©

    LabelOf : β {Ξ£ Ξ£' ΞΌ ΞΌ' β Ο} {e : Expr _ Ο} {r : Raw Ο} β
                β¨ Ξ£ , ΞΌ , e β© ββ¨ ΞΈ , pc β© β¨ Ξ£' , ΞΌ' , r ^ β β© β
                Step ΞΈ pc β¨ Ξ£ , ΞΌ , labelOf e β© β¨ Ξ£' , ΞΌ' , β β β ^ β β©

    GetLabel : β {Ξ£ ΞΌ} β Step ΞΈ pc β¨ Ξ£ , ΞΌ , getLabel β© β¨ Ξ£ , ΞΌ , (β pc β ^ pc) β©

    Taint : β {Ξ£ Ξ£' Ξ£'' ΞΌ ΞΌ' ΞΌ'' β pc' pc'' eβ Ο} {eβ : Expr Ξ Ο} {v : Value Ο} β
              (eq : pc'' β‘ pc β β) β
              Step ΞΈ pc β¨ Ξ£ , ΞΌ , eβ β© β¨ Ξ£' , ΞΌ' , β β β ^ pc' β© β
              Step ΞΈ pc''  β¨ Ξ£' , ΞΌ' , eβ β© β¨ Ξ£'' , ΞΌ'' , v β© β
              (pc'βpc'' : pc' β pc'') β -- Is this needed?
              Step ΞΈ pc β¨ Ξ£ , ΞΌ , taint eβ eβ β© β¨ Ξ£'' , ΞΌ'' , v β©

    LabelOfRef : β {Ξ£ Ξ£' ΞΌ ΞΌ' β β' β'' n Ο} {e : Expr Ξ (Ref I Ο)} β
                 β¨ Ξ£ , ΞΌ , e β© ββ¨ ΞΈ , pc β© β¨ Ξ£' , ΞΌ' , Refα΄΅ β n ^ β' β© β
                 (eq : β'' β‘ β β β') β
                 Step ΞΈ pc β¨ Ξ£ , ΞΌ , labelOfRef e β© β¨ Ξ£' , ΞΌ' , β β β ^ β'' β©

    New : β {β Ο Ξ£ Ξ£' ΞΌ ΞΌ'} {e : Expr Ξ _} {r : Raw Ο} β
          β¨ Ξ£ , ΞΌ , e β© ββ¨ ΞΈ , pc β© β¨ Ξ£' , ΞΌ' , r ^ β β© β
          let M = Ξ£' β in
          Step ΞΈ pc β¨ Ξ£ , ΞΌ , new {s = I} e β© β¨  Ξ£' [ β β¦ snocα΄Ή M r ]Λ’ , ΞΌ' , (Refα΄΅ β β₯ M β₯α΄Ή) ^ pc β©

    -- This is better than asking β' β β and returning the value at pc
    -- β β. The combination pc β β' (step-β) and β' β β implies pc β
    -- β, thus the rule would not allow to read lower references.
    Read : β {Ξ£ Ξ£' ΞΌ ΞΌ' β β' β'' n Ο} {e : Expr _ (Ref I Ο)} {r : Raw Ο } β
           β¨ Ξ£ , ΞΌ , e β© ββ¨ ΞΈ , pc β© β¨ Ξ£' , ΞΌ' , (Refα΄΅ β n) ^ β' β© β
           n β¦ r βα΄Ή (Ξ£' β) β
           (eq : β'' β‘ (β β β')) β
           Step ΞΈ pc β¨ Ξ£ , ΞΌ , ! e β©  β¨ Ξ£' , ΞΌ' ,  r ^ β'' β©

    Write : β {Ξ£β Ξ£β Ξ£β ΞΌβ ΞΌβ ΞΌβ β ββ ββ n Ο} {M' : Memory β} {eβ : Expr _ (Ref I Ο)}
              {eβ : Expr _ Ο} {rβ : Raw Ο} β
             β¨ Ξ£β , ΞΌβ , eβ β© ββ¨ ΞΈ , pc β© β¨ Ξ£β , ΞΌβ , (Refα΄΅ β n) ^ ββ β© β
             -- TODO: It was l' β pc, wouldn't this imply pc β‘ β' (from pc β β'). Probably a
             -- typo, but check actual paper and formalization online.
             -- The paper is correct, there was a typo in the rule.
              ββ β β β
             β¨ Ξ£β , ΞΌβ , eβ β© ββ¨ ΞΈ , pc β© β¨ Ξ£β , ΞΌβ , rβ ^ ββ β© β
             (ββββ : ββ β β) β
               M' β (Ξ£β β) [ n β¦ rβ ]α΄Ή β
             Step ΞΈ pc β¨ Ξ£β , ΞΌβ , eβ β eβ β© β¨ Ξ£β [ β β¦ M' ]Λ’ , ΞΌβ , οΌοΌ ^ pc β©

    --------------------------------------------------------------------------------
    -- Flow Sensitive (FS) primitives

    -- For FS refs, the semantics of labelOf is similar to regular FI refs.
    -- We have a different rule, because the reference has a different type
    -- and distinct value.
    LabelOfRef-FS : β {Ξ£ Ξ£' ΞΌ ΞΌ' ββ ββ ββ n Ο} {e : Expr Ξ (Ref S Ο)} {r : Raw Ο} β
                  β¨ Ξ£ , ΞΌ , e β© ββ¨ ΞΈ , pc β© β¨ Ξ£' , ΞΌ' , RefΛ’ n ^ ββ β© β
                  n β¦ r ^ ββ βα΄΄ ΞΌ' β
                  (eq : ββ β‘ ββ β ββ) β
                  Step ΞΈ pc β¨ Ξ£ , ΞΌ , labelOfRef e β© β¨ Ξ£' , ΞΌ' , β ββ β ^ ββ β©

    New-FS : β {Ο Ξ£ Ξ£' ΞΌ ΞΌ'} {e : Expr Ξ Ο} {v : Value Ο} β
          β¨ Ξ£ , ΞΌ , e β© ββ¨ ΞΈ , pc β© β¨ Ξ£' , ΞΌ' , v β© β
          Step ΞΈ pc β¨ Ξ£ , ΞΌ , new {s = S} e β©  β¨  Ξ£' , snocα΄΄ ΞΌ' v , RefΛ’ β₯ ΞΌ' β₯α΄΄ ^ pc β©

    -- Tainting the result with β β β' is better than asking β' β β
    -- and returning the value at pc β β. The combination pc β β'
    -- (step-β) and β' β β implies pc β β, thus the rule would not
    -- allow to read lower references.
    Read-FS : β {Ξ£ Ξ£' ΞΌ ΞΌ' β β' β'' n Ο r} {e : Expr _ (Ref S Ο)}  β
           β¨ Ξ£ , ΞΌ , e β© ββ¨ ΞΈ , pc β© β¨ Ξ£' , ΞΌ' , (RefΛ’ n) ^ β β© β
           n β¦ r ^ β' βα΄΄ ΞΌ' β
           (eq : β'' β‘ β β β') β
           Step ΞΈ pc β¨ Ξ£ , ΞΌ , ! e β©  β¨ Ξ£' , ΞΌ' ,  r ^ β'' β©

    Write-FS : β {Ξ£β Ξ£β Ξ£β ΞΌβ ΞΌβ ΞΌβ ΞΌβ' β ββ ββ ββ' n Ο}
               {eβ : Expr _ (Ref S Ο)} {eβ : Expr _ Ο} {rβ rβ : Raw Ο} β
             β¨ Ξ£β , ΞΌβ , eβ β© ββ¨ ΞΈ , pc β© β¨ Ξ£β , ΞΌβ , (RefΛ’ n) ^ β β© β
             β¨ Ξ£β , ΞΌβ , eβ β© ββ¨ ΞΈ , pc β© β¨ Ξ£β , ΞΌβ , rβ ^ ββ β© β
             n β¦ rβ ^ ββ βα΄΄ ΞΌβ β
             β β ββ β
             (eq : ββ' β‘ β β ββ) β
             ΞΌβ' β ΞΌβ [ n β¦ rβ ^ ββ' ]α΄΄ β
             Step ΞΈ pc β¨ Ξ£β , ΞΌβ , eβ β eβ β© β¨ Ξ£β , ΞΌβ' , οΌοΌ ^ pc β©

    Id : β {Ξ£β Ξ£β ΞΌβ ΞΌβ Ο} {e : Expr Ξ Ο} {v : Value Ο} β
            β¨ Ξ£β , ΞΌβ , e β© ββ¨ ΞΈ , pc β© β¨ Ξ£β , ΞΌβ , v β© β
            Step ΞΈ pc β¨ Ξ£β , ΞΌβ , Id e β© β¨ Ξ£β , ΞΌβ , Id v ^ pc β©

    UnId : β {Ξ£β Ξ£β ΞΌβ ΞΌβ Ο v ββ ββ} {e : Expr Ξ (Id Ο)} β
             β¨ Ξ£β , ΞΌβ , e β© ββ¨ ΞΈ , pc β© β¨ Ξ£β , ΞΌβ , Id v ^ ββ β© β
             let r ^ β' = v in
             (eq : ββ β‘ ββ β β') β
             Step ΞΈ pc β¨ Ξ£β , ΞΌβ , unId e β© β¨ Ξ£β , ΞΌβ , r ^ ββ β©

  -- Pretty syntax
  _ββ¨_,_β©_ : β {Ξ Ο} β IConf Ξ Ο β Env Ξ β Label β FConf Ο β Set
  cβ ββ¨ ΞΈ , pc β© cβ = Step ΞΈ pc cβ cβ

--------------------------------------------------------------------------------
open import Data.Product using ( projβ ; projβ )

-- The result of the value is at least as senstive as the program
-- counter.
step-β : β {Ξ£ Ξ£' ΞΌ ΞΌ' Ξ Ο pc} {e : Expr Ξ Ο} {v : Value Ο} {ΞΈ : Env Ξ} β
             β¨ Ξ£ , ΞΌ , e β© ββ¨ ΞΈ , pc β© β¨ Ξ£' , ΞΌ' , v β© β
             pc β (lbl v)

step-β {pc = pc} {ΞΈ = ΞΈ} (Var ΟβΞ eq) rewrite eq = join-ββ pc (lbl (ΞΈ !! ΟβΞ))
step-β Unit = refl-β
step-β (Lbl β) = refl-β
step-β (Testβ x xβ xβ refl) = trans-β (step-β xβ) (join-ββ _ _)
step-β (Testβ x xβ xβ refl) = trans-β (step-β xβ) (join-ββ _ _)
step-β Fun = refl-β
step-β (App x xβ eq xβ) rewrite eq = projβ (unjoin-β (step-β xβ))
step-β (Inl x) = refl-β
step-β (Inr x) = refl-β
step-β (Caseβ x eq xβ) rewrite eq = projβ (unjoin-β (step-β xβ))
step-β (Caseβ x eq xβ) rewrite eq =  projβ (unjoin-β (step-β xβ))
step-β (Pair x xβ) = refl-β
step-β (Fst x eq) rewrite eq = trans-β (step-β x) (join-ββ _ _)
step-β (Snd x eq) rewrite eq = trans-β (step-β x) (join-ββ _ _)
step-β (LabelOf x) = step-β x
step-β GetLabel = refl-β
step-β (Wken p x) = step-β x
step-β {pc = pc} (Taint {β = β} refl xβ xβ _) = trans-β (join-ββ pc β ) (step-β xβ)
step-β (LabelOfRef x refl) = trans-β (step-β x) (join-ββ _ _)
step-β (New x) = refl-β
step-β {pc = pc} (Read {β = β} {β' = β'} x xβ refl) = trans-β {pc} {β'} {β β β'} (step-β x) (join-ββ β' β)
step-β (Write x xβ eq xβ xβ) = refl-β
step-β (LabelOfRef-FS x xβ refl) = trans-β (step-β x) (join-ββ _ _)
step-β (New-FS x) = refl-β
step-β (Read-FS x xβ refl) = trans-β (step-β x) (join-ββ _ _)
step-β (Write-FS x xβ xβ xβ eq xβ) = refl-β
step-β (Id x) = refl-β
step-β (UnId x eq) rewrite eq = trans-β (step-β x) (join-ββ _ _)
