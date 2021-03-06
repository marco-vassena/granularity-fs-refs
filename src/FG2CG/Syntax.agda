-- This module contains the FG ā CG conversion functions for
-- expressions, values and configurations.

open import Lattice

module FG2CG.Syntax {{š³ : Lattice}} where

open import CG as CG
open import FG as FG hiding (_āĀ¹ ; _āĀ² ; here ; there ; drop ; cons ; refl-ā)
open import FG2CG.Types public

mutual

  -- FG expressions are translated to CG thunks (they may perform
  -- side-effects).
  āŖ_ā«įµ : ā {Ī Ļ} ā FG.Expr Ī Ļ ā Thunk āŖ Ī ā«į¶ (LIO āŖ Ļ ā«įµ)
  āŖ ļ¼ļ¼ ā«įµ = toLabeled ā return ļ¼ļ¼ āįµ
  āŖ var ĻāĪ ā«įµ = toLabeled ā unlabel (var āŖ ĻāĪ ā«ā) āįµ
  āŖ Ī e ā«įµ = toLabeled ā return (Ī āŖ e ā«į“±) āįµ
  āŖ eā ā eā ā«įµ =
    bind āŖ eā ā«į“±
    ā bind (āŖ eā ā«į“± āĀ¹)
    ā toLabeled
      ā bind ā unlabel (var (there here)) āįµ
      ā bind (var here ā var (there here))
      ā unlabel (var here) āįµ āįµ āįµ āįµ āįµ
  āŖ āØ eā , eā ā© ā«įµ =
    toLabeled
      ā bind āŖ eā ā«į“±
      ā bind (āŖ eā ā«į“± āĀ¹)
      ā return āØ var (there here) , var here ā© āįµ āįµ āįµ
  āŖ fst e ā«įµ =
    toLabeled
      ā bind āŖ e ā«į“±
      ā bind ā unlabel (var here) āįµ
      ā unlabel (fst (var here)) āįµ āįµ āįµ
  āŖ snd e ā«įµ =
        toLabeled
      ā bind āŖ e ā«į“±
      ā bind ā unlabel (var here) āįµ
      ā unlabel (snd (var here)) āįµ āįµ āįµ
  āŖ inl e ā«įµ = toLabeled ā bind āŖ e ā«į“± ā return (inl (var here)) āįµ āįµ
  āŖ inr e ā«įµ = toLabeled ā bind āŖ e ā«į“± ā return (inr (var here)) āįµ āįµ
  āŖ case e eā eā ā«įµ =
    toLabeled
      ā bind āŖ e ā«į“±
      ā bind ā unlabel (var here) āįµ
      ā bind (case (var here) (wken āŖ eā ā«į“± (cons (drop (drop refl-ā)))) (wken āŖ eā ā«į“± (cons (drop (drop refl-ā)))))
      ā unlabel (var here) āįµ āįµ āįµ āįµ
  āŖ ā ā ā ā«įµ = toLabeled ā return ā ā ā āįµ
  āŖ eā ā-? eā ā«įµ =
    toLabeled
      ā bind āŖ eā ā«į“±
      ā bind (āŖ eā ā«į“± āĀ¹)
      ā bind ā toLabeled ā return ļ¼ļ¼ āįµ āįµ
      ā bind ā unlabel (var (there (there here))) āįµ
      ā bind ā unlabel (var (there (there here))) āįµ
      ā return (CG.if (var (there here) ā-? var here)
                 then inl (var (there (there here)))
                 else inr (var (there (there here)))) āįµ āįµ āįµ āįµ āįµ āįµ

  āŖ getLabel ā«įµ = toLabeled ā getLabel āįµ

  āŖ labelOf e ā«įµ =
    toLabeled
      ā bind āŖ e ā«į“±
      ā labelOf (var here) āįµ āįµ

  āŖ wken e p ā«įµ = bind ā return (wken āŖ e ā«į“± āŖ p ā«ā ) āįµ (var here)

  āŖ taint eā eā ā«įµ =
    toLabeled
      ā bind āŖ eā ā«į“±
      ā bind ā unlabel (var here) āįµ
      ā bind ā taint (var here) āįµ
      ā bind (wken āŖ eā ā«į“± (drop (drop (drop refl-ā))))
      ā unlabel (var here ) āįµ āįµ āįµ āįµ āįµ

  āŖ labelOfRef e ā«įµ =
    toLabeled
      ā bind āŖ e ā«į“±
      ā bind ā unlabel (var here) āįµ
      ā labelOfRef (var here) āįµ āįµ āįµ

  āŖ new e ā«įµ =
    toLabeled
      ā bind āŖ e ā«į“±
      ā new (var here) āįµ āįµ

  āŖ ! e ā«įµ =
    toLabeled
      ā bind āŖ e ā«į“±
      ā bind ā unlabel (var here) āįµ
      ā ! (var here) āįµ āįµ āįµ

  āŖ e ā eā ā«įµ =
    bind ā toLabeled
         ā bind āŖ e ā«į“±
         ā bind (āŖ eā ā«į“± āĀ¹)
         ā bind ā unlabel (var (there here)) āįµ
         ā var here ā var (there here) āįµ āįµ āįµ āįµ āįµ
    ā toLabeled ā return ļ¼ļ¼ āįµ āįµ

  āŖ Id e ā«įµ = toLabeled ā āŖ e ā«įµ āįµ

  āŖ unId e ā«įµ =
    toLabeled
      ā bind  āŖ e ā«į“±
      ā bind ā unlabel (var here) āįµ
      ā unlabel (var here) āįµ āįµ  āįµ

  -- Lift the thunk obtained from transforming an FG expression to a
  -- CG expression.
  āŖ_ā«į“± : ā {Ī Ļ} ā FG.Expr Ī Ļ ā CG.Expr āŖ Ī ā«į¶ (LIO āŖ Ļ ā«įµ)
  āŖ e ā«į“± = ā āŖ e ā«įµ āįµ

  -- Environment translation (pointwise).
  āŖ_ā«įµ : ā {Ī} ā FG.Env Ī ā CG.Env āŖ Ī ā«į¶
  āŖ [] ā«įµ = []
  āŖ v ā· Īø ā«įµ = āŖ v ā«ā±½ ā· āŖ Īø ā«įµ

  -- Raw value translation.
  āŖ_ā«į“æ : ā {Ļ} ā FG.Raw Ļ ā CG.Value āŖ Ļ ā«įµā²
  āŖ ļ¼ļ¼ ā«į“æ = ļ¼ļ¼
  āŖ āØ e , Īø ā©į¶ ā«į“æ = āØ āŖ e ā«į“± , āŖ Īø ā«įµ ā©į¶
  āŖ inl v ā«į“æ = inl āŖ v ā«ā±½
  āŖ inr v ā«į“æ = inr āŖ v ā«ā±½
  āŖ āØ vā , vā ā© ā«į“æ = āØ āŖ vā ā«ā±½ , āŖ vā ā«ā±½ ā©
  āŖ Refį“µ ā n ā«į“æ = Refį“µ ā n
  āŖ RefĖ¢ n ā«į“æ = RefĖ¢ n
  āŖ ā ā ā ā«į“æ = ā ā ā
  āŖ Id v ā«į“æ = āŖ v ā«ā±½

  -- Value translation.
  āŖ_ā«ā±½ : ā {Ļ} ā FG.Value Ļ ā CG.Value āŖ Ļ ā«įµ
  āŖ r ^ ā ā«ā±½ = Labeled ā āŖ r ā«į“æ

open import Function as F
import Data.Product as P

-- Used in generic module (it requires has an extra label argument)
āŖ_ā«į“æā² : ā {Ļ} ā (FG.Raw Ļ P.Ć Label) ā CG.Value āŖ Ļ ā«įµā²
āŖ_ā«į“æā² = P.uncurry $ flip $ const āŖ_ā«į“æ

āŖ_ā«į“ø : ā {Ļ} ā FG.Value Ļ ā CG.LValue āŖ Ļ ā«įµā²
āŖ r ^ ā ā«į“ø = āŖ r ā«į“æ P., ā

--------------------------------------------------------------------------------
-- Store conversion (pointwise and derived generically)

-- Notice that we pass around the implicit parameters because
-- otherwise we get unification problems.
-- open import Generic.Store.Convert {FG.Ty} {CG.Ty} {FG.Raw} {CG.Value} āŖ_ā«įµā² (flip $ const āŖ_ā«į“æ) public

-- open import Generic.Heap.Convert {FG.Ty} {CG.Ty} {FG.Value} {CG.LValue} āŖ_ā«įµā² āŖ_ā«į“ø public

open import Generic.PState.Convert {FG.Ty} {CG.Ty} āŖ_ā«įµā² āŖ_ā«įµā² {FG.Raw} {CG.Value} {FG.Value} {CG.LValue} (flip $ const āŖ_ā«į“æ) (flip $ const āŖ_ā«į“ø) public

--------------------------------------------------------------------------------
-- Conversion of initial and final  configurations.

āŖ_ā«į“µ : ā {Ī Ļ} ā FG.IConf Ī Ļ ā Label ā CG.EConf āŖ Ī ā«į¶ (LIO āŖ Ļ ā«įµ)
āŖ āØ Ī£ , Ī¼ , e ā© ā«į“µ pc = āØ āŖ Ī£ ā«Ė¢ , āŖ Ī¼ ā«į““ , pc , āŖ e ā«į“± ā©

āŖ_ā«į“µā² : ā {Ī Ļ} ā FG.IConf Ī Ļ ā Label ā CG.TConf āŖ Ī ā«į¶ (LIO āŖ Ļ ā«įµ)
āŖ āØ Ī£ , Ī¼ , e ā© ā«į“µā² pc = āØ āŖ Ī£ ā«Ė¢ , āŖ Ī¼ ā«į““ , pc , āŖ e ā«įµ ā©

āŖ_ā«į¶  : ā {Ļ} ā FG.FConf Ļ ā Label ā CG.FConf āŖ Ļ ā«įµ
āŖ āØ Ī£ , Ī¼ , v ā© ā«į¶  pc = āØ āŖ Ī£ ā«Ė¢ , āŖ Ī¼ ā«į““ , pc , āŖ v ā«ā±½ ā©
