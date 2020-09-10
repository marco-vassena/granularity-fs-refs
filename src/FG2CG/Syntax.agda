-- This module contains the FG → CG conversion functions for
-- expressions, values and configurations.

open import Lattice

module FG2CG.Syntax {{𝑳 : Lattice}} where

open import CG as CG
open import FG as FG hiding (_↑¹ ; _↑² ; here ; there ; drop ; cons ; refl-⊆)
open import FG2CG.Types public

mutual

  -- FG expressions are translated to CG thunks (they may perform
  -- side-effects).
  ⟪_⟫ᵀ : ∀ {Γ τ} → FG.Expr Γ τ → Thunk ⟪ Γ ⟫ᶜ (LIO ⟪ τ ⟫ᵗ)
  ⟪ （） ⟫ᵀ = toLabeled ⌞ return （） ⌟ᵀ
  ⟪ var τ∈Γ ⟫ᵀ = toLabeled ⌞ unlabel (var ⟪ τ∈Γ ⟫∈) ⌟ᵀ
  ⟪ Λ e ⟫ᵀ = toLabeled ⌞ return (Λ ⟪ e ⟫ᴱ) ⌟ᵀ
  ⟪ e₁ ∘ e₂ ⟫ᵀ =
    bind ⟪ e₁ ⟫ᴱ
    ⌞ bind (⟪ e₂ ⟫ᴱ ↑¹)
    ⌞ toLabeled
      ⌞ bind ⌞ unlabel (var (there here)) ⌟ᵀ
      ⌞ bind (var here ∘ var (there here))
      ⌞ unlabel (var here) ⌟ᵀ ⌟ᵀ ⌟ᵀ ⌟ᵀ ⌟ᵀ
  ⟪ ⟨ e₁ , e₂ ⟩ ⟫ᵀ =
    toLabeled
      ⌞ bind ⟪ e₁ ⟫ᴱ
      ⌞ bind (⟪ e₂ ⟫ᴱ ↑¹)
      ⌞ return ⟨ var (there here) , var here ⟩ ⌟ᵀ ⌟ᵀ ⌟ᵀ
  ⟪ fst e ⟫ᵀ =
    toLabeled
      ⌞ bind ⟪ e ⟫ᴱ
      ⌞ bind ⌞ unlabel (var here) ⌟ᵀ
      ⌞ unlabel (fst (var here)) ⌟ᵀ ⌟ᵀ ⌟ᵀ
  ⟪ snd e ⟫ᵀ =
        toLabeled
      ⌞ bind ⟪ e ⟫ᴱ
      ⌞ bind ⌞ unlabel (var here) ⌟ᵀ
      ⌞ unlabel (snd (var here)) ⌟ᵀ ⌟ᵀ ⌟ᵀ
  ⟪ inl e ⟫ᵀ = toLabeled ⌞ bind ⟪ e ⟫ᴱ ⌞ return (inl (var here)) ⌟ᵀ ⌟ᵀ
  ⟪ inr e ⟫ᵀ = toLabeled ⌞ bind ⟪ e ⟫ᴱ ⌞ return (inr (var here)) ⌟ᵀ ⌟ᵀ
  ⟪ case e e₁ e₂ ⟫ᵀ =
    toLabeled
      ⌞ bind ⟪ e ⟫ᴱ
      ⌞ bind ⌞ unlabel (var here) ⌟ᵀ
      ⌞ bind (case (var here) (wken ⟪ e₁ ⟫ᴱ (cons (drop (drop refl-⊆)))) (wken ⟪ e₂ ⟫ᴱ (cons (drop (drop refl-⊆)))))
      ⌞ unlabel (var here) ⌟ᵀ ⌟ᵀ ⌟ᵀ ⌟ᵀ
  ⟪ ⌞ ℓ ⌟ ⟫ᵀ = toLabeled ⌞ return ⌞ ℓ ⌟ ⌟ᵀ
  ⟪ e₁ ⊑-? e₂ ⟫ᵀ =
    toLabeled
      ⌞ bind ⟪ e₁ ⟫ᴱ
      ⌞ bind (⟪ e₂ ⟫ᴱ ↑¹)
      ⌞ bind ⌞ toLabeled ⌞ return （） ⌟ᵀ ⌟ᵀ
      ⌞ bind ⌞ unlabel (var (there (there here))) ⌟ᵀ
      ⌞ bind ⌞ unlabel (var (there (there here))) ⌟ᵀ
      ⌞ return (CG.if (var (there here) ⊑-? var here)
                 then inl (var (there (there here)))
                 else inr (var (there (there here)))) ⌟ᵀ ⌟ᵀ ⌟ᵀ ⌟ᵀ ⌟ᵀ ⌟ᵀ

  ⟪ getLabel ⟫ᵀ = toLabeled ⌞ getLabel ⌟ᵀ

  ⟪ labelOf e ⟫ᵀ =
    toLabeled
      ⌞ bind ⟪ e ⟫ᴱ
      ⌞ labelOf (var here) ⌟ᵀ ⌟ᵀ

  ⟪ wken e p ⟫ᵀ = bind ⌞ return (wken ⟪ e ⟫ᴱ ⟪ p ⟫⊆ ) ⌟ᵀ (var here)

  ⟪ taint e₁ e₂ ⟫ᵀ =
    toLabeled
      ⌞ bind ⟪ e₁ ⟫ᴱ
      ⌞ bind ⌞ unlabel (var here) ⌟ᵀ
      ⌞ bind ⌞ taint (var here) ⌟ᵀ
      ⌞ bind (wken ⟪ e₂ ⟫ᴱ (drop (drop (drop refl-⊆))))
      ⌞ unlabel (var here ) ⌟ᵀ ⌟ᵀ ⌟ᵀ ⌟ᵀ ⌟ᵀ

  ⟪ labelOfRef e ⟫ᵀ =
    toLabeled
      ⌞ bind ⟪ e ⟫ᴱ
      ⌞ bind ⌞ unlabel (var here) ⌟ᵀ
      ⌞ labelOfRef (var here) ⌟ᵀ ⌟ᵀ ⌟ᵀ

  ⟪ new e ⟫ᵀ =
    toLabeled
      ⌞ bind ⟪ e ⟫ᴱ
      ⌞ new (var here) ⌟ᵀ ⌟ᵀ

  ⟪ ! e ⟫ᵀ =
    toLabeled
      ⌞ bind ⟪ e ⟫ᴱ
      ⌞ bind ⌞ unlabel (var here) ⌟ᵀ
      ⌞ ! (var here) ⌟ᵀ ⌟ᵀ ⌟ᵀ

  ⟪ e ≔ e₁ ⟫ᵀ =
    bind ⌞ toLabeled
         ⌞ bind ⟪ e ⟫ᴱ
         ⌞ bind (⟪ e₁ ⟫ᴱ ↑¹)
         ⌞ bind ⌞ unlabel (var (there here)) ⌟ᵀ
         ⌞ var here ≔ var (there here) ⌟ᵀ ⌟ᵀ ⌟ᵀ ⌟ᵀ ⌟ᵀ
    ⌞ toLabeled ⌞ return （） ⌟ᵀ ⌟ᵀ

  ⟪ Id e ⟫ᵀ = toLabeled ⌞ ⟪ e ⟫ᵀ ⌟ᵀ

  ⟪ unId e ⟫ᵀ =
    toLabeled
      ⌞ bind  ⟪ e ⟫ᴱ
      ⌞ bind ⌞ unlabel (var here) ⌟ᵀ
      ⌞ unlabel (var here) ⌟ᵀ ⌟ᵀ  ⌟ᵀ

  -- Lift the thunk obtained from transforming an FG expression to a
  -- CG expression.
  ⟪_⟫ᴱ : ∀ {Γ τ} → FG.Expr Γ τ → CG.Expr ⟪ Γ ⟫ᶜ (LIO ⟪ τ ⟫ᵗ)
  ⟪ e ⟫ᴱ = ⌞ ⟪ e ⟫ᵀ ⌟ᵀ

  -- Environment translation (pointwise).
  ⟪_⟫ᵉ : ∀ {Γ} → FG.Env Γ → CG.Env ⟪ Γ ⟫ᶜ
  ⟪ [] ⟫ᵉ = []
  ⟪ v ∷ θ ⟫ᵉ = ⟪ v ⟫ⱽ ∷ ⟪ θ ⟫ᵉ

  -- Raw value translation.
  ⟪_⟫ᴿ : ∀ {τ} → FG.Raw τ → CG.Value ⟪ τ ⟫ᵗ′
  ⟪ （） ⟫ᴿ = （）
  ⟪ ⟨ e , θ ⟩ᶜ ⟫ᴿ = ⟨ ⟪ e ⟫ᴱ , ⟪ θ ⟫ᵉ ⟩ᶜ
  ⟪ inl v ⟫ᴿ = inl ⟪ v ⟫ⱽ
  ⟪ inr v ⟫ᴿ = inr ⟪ v ⟫ⱽ
  ⟪ ⟨ v₁ , v₂ ⟩ ⟫ᴿ = ⟨ ⟪ v₁ ⟫ⱽ , ⟪ v₂ ⟫ⱽ ⟩
  ⟪ Refᴵ ℓ n ⟫ᴿ = Refᴵ ℓ n
  ⟪ Refˢ n ⟫ᴿ = Refˢ n
  ⟪ ⌞ ℓ ⌟ ⟫ᴿ = ⌞ ℓ ⌟
  ⟪ Id v ⟫ᴿ = ⟪ v ⟫ⱽ

  -- Value translation.
  ⟪_⟫ⱽ : ∀ {τ} → FG.Value τ → CG.Value ⟪ τ ⟫ᵗ
  ⟪ r ^ ℓ ⟫ⱽ = Labeled ℓ ⟪ r ⟫ᴿ

open import Function as F
import Data.Product as P

-- Used in generic module (it requires has an extra label argument)
⟪_⟫ᴿ′ : ∀ {τ} → (FG.Raw τ P.× Label) → CG.Value ⟪ τ ⟫ᵗ′
⟪_⟫ᴿ′ = P.uncurry $ flip $ const ⟪_⟫ᴿ

⟪_⟫ᴸ : ∀ {τ} → FG.Value τ → CG.LValue ⟪ τ ⟫ᵗ′
⟪ r ^ ℓ ⟫ᴸ = ⟪ r ⟫ᴿ P., ℓ

--------------------------------------------------------------------------------
-- Store conversion (pointwise and derived generically)

-- Notice that we pass around the implicit parameters because
-- otherwise we get unification problems.
-- open import Generic.Store.Convert {FG.Ty} {CG.Ty} {FG.Raw} {CG.Value} ⟪_⟫ᵗ′ (flip $ const ⟪_⟫ᴿ) public

-- open import Generic.Heap.Convert {FG.Ty} {CG.Ty} {FG.Value} {CG.LValue} ⟪_⟫ᵗ′ ⟪_⟫ᴸ public

open import Generic.PState.Convert {FG.Ty} {CG.Ty} ⟪_⟫ᵗ′ ⟪_⟫ᵗ′ {FG.Raw} {CG.Value} {FG.Value} {CG.LValue} (flip $ const ⟪_⟫ᴿ) (flip $ const ⟪_⟫ᴸ) public

--------------------------------------------------------------------------------
-- Conversion of initial and final  configurations.

⟪_⟫ᴵ : ∀ {Γ τ} → FG.IConf Γ τ → Label → CG.EConf ⟪ Γ ⟫ᶜ (LIO ⟪ τ ⟫ᵗ)
⟪ ⟨ Σ , μ , e ⟩ ⟫ᴵ pc = ⟨ ⟪ Σ ⟫ˢ , ⟪ μ ⟫ᴴ , pc , ⟪ e ⟫ᴱ ⟩

⟪_⟫ᴵ′ : ∀ {Γ τ} → FG.IConf Γ τ → Label → CG.TConf ⟪ Γ ⟫ᶜ (LIO ⟪ τ ⟫ᵗ)
⟪ ⟨ Σ , μ , e ⟩ ⟫ᴵ′ pc = ⟨ ⟪ Σ ⟫ˢ , ⟪ μ ⟫ᴴ , pc , ⟪ e ⟫ᵀ ⟩

⟪_⟫ᶠ : ∀ {τ} → FG.FConf τ → Label → CG.FConf ⟪ τ ⟫ᵗ
⟪ ⟨ Σ , μ , v ⟩ ⟫ᶠ pc = ⟨ ⟪ Σ ⟫ˢ , ⟪ μ ⟫ᴴ , pc , ⟪ v ⟫ⱽ ⟩
