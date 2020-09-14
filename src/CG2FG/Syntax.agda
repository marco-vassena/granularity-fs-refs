-- CG → FG translation for all the categories of the calculus.

open import Lattice as L

module CG2FG.Syntax {{𝑳 : Lattice}} where

open import CG as CG hiding (_↑¹ ; _↑² ; here ; there ; drop ; cons ; refl-⊆)
open import FG as FG
open import CG2FG.Types public
open import Data.Product renaming (_,_ to _^_)

mutual

  -- Value to value translation
  ⟦_⟧ⱽ : ∀ {τ} → CG.Value τ → Label → FG.Value ⟦ τ ⟧ᵗ
  ⟦ v ⟧ⱽ pc = ⟦ v ⟧ᴿ pc ^ pc

  -- Value to raw value translation
  ⟦_⟧ᴿ : ∀ {τ} → CG.Value τ → Label → FG.Raw ⟦ τ ⟧ᵗ
  ⟦ （） ⟧ᴿ pc = （）
  ⟦ ⟨ e , θ ⟩ᶜ ⟧ᴿ pc = ⟨ ⟦ e ⟧ᴱ , ⟦ θ ⟧ᵉ pc ⟩ᶜ
  ⟦ ⟨ t , θ ⟩ᵀ ⟧ᴿ pc = ⟨ ⟦ t ⟧ᵀ ↑¹ , ⟦ θ ⟧ᵉ pc ⟩ᶜ
  ⟦ inl v ⟧ᴿ pc = inl (⟦ v ⟧ⱽ pc)
  ⟦ inr v ⟧ᴿ pc = inr (⟦ v ⟧ⱽ pc)
  ⟦ ⟨ v , v₁ ⟩ ⟧ᴿ pc = ⟨ ⟦ v ⟧ⱽ pc , ⟦ v₁ ⟧ⱽ pc ⟩
  ⟦ Labeled ℓ v ⟧ᴿ pc = Id (⟨ (⌞ ℓ ⌟ ^ ℓ) , ⟦ v ⟧ⱽ ℓ ⟩ ^ pc)  -- This is enforcing the label on the label here!
  ⟦ Refᴵ ℓ n ⟧ᴿ pc = Refᴵ ℓ n
  ⟦ Refˢ n ⟧ᴿ pc = Refˢ n
  ⟦ ⌞ ℓ ⌟ ⟧ᴿ pc = ⌞ ℓ ⌟

  -- Environments.
  ⟦_⟧ᵉ : ∀ {Γ} → CG.Env Γ → Label → FG.Env ⟦ Γ ⟧ᶜ
  ⟦ [] ⟧ᵉ _ = []
  ⟦ v ∷ θ ⟧ᵉ pc = (⟦ v ⟧ⱽ pc) ∷ ⟦ θ ⟧ᵉ pc

  -- Expressions.
  ⟦_⟧ᴱ : ∀ {Γ τ} → CG.Expr Γ τ → FG.Expr ⟦ Γ ⟧ᶜ ⟦ τ ⟧ᵗ
  ⟦ var τ∈Γ ⟧ᴱ = var ⟦ τ∈Γ ⟧∈
  ⟦ Λ e ⟧ᴱ = Λ ⟦ e ⟧ᴱ
  ⟦ e ∘ e₁ ⟧ᴱ = ⟦ e ⟧ᴱ ∘ ⟦ e₁ ⟧ᴱ
  ⟦ ⟨ e , e₁ ⟩ ⟧ᴱ = ⟨ ⟦ e ⟧ᴱ , ⟦ e₁ ⟧ᴱ ⟩
  ⟦ fst e ⟧ᴱ = fst ⟦ e ⟧ᴱ
  ⟦ snd e ⟧ᴱ = snd ⟦ e ⟧ᴱ
  ⟦ inl e ⟧ᴱ = inl ⟦ e ⟧ᴱ
  ⟦ inr e ⟧ᴱ = inr ⟦ e ⟧ᴱ
  ⟦ case e e₁ e₂ ⟧ᴱ = case ⟦ e ⟧ᴱ ⟦ e₁ ⟧ᴱ ⟦ e₂ ⟧ᴱ
  ⟦ ⌞ t ⌟ᵀ ⟧ᴱ = Λ (⟦ t ⟧ᵀ ↑¹)
  ⟦ wken e x ⟧ᴱ = wken ⟦ e ⟧ᴱ ⟦ x ⟧⊆
  ⟦ （） ⟧ᴱ = （）
  ⟦ ⌞ ℓ ⌟ ⟧ᴱ = ⌞ ℓ ⌟
  ⟦ e₁ ⊑-? e₂ ⟧ᴱ = ⟦ e₁ ⟧ᴱ ⊑-? ⟦ e₂ ⟧ᴱ

  -- TODO: probably here we need different terms form FS refs operations
  -- Or at least split on the reference type

  -- Thunks.
  ⟦_⟧ᵀ : ∀ {τ Γ} → CG.Thunk Γ (LIO τ) → FG.Expr ⟦ Γ ⟧ᶜ ⟦ τ ⟧ᵗ
  ⟦ return e ⟧ᵀ = ⟦ e ⟧ᴱ
  ⟦ bind e₁ e₂ ⟧ᵀ = (Λ (taint (labelOf (var here)) (⟦ e₂ ⟧ᴱ FG.∘  Id （） )) ∘ (⟦ e₁ ⟧ᴱ FG.∘ Id （）))
  ⟦ unlabel e ⟧ᵀ = (Λ (taint (fst (var here)) (snd (var here)))) ∘ (unId ⟦ e ⟧ᴱ)
  ⟦ toLabeled e ⟧ᵀ =  (Λ (Id ⟨ (labelOf (var here)) , var here ⟩) ) ∘ (⟦ e ⟧ᴱ FG.∘ (Id （）))
  ⟦ labelOf e ⟧ᵀ = fst (unId ⟦ e ⟧ᴱ)
  ⟦ getLabel ⟧ᵀ = getLabel
  ⟦ taint e ⟧ᵀ = taint ⟦ e ⟧ᴱ （）
  ⟦ new e ⟧ᵀ = new (Λ (taint ( (fst (var here))) (snd (var here))) ∘ (unId ⟦ e ⟧ᴱ))
  ⟦ ! e ⟧ᵀ = ! ⟦ e ⟧ᴱ
  -- For FI refs the tainting occurs "automatically" because the label of the reference is fixed
  ⟦_⟧ᵀ  (_≔_ {s = I} e e₁) =
    ⟦ e ⟧ᴱ ≔ snd (unId ⟦ e₁ ⟧ᴱ)

  -- For FS refs this is not the case and we need to explicitly taint the raw value (like we did for new).
  ⟦_⟧ᵀ (_≔_ {s = S} e e₁) =
    ⟦ e ⟧ᴱ ≔ ((Λ (taint (fst (var here)) (snd (var here)))) ∘ unId ⟦ e₁ ⟧ᴱ )

  ⟦ labelOfRef e ⟧ᵀ = labelOfRef ⟦ e ⟧ᴱ

⟦_⟧ᴸ : ∀ {τ} → LValue τ → FG.Value ⟦ τ ⟧ᵗ
⟦ v ^ ℓ ⟧ᴸ = ⟦ v ⟧ⱽ ℓ

-- ⟦_⟧ᴸ′ : ∀ {τ} → LValue τ → FG.Value ⟦ τ ⟧ᵗ
-- ⟦ v ^ ℓ ⟧ᴸ′ pc = ⟦ v ⟧ᴿ ℓ ^ pc

--------------------------------------------------------------------------------

-- Derived store and memory translation.
-- open import Generic.Store.Convert {CG.Ty} {FG.Ty} {CG.Value} {FG.Raw} ⟦_⟧ᵗ ⟦_⟧ᴿ
--   renaming (
--   ) public

-- open import Generic.Heap.Convert {CG.Ty} {FG.Ty} {CG.LValue} {FG.Value} ⟦_⟧ᵗ ⟦_⟧ᴸ
--   renaming (
--   ) public

open import Function using (flip ; const ; _$_)

open import Generic.PState.Convert
  {CG.Ty} {FG.Ty} ⟦_⟧ᵗ ⟦_⟧ᵗ
  {CG.Value} {FG.Raw} {CG.LValue} {FG.Value} ⟦_⟧ᴿ (flip $ const ⟦_⟧ᴸ)
  renaming ( ⟪_⟫ᴾ to ⟦_⟧ᴾ
           ; ⟪_⟫ˢ to ⟦_⟧ˢ
           ; ⟪_⟫ᴹ to ⟦_⟧ᴹ
           ; ⟪_⟫ᴴ to ⟦_⟧ᴴ
           ) public


-- Convert and force program execution.
⟦_⟧ᴵ : ∀ {Γ τ} → EConf Γ (LIO τ) → IConf ⟦ Γ ⟧ᶜ ⟦ τ ⟧ᵗ
⟦ ⟨ Σ , μ , pc , e ⟩ ⟧ᴵ = ⟨ ⟦ Σ ⟧ˢ , ⟦ μ ⟧ᴴ ,  ⟦ e ⟧ᴱ ∘ (Id （）) ⟩
