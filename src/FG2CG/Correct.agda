-- This module proves that the FG → CG translation is
-- semantics-preserving

open import Lattice

module FG2CG.Correct {{𝑳 : Lattice}} where

open import Relation.Binary.PropositionalEquality
open import CG as CG hiding (step-⊑)

--------------------------------------------------------------------------------
-- Shorthands and helper lemmas about CG semantics

-- Force a thunk
⌞_⌟ᶠ : ∀ {τ Γ Σ Σ' μ μ' pc pc' v} {t : Thunk Γ (LIO τ)} {θ : Env Γ}
        → ⟨ Σ , μ , pc , t ⟩ ⇓⟨ θ ⟩ ⟨ Σ' , μ' , pc' , v ⟩
        → ⟨ Σ , μ , pc , ⌞ t ⌟ᵀ ⟩ ⇓ᶠ⟨ θ ⟩ ⟨ Σ' , μ' , pc' , v ⟩
⌞_⌟ᶠ = Force SThunk

-- Force bind.
Bindᶠ : ∀ {Γ τ₁ τ₂ Σ Σ' Σ'' μ μ' μ'' pc pc' pc'' v v₁ θ} {e₁ : Expr Γ (LIO τ₁)} {e₂ : Expr _ (LIO τ₂)}
           → ⟨ Σ , μ , pc , e₁ ⟩ ⇓ᶠ⟨ θ ⟩ ⟨ Σ' , μ' , pc' , v₁ ⟩
           → ⟨ Σ' , μ' , pc' , e₂ ⟩ ⇓ᶠ⟨ v₁ ∷ θ ⟩ ⟨ Σ'' , μ'' , pc'' , v ⟩
           → ⟨ Σ , μ , pc , ⌞ bind e₁ e₂ ⌟ᵀ ⟩ ⇓ᶠ⟨ θ ⟩ ⟨ Σ'' , μ'' , pc'' , v ⟩
Bindᶠ x₁ x₂ = ⌞ Bind x₁ x₂ ⌟ᶠ

-- To labeled in forcing semantics
ToLabeledᶠ  : ∀ {Γ Σ Σ' μ μ' pc pc' τ v θ} {t : Thunk Γ (LIO τ)}
              → ⟨ Σ , μ , pc , ⌞ t ⌟ᵀ ⟩ ⇓ᶠ⟨ θ ⟩ ⟨ Σ' , μ' , pc' , v ⟩
              → ⟨ Σ , μ , pc , ⌞ toLabeled ⌞ t ⌟ᵀ ⌟ᵀ ⟩ ⇓ᶠ⟨ θ ⟩ ⟨ Σ' , μ' , pc , Labeled pc' v ⟩
ToLabeledᶠ x = ⌞ ToLabeled x ⌟ᶠ

-- Force Wken
Wkenᶠ : ∀ {Γ Γ' Σ Σ' μ μ' pc pc' τ v θ} {e : Expr Γ (LIO τ)} (θ' : Env Γ')
        → ⟨ Σ , μ , pc , e ⟩ ⇓ᶠ⟨ θ ⟩ ⟨ Σ' , μ' , pc' , v ⟩
        → ⟨ Σ , μ , pc , wken e (drop-⊆₂ Γ Γ')  ⟩ ⇓ᶠ⟨ θ' ++ᴱ θ ⟩ ⟨ Σ' , μ' , pc' , v ⟩
Wkenᶠ {Γ' = Γ'} θ'' (Force x x₁) = Force (Wken (drop-⊆₂ _ Γ') x) x₁

-- Pure execution under weakening
⇓¹ : ∀ {Γ τ τ₁ v θ} {v₁ : Value τ₁} {e : Expr Γ τ}
     → e ⇓ᴾ⟨ θ ⟩ v
     → e ↑¹ ⇓ᴾ⟨ v₁ ∷ θ ⟩ v
⇓¹ x = Wken (drop refl-⊆) x

If₁ : ∀ {τ Γ θ v} {e₁ : Expr Γ Bool} {e₂ e₃ : Expr Γ τ} →
        e₁ ⇓ᴾ⟨ θ ⟩ (inl （）) →
        e₂ ⇓ᴾ⟨ θ ⟩ v →
        if e₁ then e₂ else e₃ ⇓ᴾ⟨ θ ⟩ v
If₁ x₁ x₂ = Case₁ x₁ (⇓¹ x₂)

If₂ : ∀ {τ Γ θ v} {e₁ : Expr Γ Bool} {e₂ e₃ : Expr Γ τ} →
        e₁ ⇓ᴾ⟨ θ ⟩ (inr （）) →
        e₃ ⇓ᴾ⟨ θ ⟩ v →
        if e₁ then e₂ else e₃ ⇓ᴾ⟨ θ ⟩ v
If₂ x₁ x₂ = Case₂ x₁ (⇓¹ x₂)

↑¹-⇓ᶠ  :  ∀ {Γ Σ Σ' μ μ' pc pc' τ τ' v θ} {e : Expr Γ (LIO τ)} {v₁ : Value τ'}
        → ⟨ Σ , μ , pc , e ⟩ ⇓ᶠ⟨ θ ⟩ ⟨ Σ' , μ' , pc' , v ⟩
        → ⟨ Σ , μ , pc , e ↑¹ ⟩ ⇓ᶠ⟨ v₁ ∷  θ ⟩ ⟨ Σ' , μ' , pc' , v ⟩
↑¹-⇓ᶠ {v₁ = v₁}  = Wkenᶠ (v₁ ∷ [])

⇓-with : ∀ {τ Γ Σ μ pc c₁ c₂ θ} {t : Thunk Γ (LIO τ)} →
            ⟨ Σ , μ , pc , t ⟩ ⇓⟨ θ ⟩ c₁ →
            c₁ ≡ c₂ → ⟨ Σ , μ , pc , t ⟩ ⇓⟨ θ ⟩ c₂
⇓-with x refl = x

open import FG as FG hiding (_↑¹ ; _↑² ; here ; there ; drop ; cons ; refl-⊆ )
open import FG2CG.Syntax

--------------------------------------------------------------------------------
-- Helping lemmas for contexts.
-- Lookup and slicing commute with translation.

⟪slice⟫-≡ : ∀ {Γ₁ Γ₂} → (θ : FG.Env Γ₂) → (p : Γ₁ FG.⊆ Γ₂) → ⟪ FG.slice θ p ⟫ᵉ ≡ CG.slice ⟪ θ ⟫ᵉ ⟪ p ⟫⊆
⟪slice⟫-≡ [] FG.base = refl
⟪slice⟫-≡ (v ∷ θ) (FG.cons p) rewrite ⟪slice⟫-≡ θ p = refl
⟪slice⟫-≡ (v ∷ θ) (FG.drop p) rewrite ⟪slice⟫-≡ θ p = refl

{-# REWRITE ⟪slice⟫-≡ #-}

lookup-≡ : ∀ {τ Γ} → (τ∈Γ : τ FG.∈ Γ) (θ : FG.Env Γ) →
            let r ^ ℓ = θ FG.!! τ∈Γ in  ⟪ θ ⟫ᵉ CG.!! ⟪ τ∈Γ ⟫∈ ≡ CG.Labeled ℓ ⟪ r ⟫ᴿ
lookup-≡ here (v ∷ θ) = refl
lookup-≡ (there τ∈Γ) (v ∷ θ) rewrite lookup-≡ τ∈Γ θ = refl

{-# REWRITE lookup-≡ #-}

--------------------------------------------------------------------------------

-- Lemmas about store generic translation.
-- import Generic.Store.Convert
-- open Generic.Store.Convert.Lemmas {FG.Ty} {CG.Ty} {FG.Raw} {CG.Value} ⟪_⟫ᵗ′ (λ r _ → ⟪ r ⟫ᴿ)

mutual

  -- TODO: why not trasnformation of the whole configuration?

    -- Correctness theorem with forcing semantics
  fg2cgᶠ : ∀ {pc Γ τ} {c : FG.IConf Γ τ} {c' : FG.FConf τ}  {θ : FG.Env Γ} →
             c ⇓⟨ θ , pc ⟩ c' →
             (⟪ c ⟫ᴵ pc) ⇓ᶠ⟨ ⟪ θ ⟫ᵉ ⟩  (⟪ c' ⟫ᶠ pc)
  fg2cgᶠ x = ⌞ fg2cg x ⌟ᶠ

  -- Correctness theorem: semantics preservation
  fg2cg :  ∀ {pc Γ τ} {c : FG.IConf Γ τ} {c' : FG.FConf τ}  {θ : FG.Env Γ} →
             c ⇓⟨ θ , pc ⟩ c' →
             (⟪ c ⟫ᴵ′ pc) ⇓⟨ ⟪ θ ⟫ᵉ ⟩ (⟪ c' ⟫ᶠ pc)

  fg2cg {θ = θ} (Var τ∈Γ eq) rewrite eq = ToLabeled ⌞ Unlabel (Var ⟪ τ∈Γ ⟫∈) refl ⌟ᶠ

  fg2cg Unit = ToLabeled ⌞ (Return Unit) ⌟ᶠ

  fg2cg (Lbl ℓ)  = ToLabeled ⌞ (Return (Lbl ℓ)) ⌟ᶠ

  fg2cg (Test₁ x₁ x₂ ℓ₁⊑ℓ₂ refl) =
    ToLabeled
      (Bindᶠ (fg2cgᶠ x₁)
      (Bindᶠ (↑¹-⇓ᶠ (fg2cgᶠ x₂))
      (Bindᶠ (ToLabeledᶠ ⌞ Return Unit ⌟ᶠ)
      (Bindᶠ ⌞ Unlabel (Var (there (there here))) (sym (ub (step-⊑ x₁))) ⌟ᶠ
      (Bindᶠ ⌞ Unlabel (Var (there (there here))) refl ⌟ᶠ
      ⌞ Return (If₁ (Test₁ (Var (there here)) (Var here) ℓ₁⊑ℓ₂)
               (Inl (Var (there (there here))))) ⌟ᶠ)))))

  fg2cg (Test₂ x₁ x₂ ℓ₁⋤ℓ₂ refl)=
    ToLabeled
      (Bindᶠ (fg2cgᶠ x₁)
      (Bindᶠ (↑¹-⇓ᶠ (fg2cgᶠ x₂))
      (Bindᶠ (ToLabeledᶠ ⌞ Return Unit ⌟ᶠ)
      (Bindᶠ ⌞ Unlabel (Var (there (there here))) (sym (ub (step-⊑ x₁))) ⌟ᶠ
      (Bindᶠ ⌞ Unlabel (Var (there (there here))) refl ⌟ᶠ
      ⌞ Return (If₂ (Test₂ (Var (there here)) (Var here) ℓ₁⋤ℓ₂)
               (Inr (Var (there (there here))))) ⌟ᶠ)))))

  fg2cg Fun = ToLabeled ⌞ (Return Fun) ⌟ᶠ

  fg2cg {θ = θ} (App {v = v} x x₁ eq x₂)
    rewrite eq | sym (ub (step-⊑ x₂)) =
    Bind (fg2cgᶠ x)
    (Bindᶠ (↑¹-⇓ᶠ (fg2cgᶠ x₁))
    (ToLabeledᶠ
      (Bindᶠ ⌞ Unlabel (Var (there here)) refl ⌟ᶠ
      (Bindᶠ (Force (App (Var here) (Var (there here)) SThunk) (fg2cg x₂))
      ⌞ Unlabel {ℓ = lbl v} (Var here) refl ⌟ᶠ))))

  fg2cg (Inl x) =
    ToLabeled
      (Bindᶠ (fg2cgᶠ x) ⌞ Return (Inl (Var here)) ⌟ᶠ)

  fg2cg (Inr x) =
    ToLabeled
      (Bindᶠ (fg2cgᶠ x) ⌞ Return (Inr (Var here)) ⌟ᶠ)

  fg2cg (Case₁ x eq x₁) rewrite eq | sym (ub (step-⊑ x₁)) =
    ToLabeled
      (Bindᶠ (fg2cgᶠ x)
      (Bindᶠ ⌞ Unlabel (Var here) refl ⌟ᶠ
      (Bindᶠ (Force (Case₁ (Var here) (Wken (cons (drop (drop refl-⊆))) SThunk)) (fg2cg x₁))
      ⌞ Unlabel (Var here) refl ⌟ᶠ)))

  fg2cg (Case₂ x eq x₁) rewrite eq | sym (ub (step-⊑ x₁)) =
      ToLabeled
      (Bindᶠ (fg2cgᶠ x)
      (Bindᶠ ⌞ Unlabel (Var here) refl ⌟ᶠ
      (Bindᶠ (Force (Case₂ (Var here) (Wken (cons (drop (drop refl-⊆))) SThunk)) (fg2cg x₁))
      ⌞ Unlabel (Var here) refl ⌟ᶠ)))

  fg2cg (Fst {ℓ = ℓ} {v₁ = r₁ ^ ℓ₁} {v₂ = r₂ ^ ℓ₂} x eq)
    rewrite eq | sym-⊔ ℓ₁ ℓ | sym (ub (step-⊑ x)) =
      ToLabeled
      (Bindᶠ (fg2cgᶠ x)
      (Bindᶠ ⌞ Unlabel (Var here) refl ⌟ᶠ
      ⌞ Unlabel (Fst (Var here)) refl ⌟ᶠ ))

  fg2cg (Snd {ℓ = ℓ} {v₁ = r₁ ^ ℓ₁} {v₂ = r₂ ^ ℓ₂} x eq)
    rewrite eq | sym-⊔ ℓ₂ ℓ | sym (ub (step-⊑ x)) =
      ToLabeled
        (Bindᶠ (fg2cgᶠ x)
        (Bindᶠ ⌞ Unlabel (Var here) refl ⌟ᶠ
        ⌞ Unlabel (Snd (Var here)) refl ⌟ᶠ ))

  fg2cg (LabelOf x) =
    ToLabeled
      (Bindᶠ (fg2cgᶠ x)
      ⌞ LabelOf (Var here) (sym (ub (step-⊑ x))) ⌟ᶠ )

  fg2cg GetLabel = ToLabeled ⌞ GetLabel ⌟ᶠ

  fg2cg {θ = θ} (Pair {v₁ = v₁} s₁ s₂) =
    ToLabeled
      (Bindᶠ (fg2cgᶠ s₁)
      (Bindᶠ (↑¹-⇓ᶠ (fg2cgᶠ s₂))
      ⌞ Return (Pair (Var (there here)) (Var here)) ⌟ᶠ ))

  fg2cg (Wken {Σ} {Σ'} p x)
    = Bind ⌞ Return (Wken  ⟪ p ⟫⊆  SThunk) ⌟ᶠ (Force (Var here) (fg2cg x))

  fg2cg {pc = pc} {θ = θ} (Taint {ℓ = ℓ} {pc' = pc'} {pc'' = pc''} refl x₁ x₂ b) =
    ToLabeled
      (Bindᶠ (fg2cgᶠ x₁)
      (Bindᶠ ⌞ Unlabel (Var here) refl ⌟ᶠ
      (Bindᶠ ⌞ Taint (Var here) (sym eq) ⌟ᶠ
      (Bindᶠ (Wkenᶠ (_ ∷ _ ∷ _ ∷ []) (fg2cgᶠ x₂))
      ⌞ Unlabel (Var here) (sym (ub (step-⊑ x₂))) ⌟ᶠ))))
    where
      eq =
        begin
          (pc ⊔ pc') ⊔ ℓ
        ≡⟨ cong (λ x → x ⊔ ℓ) (sym-⊔ pc pc')  ⟩
          (pc' ⊔ pc) ⊔ ℓ
        ≡⟨ sym (assoc-⊔ pc' pc ℓ) ⟩
          pc' ⊔ pc ⊔ ℓ
        ≡⟨ ub b ⟩
          pc ⊔ ℓ
        ∎
         where open ≡-Reasoning

  fg2cg (LabelOfRef x refl) =
    ToLabeled
      (Bindᶠ (fg2cgᶠ x)
      (Bindᶠ ⌞ Unlabel (Var here) (sym (ub pc⊑ℓ')) ⌟ᶠ
      ⌞ LabelOfRef (Var here) (sym-⊔ _ _ ) ⌟ᶠ))
    where pc⊑ℓ' = FG.step-⊑ x

  fg2cg {pc = pc} (New {ℓ = ℓ} {Σ' = Σ'} {μ' = μ'} {r = r} x) =
    ToLabeled
      (Bindᶠ (fg2cgᶠ x)
      ⌞ ⇓-with (New (Var here) (FG.step-⊑ x)) eq ⌟ᶠ)

   where memory-≡ = ∷ᴿ-≡ r (Σ' ℓ)
         value-≡ = cong₂ Refᴵ refl (∥ Σ' ∥-≡ ℓ)
         eq = cong₂ (λ Σ v → ⟨ Σ , ⟪ μ' ⟫ᴴ , pc , v ⟩) (CG.store-≡ (update-≡ˢ memory-≡)) value-≡

  fg2cg (Read x x₁ refl) =
    ToLabeled
      (Bindᶠ (fg2cgᶠ x)
      (Bindᶠ ⌞ Unlabel (Var here) (sym (ub (step-⊑ x))) ⌟ᶠ
      ⌞ Read (Var here) ⟪ x₁ ⟫∈ᴹ (sym-⊔ _ _) ⌟ᶠ))

  fg2cg {pc = pc} (Write {μ₃ = μ₃} {ℓ₁ = ℓ₁} x p x₁ ℓ₂⊑ℓ x₂) =
    Bind
      (ToLabeledᶠ (
        (Bindᶠ (fg2cgᶠ x)
        (Bindᶠ (↑¹-⇓ᶠ (fg2cgᶠ x₁))
        (Bindᶠ ⌞ Unlabel (Var (there here)) refl ⌟ᶠ
        ⌞ ⇓-with (Write (Var here) (Var (there here)) ⊑₁ ℓ₂⊑ℓ (write-≡ᴹ x₂)) eq ⌟ᶠ)))))
    (ToLabeledᶠ ⌞ Return Unit ⌟ᶠ)

    where eq = cong (λ Σ → ⟨ Σ , ⟪ μ₃ ⟫ᴴ , pc ⊔ ℓ₁ , （） ⟩) (CG.store-≡ (update-≡ˢ refl))
          ⊑₁ = join-⊑' (trans-⊑ (step-⊑ x₁) ℓ₂⊑ℓ) p

  fg2cg (Id x) = ToLabeled (fg2cgᶠ x)

  fg2cg (UnId x eq) =
    ToLabeled
      (Bindᶠ (fg2cgᶠ x)
      (Bindᶠ ⌞ Unlabel (Var here) (sym (ub (step-⊑ x))) ⌟ᶠ
      ⌞ Unlabel (Var here) eq ⌟ᶠ))

  fg2cg (LabelOfRef-FS x ∈₁ refl) =
    ToLabeled
      (Bindᶠ (fg2cgᶠ x)
      (Bindᶠ ⌞ Unlabel (Var here) (sym (ub pc⊑ℓ')) ⌟ᶠ
      ⌞ LabelOfRef-FS (Var here) ⟪ ∈₁ ⟫∈ᴴ refl ⌟ᶠ))
    where pc⊑ℓ' = FG.step-⊑ x

  fg2cg {pc = pc} (New-FS {Σ' = Σ'} {μ' = μ'} {v = v} x) =
    ToLabeled
      (Bindᶠ (fg2cgᶠ x)
      ⌞ ⇓-with (New-FS (Var here) (step-⊑ x)) eq ⌟ᶠ)
   where value-≡ = cong Refˢ ∥ μ' ∥-≡ᴴ
         eq = cong₂ (λ μ v → ⟨ ⟪ Σ' ⟫ˢ , μ , pc , v ⟩) (snocᴴ-≡ v μ') value-≡

  fg2cg (Read-FS x x₁ refl) =
    ToLabeled
      (Bindᶠ (fg2cgᶠ x)
      (Bindᶠ ⌞ Unlabel (Var here) (sym (ub (step-⊑ x))) ⌟ᶠ
      ⌞ Read-FS (Var here) ⟪ x₁ ⟫∈ᴴ refl ⌟ᶠ))

  fg2cg {pc = pc} (Write-FS {Σ₃ = Σ₃} {ℓ = ℓ} {ℓ₂ = ℓ₂} x x₁ ∈₁ ⊑₁ refl w) =
    Bind
      (ToLabeledᶠ (
        (Bindᶠ (fg2cgᶠ x)
        (Bindᶠ (↑¹-⇓ᶠ (fg2cgᶠ x₁))
        (Bindᶠ ⌞ Unlabel (Var (there here)) refl ⌟ᶠ
        ⌞ ⇓-with (Write-FS (Var here) (Var (there here)) ⟪ ∈₁ ⟫∈ᴴ ⊑₂ eq' (write-≡ᴴ w)) eq ⌟ᶠ)))))
    (ToLabeledᶠ ⌞ Return Unit ⌟ᶠ)
    where eq = cong (λ μ → ⟨ ⟪ Σ₃ ⟫ˢ , μ , pc ⊔ ℓ , （） ⟩) refl
          ⊑₂ = trans-⊑ (join-⊑' (step-⊑ x) refl-⊑) ⊑₁
          eq' = cong (_⊔ ℓ₂) (sym (ub (step-⊑ x)))
