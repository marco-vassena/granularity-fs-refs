-- Big-step semantics.

open import Lattice

module FG.Semantics {{𝑳 : Lattice}} where

open import FG.Types
open import FG.Syntax
open import Relation.Binary.PropositionalEquality

mutual

  -- Big-step operational semantics.
  --
  -- This definition expects a suitable mapping environment (θ : Env
  -- Γ) that binds all the free variables in the program (IConf Γ τ)
  -- and ensures type preservation by construction (same type τ in
  -- IConf and FConf).
  data Step {Γ} (θ : Env Γ) (pc : Label) : ∀ {τ} → IConf Γ τ → FConf τ → Set where

    Var : ∀ {Σ μ τ ℓ'} (τ∈Γ : τ ∈ Γ) →
          let v ^ ℓ = (θ !! τ∈Γ) in
          ℓ' ≡ (pc ⊔ ℓ) →
          Step θ pc ⟨ Σ , μ , var τ∈Γ ⟩ ⟨ Σ , μ , v ^ ℓ' ⟩

    Unit : ∀ {Σ μ} → Step θ pc ⟨ Σ , μ , （） ⟩ ⟨ Σ , μ , （） ^ pc ⟩

    Lbl : ∀ {Σ μ} (ℓ : Label) → Step θ pc ⟨ Σ , μ , ⌞ ℓ ⌟ ⟩ ⟨ Σ , μ , ⌞ ℓ ⌟ ^ pc ⟩

    Test₁ : ∀ {Σ₁ Σ₂ Σ₃ μ₁ μ₂ μ₃ e₁ e₂ ℓ ℓ₁ ℓ₁' ℓ₂ ℓ₂'} →
              ⟨ Σ₁ , μ₁ , e₁ ⟩ ⇓⟨ θ , pc ⟩ ⟨ Σ₂ , μ₂ , ⌞ ℓ₁ ⌟ ^ ℓ₁' ⟩ →
              ⟨ Σ₂ , μ₂ , e₂ ⟩ ⇓⟨ θ , pc ⟩ ⟨ Σ₃ , μ₃ , ⌞ ℓ₂ ⌟ ^ ℓ₂' ⟩ →
              ℓ₁ ⊑ ℓ₂ →
              ℓ ≡ ℓ₁' ⊔ ℓ₂' →
              Step θ pc ⟨ Σ₁ , μ₁ , e₁ ⊑-? e₂ ⟩ ⟨ Σ₃ , μ₃ , true pc ^ ℓ ⟩

    Test₂ : ∀ {Σ₁ Σ₂ Σ₃ μ₁ μ₂ μ₃ e₁ e₂ ℓ ℓ₁ ℓ₁' ℓ₂ ℓ₂'} →
              ⟨ Σ₁ , μ₁ , e₁ ⟩ ⇓⟨ θ , pc ⟩ ⟨ Σ₂ , μ₂ , ⌞ ℓ₁ ⌟ ^ ℓ₁' ⟩ →
              ⟨ Σ₂ , μ₂ , e₂ ⟩ ⇓⟨ θ , pc ⟩ ⟨ Σ₃ , μ₃ , ⌞ ℓ₂ ⌟ ^ ℓ₂' ⟩ →
              ℓ₁ ⋤ ℓ₂ →
              ℓ ≡ ℓ₁' ⊔ ℓ₂' →
              Step θ pc ⟨ Σ₁ , μ₁ , e₁ ⊑-? e₂ ⟩ ⟨ Σ₃ , μ₃ , false pc ^ ℓ ⟩

    Fun : ∀ {Σ μ τ₁ τ₂} {e : Expr (τ₁ ∷ Γ) τ₂}  → Step θ pc ⟨ Σ , μ , Λ e ⟩ ⟨ Σ , μ , ⟨ e , θ ⟩ᶜ ^ pc ⟩

    App : ∀ {Σ Σ' Σ'' Σ''' μ μ' μ'' μ''' Γ' θ' ℓ ℓ' τ₁ τ₂}
            {e₁ : Expr Γ (τ₁ ➔ τ₂)} {e : Expr (τ₁ ∷ Γ') τ₂} →
             {e₂ : Expr _ τ₁} {v₂ : Value τ₁} {v : Value τ₂} →
             ⟨ Σ , μ , e₁ ⟩ ⇓⟨ θ , pc ⟩ ⟨ Σ' , μ' , ⟨ e , θ' ⟩ᶜ ^ ℓ ⟩ →
             ⟨ Σ' , μ' , e₂ ⟩ ⇓⟨ θ , pc ⟩ ⟨ Σ'' , μ'' , v₂ ⟩ →
             ℓ' ≡ pc ⊔ ℓ →
             ⟨ Σ'' , μ'' , e ⟩ ⇓⟨ v₂ ∷ θ' , ℓ' ⟩ ⟨ Σ''' , μ''' , v ⟩ →
             Step θ pc ⟨ Σ , μ , e₁ ∘ e₂ ⟩ ⟨ Σ''' , μ''' , v ⟩

    Wken : ∀ {Σ Σ' μ μ' τ Γ'} {e : Expr Γ' τ} {v : Value τ} →
           (p : Γ' ⊆ Γ) → ⟨ Σ , μ , e ⟩ ⇓⟨ slice θ p , pc ⟩ ⟨ Σ' , μ' , v ⟩ →
           Step θ pc ⟨ Σ , μ , wken e p ⟩ ⟨ Σ' , μ' , v ⟩

    Inl : ∀ {Σ Σ' μ μ' τ₁ τ₂} {e : Expr _ τ₁} {v : Value τ₁}  →
            ⟨ Σ , μ , e ⟩ ⇓⟨ θ , pc ⟩ ⟨ Σ' , μ' , v ⟩ →
            Step θ pc ⟨ Σ , μ , inl {τ₂ = τ₂} e ⟩ ⟨ Σ' , μ' , inl v ^ pc ⟩

    Inr : ∀ {Σ Σ' μ μ' τ₁ τ₂} {e : Expr _ τ₂} {v : Value τ₂}  →
            ⟨ Σ , μ , e ⟩ ⇓⟨ θ , pc ⟩ ⟨ Σ' , μ' , v ⟩ →
            Step θ pc ⟨ Σ , μ , inr {τ₁ = τ₁} e ⟩ ⟨ Σ' , μ' , inr v ^ pc ⟩

    Case₁ :  ∀ {Σ Σ' Σ'' μ μ' μ'' ℓ ℓ' τ₁ τ₂ τ} {e : Expr _ (τ₁ + τ₂)} {e₁ : Expr _ τ}  {e₂ : Expr _ τ}  →
             {v₁ : Value τ₁} {v : Value τ} →
             ⟨ Σ , μ , e ⟩ ⇓⟨ θ , pc ⟩ ⟨ Σ' , μ' , inl v₁ ^ ℓ ⟩ →
             ℓ' ≡ pc ⊔ ℓ →
             ⟨ Σ' , μ' , e₁ ⟩ ⇓⟨ v₁ ∷ θ , ℓ' ⟩ ⟨ Σ'' , μ'' , v ⟩ →
             Step θ pc ⟨ Σ , μ , case e e₁ e₂ ⟩ ⟨ Σ'' , μ'' , v ⟩

    Case₂ :  ∀ {Σ Σ' Σ'' μ μ' μ'' ℓ ℓ' τ₁ τ₂ τ} {e : Expr _ (τ₁ + τ₂)} {e₁ : Expr _ τ}  {e₂ : Expr _ τ}  →
             {v₂ : Value τ₂} {v : Value τ} →
             ⟨ Σ , μ , e ⟩ ⇓⟨ θ , pc ⟩ ⟨ Σ' , μ' , inr v₂ ^ ℓ ⟩ →
             ℓ' ≡ pc ⊔ ℓ →
             ⟨ Σ' , μ' , e₂ ⟩ ⇓⟨ v₂ ∷ θ , ℓ' ⟩ ⟨ Σ'' , μ'' , v ⟩ →
             Step θ pc ⟨ Σ , μ , case e e₁ e₂ ⟩ ⟨ Σ'' , μ'' , v ⟩


    Pair : ∀ {Σ Σ' Σ'' μ μ' μ'' τ₁ τ₂} {e₁ : Expr _ τ₁} {e₂ : Expr _ τ₂} {v₁ : Value τ₁} {v₂ : Value τ₂} →
             ⟨ Σ , μ , e₁ ⟩ ⇓⟨ θ , pc ⟩ ⟨ Σ' , μ' , v₁ ⟩ →
             ⟨ Σ' , μ' , e₂ ⟩ ⇓⟨ θ , pc ⟩ ⟨ Σ'' , μ'' , v₂ ⟩ →
             Step θ pc ⟨ Σ , μ , ⟨ e₁ , e₂ ⟩ ⟩ ⟨ Σ'' , μ'' , ⟨ v₁ , v₂ ⟩ ^ pc ⟩

    Fst : ∀ {Σ Σ' μ μ' τ₁ τ₂ ℓ ℓ'} {e : Expr _ (τ₁ × τ₂)} {v₁ : Value τ₁} {v₂ : Value τ₂} →
             ⟨ Σ , μ , e ⟩ ⇓⟨ θ , pc ⟩ ⟨ Σ' , μ' , ⟨ v₁ , v₂ ⟩ ^ ℓ ⟩ →
             let r ^ ℓ₁ = v₁ in
             ℓ' ≡ ℓ ⊔ ℓ₁ →
            Step θ pc ⟨ Σ , μ , fst e ⟩ ⟨ Σ' , μ' , r ^ ℓ' ⟩

    Snd : ∀ {Σ Σ' μ μ' τ₁ τ₂ ℓ ℓ'} {e : Expr _ (τ₁ × τ₂)} {v₁ : Value τ₁} {v₂ : Value τ₂} →
             ⟨ Σ , μ , e ⟩ ⇓⟨ θ , pc ⟩ ⟨ Σ' , μ' , ⟨ v₁ , v₂ ⟩ ^ ℓ ⟩ →
             let r ^ ℓ₂ = v₂ in
             ℓ' ≡ ℓ ⊔ ℓ₂ →
             Step θ pc ⟨ Σ , μ , snd e ⟩ ⟨ Σ' , μ' , r ^ ℓ' ⟩

    LabelOf : ∀ {Σ Σ' μ μ' ℓ τ} {e : Expr _ τ} {r : Raw τ} →
                ⟨ Σ , μ , e ⟩ ⇓⟨ θ , pc ⟩ ⟨ Σ' , μ' , r ^ ℓ ⟩ →
                Step θ pc ⟨ Σ , μ , labelOf e ⟩ ⟨ Σ' , μ' , ⌞ ℓ ⌟ ^ ℓ ⟩

    GetLabel : ∀ {Σ μ} → Step θ pc ⟨ Σ , μ , getLabel ⟩ ⟨ Σ , μ , (⌞ pc ⌟ ^ pc) ⟩

    Taint : ∀ {Σ Σ' Σ'' μ μ' μ'' ℓ pc' pc'' e₁ τ} {e₂ : Expr Γ τ} {v : Value τ} →
              (eq : pc'' ≡ pc ⊔ ℓ) →
              Step θ pc ⟨ Σ , μ , e₁ ⟩ ⟨ Σ' , μ' , ⌞ ℓ ⌟ ^ pc' ⟩ →
              Step θ pc''  ⟨ Σ' , μ' , e₂ ⟩ ⟨ Σ'' , μ'' , v ⟩ →
              (pc'⊑pc'' : pc' ⊑ pc'') →
              Step θ pc ⟨ Σ , μ , taint e₁ e₂ ⟩ ⟨ Σ'' , μ'' , v ⟩

    LabelOfRef : ∀ {Σ Σ' μ μ' ℓ ℓ' ℓ'' n τ} {e : Expr Γ (Ref I τ)} →
                 ⟨ Σ , μ , e ⟩ ⇓⟨ θ , pc ⟩ ⟨ Σ' , μ' , Refᴵ ℓ n ^ ℓ' ⟩ →
                 (eq : ℓ'' ≡ ℓ ⊔ ℓ') →
                 Step θ pc ⟨ Σ , μ , labelOfRef e ⟩ ⟨ Σ' , μ' , ⌞ ℓ ⌟ ^ ℓ'' ⟩

    New : ∀ {ℓ τ Σ Σ' μ μ'} {e : Expr Γ _} {r : Raw τ} →
          ⟨ Σ , μ , e ⟩ ⇓⟨ θ , pc ⟩ ⟨ Σ' , μ' , r ^ ℓ ⟩ →
          let M = Σ' ℓ in
          Step θ pc ⟨ Σ , μ , new {s = I} e ⟩ ⟨  Σ' [ ℓ ↦ snocᴹ M r ]ˢ , μ' , (Refᴵ ℓ ∥ M ∥ᴹ) ^ pc ⟩

    -- This is better than asking ℓ' ⊑ ℓ and returning the value at pc
    -- ⊔ ℓ. The combination pc ⊑ ℓ' (step-⊑) and ℓ' ⊑ ℓ implies pc ⊑
    -- ℓ, thus the rule would not allow to read lower references.
    Read : ∀ {Σ Σ' μ μ' ℓ ℓ' ℓ'' n τ} {e : Expr _ (Ref I τ)} {r : Raw τ } →
           ⟨ Σ , μ , e ⟩ ⇓⟨ θ , pc ⟩ ⟨ Σ' , μ' , (Refᴵ ℓ n) ^ ℓ' ⟩ →
           n ↦ r ∈ᴹ (Σ' ℓ) →
           (eq : ℓ'' ≡ (ℓ ⊔ ℓ')) →
           Step θ pc ⟨ Σ , μ , ! e ⟩  ⟨ Σ' , μ' ,  r ^ ℓ'' ⟩

    Write : ∀ {Σ₁ Σ₂ Σ₃ μ₁ μ₂ μ₃ ℓ ℓ₂ ℓ₁ n τ} {M' : Memory ℓ} {e₁ : Expr _ (Ref I τ)}
              {e₂ : Expr _ τ} {r₂ : Raw τ} →
             ⟨ Σ₁ , μ₁ , e₁ ⟩ ⇓⟨ θ , pc ⟩ ⟨ Σ₂ , μ₂ , (Refᴵ ℓ n) ^ ℓ₁ ⟩ →
             -- TODO: It was l' ⊑ pc, wouldn't this imply pc ≡ ℓ' (from pc ⊑ ℓ'). Probably a
             -- typo, but check actual paper and formalization online.
             -- The paper is correct, there was a typo in the rule.
              ℓ₁ ⊑ ℓ →
             ⟨ Σ₂ , μ₂ , e₂ ⟩ ⇓⟨ θ , pc ⟩ ⟨ Σ₃ , μ₃ , r₂ ^ ℓ₂ ⟩ →
             (ℓ₂⊑ℓ : ℓ₂ ⊑ ℓ) →
               M' ≔ (Σ₃ ℓ) [ n ↦ r₂ ]ᴹ →
             Step θ pc ⟨ Σ₁ , μ₁ , e₁ ≔ e₂ ⟩ ⟨ Σ₃ [ ℓ ↦ M' ]ˢ , μ₃ , （） ^ pc ⟩

    --------------------------------------------------------------------------------
    -- Flow Sensitive (FS) primitives

    -- For FS refs, the semantics of labelOf is similar to regular FI refs.
    -- We have a different rule, because the reference has a different type
    -- and distinct value.
    LabelOfRef-FS : ∀ {Σ Σ' μ μ' ℓ₁ ℓ₂ ℓ₃ n τ} {e : Expr Γ (Ref S τ)} {r : Raw τ} →
                  ⟨ Σ , μ , e ⟩ ⇓⟨ θ , pc ⟩ ⟨ Σ' , μ' , Refˢ n ^ ℓ₁ ⟩ →
                  n ↦ r ^ ℓ₂ ∈ᴴ μ' →
                  (eq : ℓ₃ ≡ ℓ₁ ⊔ ℓ₂) →
                  Step θ pc ⟨ Σ , μ , labelOfRef e ⟩ ⟨ Σ' , μ' , ⌞ ℓ₂ ⌟ ^ ℓ₃ ⟩

    New-FS : ∀ {τ Σ Σ' μ μ'} {e : Expr Γ τ} {v : Value τ} →
          ⟨ Σ , μ , e ⟩ ⇓⟨ θ , pc ⟩ ⟨ Σ' , μ' , v ⟩ →
          Step θ pc ⟨ Σ , μ , new {s = S} e ⟩  ⟨  Σ' , snocᴴ μ' v , Refˢ ∥ μ' ∥ᴴ ^ pc ⟩

    -- Tainting the result with ℓ ⊔ ℓ' is better than asking ℓ' ⊑ ℓ
    -- and returning the value at pc ⊔ ℓ. The combination pc ⊑ ℓ'
    -- (step-⊑) and ℓ' ⊑ ℓ implies pc ⊑ ℓ, thus the rule would not
    -- allow to read lower references.
    Read-FS : ∀ {Σ Σ' μ μ' ℓ ℓ' ℓ'' n τ r} {e : Expr _ (Ref S τ)}  →
           ⟨ Σ , μ , e ⟩ ⇓⟨ θ , pc ⟩ ⟨ Σ' , μ' , (Refˢ n) ^ ℓ ⟩ →
           n ↦ r ^ ℓ' ∈ᴴ μ' →
           (eq : ℓ'' ≡ ℓ ⊔ ℓ') →
           Step θ pc ⟨ Σ , μ , ! e ⟩  ⟨ Σ' , μ' ,  r ^ ℓ'' ⟩

    Write-FS : ∀ {Σ₁ Σ₂ Σ₃ μ₁ μ₂ μ₃ μ₃' ℓ ℓ₁ ℓ₂ ℓ₂' n τ}
               {e₁ : Expr _ (Ref S τ)} {e₂ : Expr _ τ} {r₁ r₂ : Raw τ} →
             ⟨ Σ₁ , μ₁ , e₁ ⟩ ⇓⟨ θ , pc ⟩ ⟨ Σ₂ , μ₂ , (Refˢ n) ^ ℓ ⟩ →
             ⟨ Σ₂ , μ₂ , e₂ ⟩ ⇓⟨ θ , pc ⟩ ⟨ Σ₃ , μ₃ , r₂ ^ ℓ₂ ⟩ →
             n ↦ r₁ ^ ℓ₁ ∈ᴴ μ₃ →
             ℓ ⊑ ℓ₁ →
             (eq : ℓ₂' ≡ ℓ ⊔ ℓ₂) →
             μ₃' ≔ μ₃ [ n ↦ r₂ ^ ℓ₂' ]ᴴ →
             Step θ pc ⟨ Σ₁ , μ₁ , e₁ ≔ e₂ ⟩ ⟨ Σ₃ , μ₃' , （） ^ pc ⟩

    Id : ∀ {Σ₁ Σ₂ μ₁ μ₂ τ} {e : Expr Γ τ} {v : Value τ} →
            ⟨ Σ₁ , μ₁ , e ⟩ ⇓⟨ θ , pc ⟩ ⟨ Σ₂ , μ₂ , v ⟩ →
            Step θ pc ⟨ Σ₁ , μ₁ , Id e ⟩ ⟨ Σ₂ , μ₂ , Id v ^ pc ⟩

    UnId : ∀ {Σ₁ Σ₂ μ₁ μ₂ τ v ℓ₁ ℓ₂} {e : Expr Γ (Id τ)} →
             ⟨ Σ₁ , μ₁ , e ⟩ ⇓⟨ θ , pc ⟩ ⟨ Σ₂ , μ₂ , Id v ^ ℓ₁ ⟩ →
             let r ^ ℓ' = v in
             (eq : ℓ₂ ≡ ℓ₁ ⊔ ℓ') →
             Step θ pc ⟨ Σ₁ , μ₁ , unId e ⟩ ⟨ Σ₂ , μ₂ , r ^ ℓ₂ ⟩

  -- Pretty syntax
  _⇓⟨_,_⟩_ : ∀ {Γ τ} → IConf Γ τ → Env Γ → Label → FConf τ → Set
  c₁ ⇓⟨ θ , pc ⟩ c₂ = Step θ pc c₁ c₂

--------------------------------------------------------------------------------
-- Shorthands

Wken′ : ∀ {Γ Γ' Σ Σ' μ μ' pc τ v θ} {e : Expr Γ τ} (θ' : Env Γ')
        → ⟨ Σ , μ , e ⟩ ⇓⟨ θ , pc ⟩ ⟨ Σ' , μ' , v ⟩
        → ⟨ Σ , μ , wken e (drop-⊆₂ Γ Γ')  ⟩ ⇓⟨ θ' ++ᴱ θ , pc ⟩ ⟨ Σ' , μ' , v ⟩
Wken′  {Γ' = Γ'} θ'' x = Wken (drop-⊆₂ _ Γ') x

-- Execution under weakening

↑¹-⇓  :  ∀ {Γ Σ Σ' μ μ' pc τ τ' v θ} {e : Expr Γ τ} {v₁ : Value τ'}
        → ⟨ Σ , μ , e ⟩ ⇓⟨ θ , pc ⟩ ⟨ Σ' , μ' , v ⟩
        → ⟨ Σ , μ , e ↑¹ ⟩ ⇓⟨ v₁ ∷  θ , pc ⟩ ⟨ Σ' , μ' , v ⟩
↑¹-⇓ {v₁ = v₁}  = Wken′ (v₁ ∷ [])

↑²-⇓  :  ∀ {Γ Σ Σ' μ μ' pc τ τ₁ τ₂ v θ} {e : Expr Γ τ} {v₁ : Value τ₁} {v₂ : Value τ₂}
        → ⟨ Σ , μ , e ⟩ ⇓⟨ θ , pc ⟩ ⟨ Σ' , μ' , v ⟩
        → ⟨ Σ , μ , e ↑² ⟩ ⇓⟨ v₁ ∷ v₂ ∷ θ , pc ⟩ ⟨ Σ' , μ' , v ⟩
↑²-⇓ {v₁ = v₁} {v₂ = v₂} = Wken′ (v₁ ∷ v₂ ∷ [])

⇓-with : ∀ {τ Γ c₂ c₂' θ pc} {c₁ : IConf Γ τ} → c₁ ⇓⟨ θ , pc ⟩ c₂ → c₂ ≡ c₂' → c₁ ⇓⟨ θ , pc ⟩ c₂'
⇓-with x refl = x

--------------------------------------------------------------------------------

open Value
open import Data.Product using ( proj₁ ; proj₂ )
open import Relation.Binary.PropositionalEquality

-- The result of the value is at least as senstive as the program
-- counter.
step-⊑ : ∀ {Σ Σ' μ μ' Γ τ pc} {e : Expr Γ τ} {v : Value τ} {θ : Env Γ} →
             ⟨ Σ , μ , e ⟩ ⇓⟨ θ , pc ⟩ ⟨ Σ' , μ' , v ⟩ →
             pc ⊑ (lbl v)

step-⊑ {pc = pc} {θ = θ} (Var τ∈Γ eq) rewrite eq = join-⊑₁ pc (lbl (θ !! τ∈Γ))
step-⊑ Unit = refl-⊑
step-⊑ (Lbl ℓ) = refl-⊑
step-⊑ (Test₁ x x₁ x₂ refl) = trans-⊑ (step-⊑ x₁) (join-⊑₂ _ _)
step-⊑ (Test₂ x x₁ x₂ refl) = trans-⊑ (step-⊑ x₁) (join-⊑₂ _ _)
step-⊑ Fun = refl-⊑
step-⊑ (App x x₁ eq x₂) rewrite eq = proj₁ (unjoin-⊑ (step-⊑ x₂))
step-⊑ (Inl x) = refl-⊑
step-⊑ (Inr x) = refl-⊑
step-⊑ (Case₁ x eq x₁) rewrite eq = proj₁ (unjoin-⊑ (step-⊑ x₁))
step-⊑ (Case₂ x eq x₁) rewrite eq =  proj₁ (unjoin-⊑ (step-⊑ x₁))
step-⊑ (Pair x x₁) = refl-⊑
step-⊑ (Fst x eq) rewrite eq = trans-⊑ (step-⊑ x) (join-⊑₁ _ _)
step-⊑ (Snd x eq) rewrite eq = trans-⊑ (step-⊑ x) (join-⊑₁ _ _)
step-⊑ (LabelOf x) = step-⊑ x
step-⊑ GetLabel = refl-⊑
step-⊑ (Wken p x) = step-⊑ x
step-⊑ {pc = pc} (Taint {ℓ = ℓ} refl x₁ x₂ _) = trans-⊑ (join-⊑₁ pc ℓ ) (step-⊑ x₂)
step-⊑ (LabelOfRef x refl) = trans-⊑ (step-⊑ x) (join-⊑₂ _ _)
step-⊑ (New x) = refl-⊑
step-⊑ {pc = pc} (Read {ℓ = ℓ} {ℓ' = ℓ'} x x₁ refl) = trans-⊑ {pc} {ℓ'} {ℓ ⊔ ℓ'} (step-⊑ x) (join-⊑₂ ℓ' ℓ)
step-⊑ (Write x x₁ eq x₂ x₃) = refl-⊑
step-⊑ (LabelOfRef-FS x x₁ refl) = trans-⊑ (step-⊑ x) (join-⊑₁ _ _)
step-⊑ (New-FS x) = refl-⊑
step-⊑ (Read-FS x x₁ refl) = trans-⊑ (step-⊑ x) (join-⊑₁ _ _)
step-⊑ (Write-FS x x₁ x₂ x₃ eq x₄) = refl-⊑
step-⊑ (Id x) = refl-⊑
step-⊑ (UnId x eq) rewrite eq = trans-⊑ (step-⊑ x) (join-⊑₁ _ _)
