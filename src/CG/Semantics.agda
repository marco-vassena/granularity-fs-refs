-- Big-step semantics.

open import Lattice

module CG.Semantics {{𝑳 : Lattice}} where

open import CG.Types
open import CG.Syntax
open import Relation.Binary.PropositionalEquality
open import Data.Product hiding (_×_) renaming (_,_ to _^_)

mutual

  -- Pure big-step semantics of the core of CG
  --
  -- This definition expects a suitable mapping environment (θ : Env
  -- Γ) that binds all the free variables in the expression (Expr Γ τ)
  -- and ensures type preservation by construction (same type τ in
  -- Expr and Value).
  data PStep {Γ} (θ : Env Γ) : ∀ {τ} → Expr Γ τ → Value τ → Set where

    Unit : PStep θ （） （）

    Lbl : (ℓ : Label) → PStep θ  ⌞ ℓ ⌟  ⌞ ℓ ⌟

    Test₁ : ∀ {e₁ e₂ ℓ₁ ℓ₂} →
              e₁ ⇓ᴾ⟨ θ ⟩ ⌞ ℓ₁ ⌟ →
              e₂ ⇓ᴾ⟨ θ ⟩ ⌞ ℓ₂ ⌟ →
              ℓ₁ ⊑ ℓ₂ →
              PStep θ (e₁ ⊑-? e₂) true

    Test₂ : ∀ {e₁ e₂ ℓ₁ ℓ₂} →
              e₁ ⇓ᴾ⟨ θ ⟩ ⌞ ℓ₁ ⌟ →
              e₂ ⇓ᴾ⟨ θ ⟩ ⌞ ℓ₂ ⌟ →
              ℓ₁ ⋤ ℓ₂ →
              PStep θ (e₁ ⊑-? e₂) false

    Wken : ∀ {τ Γ'} {e : Expr Γ' τ} {v : Value τ} →
           (p : Γ' ⊆ Γ) →
           e ⇓ᴾ⟨ slice θ p ⟩ v →
           PStep θ (wken e p) v

    Var : ∀ {τ} (τ∈Γ : τ ∈ Γ) → PStep θ (var τ∈Γ) (θ !! τ∈Γ)

    SThunk : ∀ {τ} {t : Thunk Γ (LIO τ)} → PStep θ ⌞ t ⌟ᵀ ⟨ t , θ ⟩ᵀ

    Fun : ∀ {τ₁ τ₂} {e : Expr (τ₁ ∷ Γ) τ₂} → PStep θ (Λ e) ⟨ e , θ ⟩ᶜ

    App : ∀ {τ₁ τ₂ Γ'} {θ' : Env Γ'} {e₁ : Expr Γ (τ₁ ➔ τ₂)} {e₂ : Expr Γ τ₁}
            {e : Expr (τ₁ ∷ Γ') τ₂} {v₂ : Value τ₁} {v : Value τ₂} →
            e₁ ⇓ᴾ⟨ θ ⟩ ⟨ e , θ' ⟩ᶜ
          → e₂ ⇓ᴾ⟨ θ ⟩ v₂
          → e ⇓ᴾ⟨ v₂ ∷ θ' ⟩ v
          → PStep θ (e₁ ∘ e₂) v

    Inl : ∀ {τ₁ τ₂} {e : Expr Γ τ₁} {v : Value τ₁} →
            e ⇓ᴾ⟨ θ ⟩ v →
            PStep θ (inl {τ₂ = τ₂} e) (inl v)

    Inr : ∀ {τ₁ τ₂} {e : Expr Γ τ₂} {v : Value τ₂} →
          e ⇓ᴾ⟨ θ ⟩ v →
          PStep θ (inr {τ₁ = τ₁} e) (inr v)

    Case₁ : ∀ {τ τ₁ τ₂} {e : Expr Γ (τ₁ + τ₂)} {e₁ : Expr _ τ} {e₂ : Expr _ τ}
              {v : Value τ} {v₁ : Value τ₁} →
            e ⇓ᴾ⟨ θ ⟩ (inl v₁) →
            e₁ ⇓ᴾ⟨ v₁ ∷ θ ⟩ v →
            PStep θ (case e e₁ e₂) v

    Case₂ : ∀ {τ τ₁ τ₂} {e : Expr Γ (τ₁ + τ₂)} {e₁ : Expr _ τ} {e₂ : Expr _ τ}
              {v : Value τ} {v₂ : Value τ₂} →
            e ⇓ᴾ⟨ θ ⟩ (inr v₂) →
            e₂ ⇓ᴾ⟨ v₂ ∷ θ ⟩ v  →
            PStep θ (case e e₁ e₂) v

    Pair : ∀ {τ₁ τ₂} {e₁ : Expr Γ τ₁} {e₂ : Expr Γ τ₂} {v₁ : Value τ₁} {v₂ : Value τ₂} →
           e₁ ⇓ᴾ⟨ θ ⟩ v₁ →
           e₂ ⇓ᴾ⟨ θ ⟩ v₂ →
           PStep θ ⟨ e₁ , e₂ ⟩ ⟨ v₁ , v₂ ⟩

    Fst : ∀ {τ₁ τ₂} {e : Expr _ (τ₁ × τ₂)} {v₁ : Value τ₁} {v₂ : Value τ₂} →
            e ⇓ᴾ⟨ θ ⟩ ⟨ v₁ , v₂ ⟩ → PStep θ (fst e) v₁

    Snd : ∀ {τ₁ τ₂} {e : Expr _ (τ₁ × τ₂)} {v₁ : Value τ₁} {v₂ : Value τ₂} →
            e ⇓ᴾ⟨ θ ⟩ ⟨ v₁ , v₂ ⟩ → PStep θ (snd e) v₂

  -- Pretty Syntax
  _⇓ᴾ⟨_⟩_ : ∀ {τ Γ} → Expr Γ τ → Env Γ → Value τ → Set
  e ⇓ᴾ⟨ θ ⟩ v = PStep θ e v

  infixr 3 _⇓ᴾ⟨_⟩_

mutual

  -- Thunk semantics for LIO computations.
  data Step {Γ} (θ : Env Γ) : ∀ {τ} → TConf Γ (LIO τ) → FConf τ → Set where

    Return : ∀ {Σ μ pc τ} {e : Expr _ τ} {v : Value τ} →
               e ⇓ᴾ⟨ θ ⟩ v →
               Step θ ⟨ Σ , μ , pc , return e ⟩ ⟨ Σ , μ , pc , v ⟩

    Bind : ∀ {Σ Σ' Σ'' μ μ' μ'' pc pc' pc'' τ₁ τ₂ v v₁} {e₁ : Expr Γ (LIO τ₁)} {e₂ : Expr (τ₁ ∷ Γ) (LIO τ₂)}
           → ⟨ Σ , μ , pc , e₁ ⟩ ⇓ᶠ⟨ θ ⟩ ⟨ Σ' , μ' , pc' , v₁ ⟩
           → ⟨ Σ' , μ' , pc' , e₂ ⟩ ⇓ᶠ⟨ v₁ ∷ θ ⟩  ⟨ Σ'' , μ'' , pc'' , v ⟩
           → Step θ ⟨ Σ , μ , pc , bind e₁ e₂ ⟩ ⟨ Σ'' , μ'' , pc'' , v ⟩

    Unlabel : ∀ {Σ μ pc ℓ ℓ' τ} {e : Expr _ (Labeled τ)} {v : Value τ} →
              e ⇓ᴾ⟨ θ ⟩ Labeled ℓ v →
              (eq : ℓ' ≡ pc ⊔ ℓ) →
              Step θ ⟨ Σ , μ , pc , (unlabel e) ⟩ ⟨ Σ , μ , ℓ' , v ⟩

    ToLabeled : ∀ {Σ Σ' μ μ' pc pc' τ v } {e : Expr _ (LIO τ)}
                → ⟨ Σ , μ , pc , e ⟩ ⇓ᶠ⟨ θ ⟩ ⟨ Σ' , μ' , pc' , v ⟩
                → Step θ ⟨ Σ , μ , pc , toLabeled e ⟩  ⟨ Σ' , μ' , pc , Labeled pc' v ⟩

    LabelOf : ∀ {Σ μ pc ℓ ℓ' τ} {e : Expr _ (Labeled τ)} {v : Value τ} →
                e ⇓ᴾ⟨ θ ⟩ Labeled ℓ v →
                ℓ' ≡ pc ⊔ ℓ →
                Step θ ⟨ Σ , μ , pc , labelOf e ⟩ ⟨ Σ , μ , ℓ' , ⌞ ℓ ⌟ ⟩

    GetLabel : ∀ {Σ μ pc} → Step θ ⟨ Σ , μ , pc , getLabel ⟩ ⟨ Σ , μ , pc , ⌞ pc ⌟ ⟩

    Taint : ∀ {Σ μ pc pc' ℓ} {e : Expr _ 𝓛} →
              e ⇓ᴾ⟨ θ ⟩ ⌞ ℓ ⌟ →
              pc' ≡ pc ⊔ ℓ →
              Step θ ⟨ Σ , μ , pc , (taint e) ⟩ ⟨ Σ , μ , pc'  , （） ⟩

  --------------------------------------------------------------------------------
  -- Flow Insensitive references

    New : ∀ {Σ μ pc ℓ τ} {e : Expr Γ _} {v : Value τ} →
          e ⇓ᴾ⟨ θ ⟩ (Labeled ℓ v) →
          pc ⊑ ℓ →
          let M = Σ ℓ in
          Step θ ⟨ Σ , μ , pc , new e ⟩  ⟨ Σ [ ℓ ↦ snocᴹ M v ]ˢ , μ , pc , Refᴵ ℓ ∥ M ∥ᴹ ⟩

    Read : ∀ {Σ μ pc ℓ pc' n τ} {e : Expr _ (Ref I τ)} {v : Value τ } →
           e ⇓ᴾ⟨ θ ⟩ Refᴵ ℓ n →
           (n∈M : n ↦ v ∈ᴹ (Σ ℓ)) →
           (eq : pc' ≡ pc ⊔ ℓ) →
           Step θ ⟨ Σ , μ , pc , ! e ⟩  ⟨ Σ , μ , pc' , v ⟩

    Write : ∀ {Σ μ pc ℓ ℓ' n τ} {M' : Memory ℓ} {e₁ : Expr _ (Ref I τ)} {e₂ : Expr _ (Labeled τ)} {v₂ : Value τ} →
             e₁ ⇓ᴾ⟨ θ ⟩ Refᴵ ℓ n →
             e₂ ⇓ᴾ⟨ θ ⟩ Labeled ℓ' v₂ →
             pc ⊑ ℓ →
             ℓ' ⊑ ℓ →
             (up : M' ≔ (Σ ℓ) [ n ↦ v₂ ]ᴹ) →
             Step θ ⟨ Σ , μ , pc , e₁ ≔ e₂ ⟩ ⟨ Σ [ ℓ ↦ M' ]ˢ , μ , pc , （） ⟩

    -- LabelOfRef does not raise the program counter because the
    -- reference is flow-insensitive (the label on the ref does not
    -- change).
    LabelOfRef : ∀ {Σ μ ℓ pc pc' n τ} {e : Expr _ (Ref I τ)} →
                 e ⇓ᴾ⟨ θ ⟩ Refᴵ ℓ n →
                 (eq : pc' ≡ pc ⊔ ℓ) →
                 Step θ ⟨ Σ , μ , pc , labelOfRef e ⟩ ⟨ Σ , μ , pc' , ⌞ ℓ ⌟ ⟩

  --------------------------------------------------------------------------------
  -- Flow Sensitive references

    New-FS : ∀ {Σ μ pc ℓ τ} {e : Expr Γ _} {v : Value τ} →
             e ⇓ᴾ⟨ θ ⟩ (Labeled ℓ v) →
             pc ⊑ ℓ →
             Step θ ⟨ Σ , μ , pc , new e ⟩  ⟨ Σ , snocᴴ μ (v ^ ℓ) , pc , Refˢ ∥ μ ∥ᴴ ⟩

    Read-FS : ∀ {Σ μ pc ℓ pc' n τ} {e : Expr _ (Ref S τ)} {v : Value τ} →
              e ⇓ᴾ⟨ θ ⟩ Refˢ n →
              (n∈μ : n ↦ v ^ ℓ ∈ᴴ μ) →
              (eq : pc' ≡ pc ⊔ ℓ) →
              Step θ ⟨ Σ , μ , pc , ! e ⟩  ⟨ Σ , μ , pc' , v ⟩

    Write-FS : ∀ {Σ μ μ' pc ℓ ℓ' ℓ'' n τ} {e₁ : Expr _ (Ref S τ)}
                 {e₂ : Expr _ (Labeled τ)} {v₂ v₂' : Value τ} →
             e₁ ⇓ᴾ⟨ θ ⟩ Refˢ n →
             e₂ ⇓ᴾ⟨ θ ⟩ Labeled ℓ' v₂ →
             (n∈μ : n ↦ v₂' ^ ℓ ∈ᴴ μ) →
             pc ⊑ ℓ →
             (ℓ'' ≡ pc ⊔ ℓ') →
             (up : μ' ≔ μ [ n ↦ v₂ ^ ℓ'' ]ᴴ) →
             Step θ ⟨ Σ , μ , pc , e₁ ≔ e₂ ⟩ ⟨ Σ , μ' , pc , （） ⟩

    LabelOfRef-FS : ∀ {Σ μ ℓ pc pc' n τ} {e : Expr _ (Ref S τ)} {v : Value τ} →
                    e ⇓ᴾ⟨ θ ⟩ Refˢ n →
                    (n∈μ : n ↦ v ^ ℓ ∈ᴴ μ) →
                    (eq : pc' ≡ pc ⊔ ℓ) →
                    Step θ ⟨ Σ , μ , pc , labelOfRef e ⟩ ⟨ Σ , μ , pc' , ⌞ ℓ ⌟ ⟩


  -- Pretty syntax.
  _⇓⟨_⟩_ : ∀ {Γ τ} → TConf Γ (LIO τ) → Env Γ → FConf τ → Set
  c₁ ⇓⟨ θ ⟩ c₂ = Step θ c₁ c₂


  -- Forcing semantics for monadic expressions.
  data FStep {Γ} (θ : Env Γ) : ∀ {τ} → EConf Γ (LIO τ) → FConf τ → Set where
    Force : ∀ {τ Γ' pc pc' Σ Σ' μ μ' v e} {t : Thunk Γ' (LIO τ)} {θ' : Env Γ'}
            → e ⇓ᴾ⟨ θ ⟩ ⟨ t , θ' ⟩ᵀ
            → ⟨ Σ , μ , pc , t ⟩ ⇓⟨ θ' ⟩ ⟨ Σ' , μ' , pc' , v ⟩
            → FStep θ ⟨ Σ , μ , pc , e ⟩ ⟨ Σ' , μ' , pc' , v ⟩

  _⇓ᶠ⟨_⟩_ : ∀ {Γ τ} → EConf Γ (LIO τ) → Env Γ → FConf τ → Set
  c₁ ⇓ᶠ⟨ θ ⟩ c₂ = FStep θ c₁ c₂

--------------------------------------------------------------------------------
-- The semantics only raises the program counter.

open Conf

mutual

  step-⊑ : ∀ {τ Γ c₂} {θ : Env Γ} {c₁ : TConf Γ (LIO τ)} →
             c₁ ⇓⟨ θ ⟩ c₂ →
             (pc c₁) ⊑ (pc c₂)
  step-⊑ (Return x) = refl-⊑
  step-⊑ (Bind x x₁) = trans-⊑ (stepᶠ-⊑ x) (stepᶠ-⊑ x₁)
  step-⊑ (Unlabel x eq) rewrite eq = join-⊑₁ _ _
  step-⊑ (ToLabeled x) = refl-⊑
  step-⊑ (LabelOf x eq) rewrite eq = join-⊑₁ _ _
  step-⊑ GetLabel = refl-⊑
  step-⊑ (Taint x₁ refl) = join-⊑₁ _ _
  step-⊑ (New a b) = refl-⊑
  step-⊑ (Read x u refl) = join-⊑₁ _ _
  step-⊑ (Write x _ x₁ _ _) = refl-⊑
  step-⊑ (LabelOfRef x refl) = join-⊑₁ _ _
  step-⊑ (New-FS x x₁) = refl-⊑
  step-⊑ (Read-FS x n∈μ refl) = join-⊑₁ _ _
  step-⊑ (Write-FS x x₁ n∈μ x₂ eq up) = refl-⊑
  step-⊑ (LabelOfRef-FS x n∈μ refl) = join-⊑₁ _ _

  stepᶠ-⊑ : ∀ {τ Γ c₂} {θ : Env Γ} {c₁ : EConf Γ (LIO τ)} →
              c₁ ⇓ᶠ⟨ θ ⟩ c₂ →
              (pc c₁) ⊑ (pc c₂)

  stepᶠ-⊑ (Force x x₁) = step-⊑ x₁
