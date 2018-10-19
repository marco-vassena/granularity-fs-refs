-- Big-step semantics.

open import Lattice

module CG.Semantics {{𝑳 : Lattice}} where

open import CG.Types
open import CG.Syntax
open import Relation.Binary.PropositionalEquality

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

    Return : ∀ {Σ pc τ} {e : Expr _ τ} {v : Value τ} →
               e ⇓ᴾ⟨ θ ⟩ v →
               Step θ ⟨ Σ , pc , return e ⟩ ⟨ Σ , pc , v ⟩

    Bind : ∀ {Σ Σ' Σ'' pc pc' pc'' τ₁ τ₂ v v₁} {e₁ : Expr Γ (LIO τ₁)} {e₂ : Expr (τ₁ ∷ Γ) (LIO τ₂)}
           → ⟨ Σ , pc , e₁ ⟩ ⇓ᶠ⟨ θ ⟩ ⟨ Σ' , pc' , v₁ ⟩
           → ⟨ Σ' , pc' , e₂ ⟩ ⇓ᶠ⟨ v₁ ∷ θ ⟩  ⟨ Σ'' , pc'' , v ⟩
           → Step θ ⟨ Σ , pc , bind e₁ e₂ ⟩ ⟨ Σ'' , pc'' , v ⟩

    Unlabel : ∀ {Σ pc ℓ ℓ' τ} {e : Expr _ (Labeled τ)} {v : Value τ} →
              e ⇓ᴾ⟨ θ ⟩ Labeled ℓ v →
              (eq : ℓ' ≡ pc ⊔ ℓ) →
              Step θ ⟨ Σ , pc , (unlabel e) ⟩ ⟨ Σ , ℓ' , v ⟩

    ToLabeled : ∀ {Σ Σ' pc pc' τ v } {e : Expr _ (LIO τ)}
                → ⟨ Σ , pc , e ⟩ ⇓ᶠ⟨ θ ⟩ ⟨ Σ' , pc' , v ⟩
                → Step θ ⟨ Σ , pc , toLabeled e ⟩  ⟨ Σ' , pc , Labeled pc' v ⟩

    LabelOf : ∀ {Σ pc ℓ ℓ' τ} {e : Expr _ (Labeled τ)} {v : Value τ} →
                e ⇓ᴾ⟨ θ ⟩ Labeled ℓ v →
                ℓ' ≡ pc ⊔ ℓ →
                Step θ ⟨ Σ , pc , labelOf e ⟩ ⟨ Σ , ℓ' , ⌞ ℓ ⌟ ⟩

    GetLabel : ∀ {Σ pc} → Step θ ⟨ Σ , pc , getLabel ⟩ ⟨ Σ , pc , ⌞ pc ⌟ ⟩

    Taint : ∀ {Σ pc pc' ℓ} {e : Expr _ 𝓛} →
              e ⇓ᴾ⟨ θ ⟩ ⌞ ℓ ⌟ →
              pc' ≡ pc ⊔ ℓ →
              Step θ ⟨ Σ , pc , (taint e) ⟩ ⟨ Σ , pc'  , （） ⟩

    New : ∀ {Σ pc ℓ τ} {e : Expr Γ _} {v : Value τ} →
          e ⇓ᴾ⟨ θ ⟩ (Labeled ℓ v) →
          pc ⊑ ℓ →
          let M = Σ ℓ in
          Step θ ⟨ Σ , pc , new e ⟩  ⟨ Σ [ ℓ ↦ M ∷ᴿ v ]ˢ  , pc , Ref ℓ ∥ M ∥ ⟩

    Read : ∀ {Σ pc ℓ pc' n τ} {e : Expr _ (Ref τ)} {v : Value τ } →
           e ⇓ᴾ⟨ θ ⟩ Ref ℓ n →
           (n∈M : n ↦ v ∈ᴹ (Σ ℓ)) →
           (eq : pc' ≡ pc ⊔ ℓ) →
           Step θ ⟨ Σ , pc , ! e ⟩  ⟨ Σ , pc' , v ⟩

    Write : ∀ {Σ pc ℓ ℓ' n τ} {M' : Memory ℓ} {e₁ : Expr _ (Ref τ)} {e₂ : Expr _ (Labeled τ)} {v₂ : Value τ} →
             e₁ ⇓ᴾ⟨ θ ⟩ Ref ℓ n →
             e₂ ⇓ᴾ⟨ θ ⟩ Labeled ℓ' v₂ →
             pc ⊑ ℓ →
             ℓ' ⊑ ℓ →
             (up : M' ≔ (Σ ℓ) [ n ↦ v₂ ]ᴹ) →
             Step θ ⟨ Σ , pc , e₁ ≔ e₂ ⟩ ⟨ Σ [ ℓ ↦ M' ]ˢ , pc , （） ⟩

    -- LabelOfRef does not raise the program counter because the
    -- reference is flow-insensitive (the label on the ref does not
    -- change).
    LabelOfRef : ∀ {Σ ℓ pc pc' n τ} {e : Expr _ (Ref τ)} →
                 e ⇓ᴾ⟨ θ ⟩ Ref ℓ n →
                 (eq : pc' ≡ pc ⊔ ℓ) →
                 Step θ ⟨ Σ , pc , labelOfRef e ⟩ ⟨ Σ , pc' , ⌞ ℓ ⌟ ⟩

  -- Pretty syntax.
  _⇓⟨_⟩_ : ∀ {Γ τ} → TConf Γ (LIO τ) → Env Γ → FConf τ → Set
  c₁ ⇓⟨ θ ⟩ c₂ = Step θ c₁ c₂


  -- Forcing semantics for monadic expressions.
  data FStep {Γ} (θ : Env Γ) : ∀ {τ} → EConf Γ (LIO τ) → FConf τ → Set where
    Force : ∀ {τ Γ' pc pc' Σ Σ' v e} {t : Thunk Γ' (LIO τ)} {θ' : Env Γ'}
            → e ⇓ᴾ⟨ θ ⟩ ⟨ t , θ' ⟩ᵀ
            → ⟨ Σ , pc , t ⟩ ⇓⟨ θ' ⟩ ⟨ Σ' , pc' , v ⟩
            → FStep θ ⟨ Σ , pc , e ⟩ ⟨ Σ' , pc' , v ⟩

  _⇓ᶠ⟨_⟩_ : ∀ {Γ τ} → EConf Γ (LIO τ) → Env Γ → FConf τ → Set
  c₁ ⇓ᶠ⟨ θ ⟩ c₂ = FStep θ c₁ c₂

--------------------------------------------------------------------------------
-- Syntactic sugar

-- Force a thunk
⌞_⌟ᶠ : ∀ {τ Γ Σ Σ' pc pc' v} {t : Thunk Γ (LIO τ)} {θ : Env Γ}
        → ⟨ Σ , pc , t ⟩ ⇓⟨ θ ⟩ ⟨ Σ' , pc' , v ⟩
        → ⟨ Σ , pc , ⌞ t ⌟ᵀ ⟩ ⇓ᶠ⟨ θ ⟩ ⟨ Σ' , pc' , v ⟩
⌞_⌟ᶠ = Force SThunk

-- Force bind.
Bindᶠ : ∀ {Γ τ₁ τ₂ Σ Σ' Σ'' pc pc' pc'' v v₁ θ} {e₁ : Expr Γ (LIO τ₁)} {e₂ : Expr _ (LIO τ₂)}
           → ⟨ Σ , pc , e₁ ⟩ ⇓ᶠ⟨ θ ⟩ ⟨ Σ' , pc' , v₁ ⟩
           → ⟨ Σ' , pc' , e₂ ⟩ ⇓ᶠ⟨ v₁ ∷ θ ⟩ ⟨ Σ'' , pc'' , v ⟩
           → ⟨ Σ , pc , ⌞ bind e₁ e₂ ⌟ᵀ ⟩ ⇓ᶠ⟨ θ ⟩ ⟨ Σ'' , pc'' , v ⟩
Bindᶠ x₁ x₂ = ⌞ Bind x₁ x₂ ⌟ᶠ

-- To labeled in forcing semantics
ToLabeledᶠ  : ∀ {Γ Σ Σ' pc pc' τ v θ} {t : Thunk Γ (LIO τ)}
              → ⟨ Σ , pc , ⌞ t ⌟ᵀ ⟩ ⇓ᶠ⟨ θ ⟩ ⟨ Σ' , pc' , v ⟩
              → ⟨ Σ , pc , ⌞ toLabeled ⌞ t ⌟ᵀ ⌟ᵀ ⟩ ⇓ᶠ⟨ θ ⟩ ⟨ Σ' , pc , Labeled pc' v ⟩
ToLabeledᶠ x = ⌞ ToLabeled x ⌟ᶠ

-- Force Wken
Wkenᶠ : ∀ {Γ Γ' Σ Σ' pc pc' τ v θ} {e : Expr Γ (LIO τ)} (θ' : Env Γ')
        → ⟨ Σ , pc , e ⟩ ⇓ᶠ⟨ θ ⟩ ⟨ Σ' , pc' , v ⟩
        → ⟨ Σ , pc , wken e (drop-⊆₂ Γ Γ')  ⟩ ⇓ᶠ⟨ θ' ++ᴱ θ ⟩ ⟨ Σ' , pc' , v ⟩
Wkenᶠ {Γ' = Γ'} θ'' (Force x x₁) = Force (Wken (drop-⊆₂ _ Γ') x) x₁

-- Pure execution under weakening
⇓¹ : ∀ {Γ τ τ₁ v θ} {v₁ : Value τ₁} {e : Expr Γ τ}
     → e ⇓ᴾ⟨ θ ⟩ v
     → e ↑¹ ⇓ᴾ⟨ v₁ ∷ θ ⟩ v
⇓¹ x = Wken (drop refl-⊆) x


⇓² : ∀ {Γ τ τ₁ τ₂ v θ} {v₁ : Value τ₁} {v₂ : Value τ₂} {e : Expr Γ τ}
     → e ⇓ᴾ⟨ θ ⟩ v
     → e ↑² ⇓ᴾ⟨ v₁ ∷ v₂ ∷ θ ⟩ v
⇓² x = Wken (drop (drop refl-⊆)) x

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

↑¹-⇓ᶠ  :  ∀ {Γ  Σ Σ' pc pc' τ τ' v θ} {e : Expr Γ (LIO τ)} {v₁ : Value τ'}
        → ⟨ Σ , pc , e ⟩ ⇓ᶠ⟨ θ ⟩ ⟨ Σ' , pc' , v ⟩
        → ⟨ Σ , pc , e ↑¹ ⟩ ⇓ᶠ⟨ v₁ ∷  θ ⟩ ⟨ Σ' , pc' , v ⟩
↑¹-⇓ᶠ {v₁ = v₁}  = Wkenᶠ (v₁ ∷ [])

↑²-⇓ᶠ  :  ∀ {Γ  Σ Σ' pc pc' τ τ₁ τ₂ v θ} {e : Expr Γ (LIO τ)} {v₁ : Value τ₁} {v₂ : Value τ₂}
        → ⟨ Σ , pc , e ⟩ ⇓ᶠ⟨ θ ⟩ ⟨ Σ' , pc' , v ⟩
        → ⟨ Σ , pc , e ↑² ⟩ ⇓ᶠ⟨ v₁ ∷ v₂ ∷  θ ⟩ ⟨ Σ' , pc' , v ⟩
↑²-⇓ᶠ {v₁ = v₁} {v₂ = v₂} = Wkenᶠ (v₁ ∷ v₂ ∷ [])

⇓ᴾ-with : ∀ {τ Γ v₁ v₂ θ} {e : Expr Γ τ} → e ⇓ᴾ⟨ θ ⟩ v₁ → v₁ ≡ v₂ → e ⇓ᴾ⟨ θ ⟩ v₂
⇓ᴾ-with x refl = x

⇓ᶠ-with : ∀ {τ Γ Σ Σ' pc pc' v₁ v₂ θ} {e : Expr Γ (LIO τ)} →
            ⟨ Σ , pc , e ⟩ ⇓ᶠ⟨ θ ⟩ ⟨ Σ' , pc' , v₁ ⟩ →
            v₁ ≡ v₂ → ⟨ Σ , pc , e ⟩ ⇓ᶠ⟨ θ ⟩ ⟨ Σ' , pc' , v₂ ⟩
⇓ᶠ-with x refl = x

⇓-with : ∀ {τ Γ Σ Σ' pc pc' v₁ v₂ θ} {t : Thunk Γ (LIO τ)} →
            ⟨ Σ , pc , t ⟩ ⇓⟨ θ ⟩ ⟨ Σ' , pc' , v₁ ⟩ →
            v₁ ≡ v₂ → ⟨ Σ , pc , t ⟩ ⇓⟨ θ ⟩ ⟨ Σ' , pc' , v₂ ⟩
⇓-with x refl = x

⇓-with′ : ∀ {τ Γ Σ pc c₁ c₂ θ} {t : Thunk Γ (LIO τ)} →
            ⟨ Σ , pc , t ⟩ ⇓⟨ θ ⟩ c₁ →
            c₁ ≡ c₂ → ⟨ Σ , pc , t ⟩ ⇓⟨ θ ⟩ c₂
⇓-with′ x refl = x

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

  stepᶠ-⊑ : ∀ {τ Γ c₂} {θ : Env Γ} {c₁ : EConf Γ (LIO τ)} →
              c₁ ⇓ᶠ⟨ θ ⟩ c₂ →
              (pc c₁) ⊑ (pc c₂)

  stepᶠ-⊑ (Force x x₁) = step-⊑ x₁
