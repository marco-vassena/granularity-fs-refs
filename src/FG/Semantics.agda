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

    Var : ∀ {Σ τ ℓ'} (τ∈Γ : τ ∈ Γ) →
          let v ^ ℓ = (θ !! τ∈Γ) in
          ℓ' ≡ (pc ⊔ ℓ) →
          Step θ pc ⟨ Σ , var τ∈Γ ⟩ ⟨ Σ , v ^ ℓ' ⟩

    Unit : ∀ {Σ} → Step θ pc ⟨ Σ , （） ⟩ ⟨ Σ , （） ^ pc ⟩

    Lbl : ∀ {Σ} (ℓ : Label) → Step θ pc ⟨ Σ , ⌞ ℓ ⌟ ⟩ ⟨ Σ , ⌞ ℓ ⌟ ^ pc ⟩

    Test₁ : ∀ {Σ₁ Σ₂ Σ₃ e₁ e₂ ℓ ℓ₁ ℓ₁' ℓ₂ ℓ₂'} →
              ⟨ Σ₁ , e₁ ⟩ ⇓⟨ θ , pc ⟩ ⟨ Σ₂ , ⌞ ℓ₁ ⌟ ^ ℓ₁' ⟩ →
              ⟨ Σ₂ , e₂ ⟩ ⇓⟨ θ , pc ⟩ ⟨ Σ₃ , ⌞ ℓ₂ ⌟ ^ ℓ₂' ⟩ →
              ℓ₁ ⊑ ℓ₂ →
              ℓ ≡ ℓ₁' ⊔ ℓ₂' →
              Step θ pc ⟨ Σ₁ , e₁ ⊑-? e₂ ⟩ ⟨ Σ₃ , true pc ^ ℓ ⟩

    Test₂ : ∀ {Σ₁ Σ₂ Σ₃ e₁ e₂ ℓ ℓ₁ ℓ₁' ℓ₂ ℓ₂'} →
              ⟨ Σ₁ , e₁ ⟩ ⇓⟨ θ , pc ⟩ ⟨ Σ₂ , ⌞ ℓ₁ ⌟ ^ ℓ₁' ⟩ →
              ⟨ Σ₂ , e₂ ⟩ ⇓⟨ θ , pc ⟩ ⟨ Σ₃ , ⌞ ℓ₂ ⌟ ^ ℓ₂' ⟩ →
              ℓ₁ ⋤ ℓ₂ →
              ℓ ≡ ℓ₁' ⊔ ℓ₂' →
              Step θ pc ⟨ Σ₁ , e₁ ⊑-? e₂ ⟩ ⟨ Σ₃ , false pc ^ ℓ ⟩

    Fun : ∀ {Σ τ₁ τ₂} {e : Expr (τ₁ ∷ Γ) τ₂}  → Step θ pc ⟨ Σ , Λ e ⟩ ⟨ Σ , ⟨ e , θ ⟩ᶜ ^ pc ⟩

    App : ∀ {Σ Σ' Σ'' Σ''' Γ' θ' ℓ ℓ' τ₁ τ₂} {e₁ : Expr Γ (τ₁ ➔ τ₂)} {e : Expr (τ₁ ∷ Γ') τ₂} →
             {e₂ : Expr _ τ₁} {v₂ : Value τ₁} {v : Value τ₂} →
             ⟨ Σ , e₁ ⟩ ⇓⟨ θ , pc ⟩ ⟨ Σ' , ⟨ e , θ' ⟩ᶜ ^ ℓ ⟩ →
             ⟨ Σ'  , e₂ ⟩ ⇓⟨ θ , pc ⟩ ⟨ Σ'' , v₂ ⟩ →
             ℓ' ≡ pc ⊔ ℓ →
             ⟨ Σ'' , e ⟩ ⇓⟨ v₂ ∷ θ' , ℓ' ⟩ ⟨ Σ''' , v ⟩ →
             Step θ pc ⟨ Σ , e₁ ∘ e₂ ⟩ ⟨ Σ''' , v ⟩

    Wken : ∀ {Σ Σ' τ Γ'} {e : Expr Γ' τ} {v : Value τ} →
           (p : Γ' ⊆ Γ) → ⟨ Σ , e ⟩ ⇓⟨ slice θ p , pc ⟩ ⟨ Σ' , v ⟩ →
           Step θ pc ⟨ Σ , wken e p ⟩ ⟨ Σ' , v ⟩

    Inl : ∀ {Σ Σ' τ₁ τ₂} {e : Expr _ τ₁} {v : Value τ₁}  →
            ⟨ Σ , e ⟩ ⇓⟨ θ , pc ⟩ ⟨ Σ' , v ⟩ →
            Step θ pc ⟨ Σ , inl {τ₂ = τ₂} e ⟩ ⟨ Σ' , inl v ^ pc ⟩

    Inr : ∀ {Σ Σ' τ₁ τ₂} {e : Expr _ τ₂} {v : Value τ₂}  →
            ⟨ Σ , e ⟩ ⇓⟨ θ , pc ⟩ ⟨ Σ' , v ⟩ →
            Step θ pc ⟨ Σ , inr {τ₁ = τ₁} e ⟩ ⟨ Σ' , inr v ^ pc ⟩

    Case₁ :  ∀ {Σ Σ' Σ'' ℓ ℓ' τ₁ τ₂ τ} {e : Expr _ (τ₁ + τ₂)} {e₁ : Expr _ τ}  {e₂ : Expr _ τ}  →
             {v₁ : Value τ₁} {v : Value τ} →
             ⟨ Σ , e ⟩ ⇓⟨ θ , pc ⟩ ⟨ Σ' , inl v₁ ^ ℓ ⟩ →
             ℓ' ≡ pc ⊔ ℓ →
             ⟨ Σ' , e₁ ⟩ ⇓⟨ v₁ ∷ θ , ℓ' ⟩ ⟨ Σ'' , v ⟩ →
             Step θ pc ⟨ Σ , case e e₁ e₂ ⟩ ⟨ Σ'' , v ⟩

    Case₂ :  ∀ {Σ Σ' Σ'' ℓ ℓ' τ₁ τ₂ τ} {e : Expr _ (τ₁ + τ₂)} {e₁ : Expr _ τ}  {e₂ : Expr _ τ}  →
             {v₂ : Value τ₂} {v : Value τ} →
             ⟨ Σ , e ⟩ ⇓⟨ θ , pc ⟩ ⟨ Σ' , inr v₂ ^ ℓ ⟩ →
             ℓ' ≡ pc ⊔ ℓ →
             ⟨ Σ' , e₂ ⟩ ⇓⟨ v₂ ∷ θ , ℓ' ⟩ ⟨ Σ'' , v ⟩ →
             Step θ pc ⟨ Σ , case e e₁ e₂ ⟩ ⟨ Σ'' , v ⟩


    Pair : ∀ {Σ Σ' Σ'' τ₁ τ₂} {e₁ : Expr _ τ₁} {e₂ : Expr _ τ₂} {v₁ : Value τ₁} {v₂ : Value τ₂} →
             ⟨ Σ , e₁ ⟩ ⇓⟨ θ , pc ⟩ ⟨ Σ' , v₁ ⟩ →
             ⟨ Σ' , e₂ ⟩ ⇓⟨ θ , pc ⟩ ⟨ Σ'' , v₂ ⟩ →
             Step θ pc ⟨ Σ , ⟨ e₁ , e₂ ⟩ ⟩ ⟨ Σ'' , ⟨ v₁ , v₂ ⟩ ^ pc ⟩

    Fst : ∀ {Σ Σ' τ₁ τ₂ ℓ ℓ'} {e : Expr _ (τ₁ × τ₂)} {v₁ : Value τ₁} {v₂ : Value τ₂} →
             ⟨ Σ , e ⟩ ⇓⟨ θ , pc ⟩ ⟨ Σ' , ⟨ v₁ , v₂ ⟩ ^ ℓ ⟩ →
             let r ^ ℓ₁ = v₁ in
             ℓ' ≡ ℓ ⊔ ℓ₁ →
            Step θ pc ⟨ Σ , fst e ⟩ ⟨ Σ' , r ^ ℓ' ⟩

    Snd : ∀ {Σ Σ' τ₁ τ₂ ℓ ℓ'} {e : Expr _ (τ₁ × τ₂)} {v₁ : Value τ₁} {v₂ : Value τ₂} →
             ⟨ Σ , e ⟩ ⇓⟨ θ , pc ⟩ ⟨ Σ' , ⟨ v₁ , v₂ ⟩ ^ ℓ ⟩ →
             let r ^ ℓ₂ = v₂ in
             ℓ' ≡ ℓ ⊔ ℓ₂ →
             Step θ pc ⟨ Σ , snd e ⟩ ⟨ Σ' , r ^ ℓ' ⟩

    LabelOf : ∀ {Σ Σ' ℓ τ} {e : Expr _ τ} {r : Raw τ} →
                ⟨ Σ , e ⟩ ⇓⟨ θ , pc ⟩ ⟨ Σ' , r ^ ℓ ⟩ →
                Step θ pc ⟨ Σ , labelOf e ⟩ ⟨ Σ' , ⌞ ℓ ⌟ ^ ℓ ⟩

    GetLabel : ∀ {Σ} → Step θ pc ⟨ Σ , getLabel ⟩ ⟨ Σ , (⌞ pc ⌟ ^ pc) ⟩

    Taint : ∀ {Σ Σ' Σ'' ℓ pc' pc'' e₁ τ} {e₂ : Expr Γ τ} {v : Value τ} →
              (eq : pc'' ≡ pc ⊔ ℓ) →
              Step θ pc ⟨ Σ , e₁ ⟩ ⟨ Σ' , ⌞ ℓ ⌟ ^ pc' ⟩ →
              Step θ pc''  ⟨ Σ' , e₂ ⟩ ⟨ Σ'' , v ⟩ →
              (pc'⊑pc'' : pc' ⊑ pc'') →
              Step θ pc ⟨ Σ , taint e₁ e₂ ⟩ ⟨ Σ'' , v ⟩

    LabelOfRef : ∀ {Σ Σ' ℓ ℓ' ℓ'' n τ} {e : Expr Γ (Ref τ)} →
                 ⟨ Σ , e ⟩ ⇓⟨ θ , pc ⟩ ⟨ Σ' , Ref ℓ n ^ ℓ' ⟩ →
                 (eq : ℓ'' ≡ ℓ ⊔ ℓ') →
                 Step θ pc ⟨ Σ , labelOfRef e ⟩ ⟨ Σ' , ⌞ ℓ ⌟ ^ ℓ'' ⟩

    New : ∀ {ℓ τ Σ Σ' } {e : Expr Γ _} {r : Raw τ} →
          ⟨ Σ , e ⟩ ⇓⟨ θ , pc ⟩ ⟨ Σ' , r ^ ℓ ⟩ →
          let M = Σ' ℓ in
          Step θ pc ⟨ Σ , new e ⟩  ⟨  Σ' [ ℓ ↦ M ∷ᴿ r ]ˢ , (Ref ℓ ∥ M ∥) ^ pc ⟩

    -- This is better than asking ℓ' ⊑ ℓ and returning the value at pc
    -- ⊔ ℓ. The combination pc ⊑ ℓ' (step-⊑) and ℓ' ⊑ ℓ implies pc ⊑
    -- ℓ, thus the rule would not allow to read lower references.
    Read : ∀ {Σ Σ' ℓ ℓ' ℓ'' n τ} {e : Expr _ (Ref τ)} {r : Raw τ } →
           ⟨ Σ , e ⟩ ⇓⟨ θ , pc ⟩ ⟨ Σ' , (Ref  ℓ n) ^ ℓ' ⟩ →
           n ↦ r ∈ᴹ (Σ' ℓ) →
           (eq : ℓ'' ≡ (ℓ ⊔ ℓ')) →
           Step θ pc ⟨ Σ , ! e ⟩  ⟨ Σ' ,  r ^ ℓ'' ⟩

    Write : ∀ {Σ₁ Σ₂ Σ₃ ℓ ℓ₂ ℓ' n τ} {M' : Memory ℓ} {e₁ : Expr _ (Ref τ)}
              {e₂ : Expr _ τ} {r₂ : Raw τ} →
             ⟨ Σ₁ , e₁ ⟩ ⇓⟨ θ , pc ⟩ ⟨ Σ₂ , (Ref ℓ n) ^ ℓ' ⟩ →
              ℓ' ⊑ pc →
             ⟨ Σ₂ , e₂ ⟩ ⇓⟨ θ , pc ⟩ ⟨ Σ₃ , r₂ ^ ℓ₂ ⟩ →
             (ℓ₂⊑ℓ : ℓ₂ ⊑ ℓ) →
               M' ≔ (Σ₃ ℓ) [ n ↦ r₂ ]ᴹ →
             Step θ pc ⟨ Σ₁ , e₁ ≔ e₂ ⟩ ⟨ Σ₃ [ ℓ ↦ M' ]ˢ , （） ^ pc ⟩

    Id : ∀ {Σ₁ Σ₂ τ} {e : Expr Γ τ} {v : Value τ} →
            ⟨ Σ₁ , e ⟩ ⇓⟨ θ , pc ⟩ ⟨ Σ₂ , v ⟩ →
            Step θ pc ⟨ Σ₁ , Id e ⟩ ⟨ Σ₂ , Id v ^ pc ⟩

    UnId : ∀ {Σ₁ Σ₂ τ v ℓ₁ ℓ₂} {e : Expr Γ (Id τ)} →
             ⟨ Σ₁ , e ⟩ ⇓⟨ θ , pc ⟩ ⟨ Σ₂ , Id v ^ ℓ₁ ⟩ →
             let r ^ ℓ' = v in
             (eq : ℓ₂ ≡ ℓ₁ ⊔ ℓ') →
             Step θ pc ⟨ Σ₁ , unId e ⟩ ⟨ Σ₂ , r ^ ℓ₂ ⟩

  -- Pretty syntax
  _⇓⟨_,_⟩_ : ∀ {Γ τ} → IConf Γ τ → Env Γ → Label → FConf τ → Set
  c₁ ⇓⟨ θ , pc ⟩ c₂ = Step θ pc c₁ c₂

--------------------------------------------------------------------------------
-- Shorthands

Wken′ : ∀ {Γ Γ' Σ Σ' pc τ v θ} {e : Expr Γ τ} (θ' : Env Γ')
        → ⟨ Σ , e ⟩ ⇓⟨ θ , pc ⟩ ⟨ Σ' , v ⟩
        → ⟨ Σ , wken e (drop-⊆₂ Γ Γ')  ⟩ ⇓⟨ θ' ++ᴱ θ , pc ⟩ ⟨ Σ' , v ⟩
Wken′  {Γ' = Γ'} θ'' x = Wken (drop-⊆₂ _ Γ') x

-- Execution under weakening

↑¹-⇓  :  ∀ {Γ  Σ Σ' pc τ τ' v θ} {e : Expr Γ τ} {v₁ : Value τ'}
        → ⟨ Σ , e ⟩ ⇓⟨ θ , pc ⟩ ⟨ Σ' , v ⟩
        → ⟨ Σ , e ↑¹ ⟩ ⇓⟨ v₁ ∷  θ , pc ⟩ ⟨ Σ' , v ⟩
↑¹-⇓ {v₁ = v₁}  = Wken′ (v₁ ∷ [])

↑²-⇓  :  ∀ {Γ  Σ Σ' pc τ τ₁ τ₂ v θ} {e : Expr Γ τ} {v₁ : Value τ₁} {v₂ : Value τ₂}
        → ⟨ Σ , e ⟩ ⇓⟨ θ , pc ⟩ ⟨ Σ' , v ⟩
        → ⟨ Σ , e ↑² ⟩ ⇓⟨ v₁ ∷ v₂ ∷ θ , pc ⟩ ⟨ Σ' , v ⟩
↑²-⇓ {v₁ = v₁} {v₂ = v₂} = Wken′ (v₁ ∷ v₂ ∷ [])

⇓-with : ∀ {τ Γ c₂ c₂' θ pc} {c₁ : IConf Γ τ} → c₁ ⇓⟨ θ , pc ⟩ c₂ → c₂ ≡ c₂' → c₁ ⇓⟨ θ , pc ⟩ c₂'
⇓-with x refl = x

--------------------------------------------------------------------------------

open Value
open import Data.Product
open import Relation.Binary.PropositionalEquality

-- The result of the value is at least as senstive as the program
-- counter.
step-⊑ : ∀ {Σ Σ' Γ τ pc} {e : Expr Γ τ} {v : Value τ} {θ : Env Γ} →
             ⟨ Σ , e ⟩ ⇓⟨ θ , pc ⟩ ⟨ Σ' , v ⟩ →
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
step-⊑ (Id x) = refl-⊑
step-⊑ (UnId x eq) rewrite eq = trans-⊑ (step-⊑ x) (join-⊑₁ _ _)
