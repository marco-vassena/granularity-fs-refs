open import Lattice

module CG.Valid {{𝑳 : Lattice}} where

open import CG.Types hiding (_×_) renaming ( _⊆_ to  _⊆ᶜ_)
open import CG.Syntax
open import Data.Product as P renaming (_,_ to _∧_)
open import Data.Nat renaming (_⊔_ to _⊔ᴺ_) hiding (_^_)
open import Data.Nat.Properties
open import Data.Unit hiding (_≤_)
open import Relation.Binary.PropositionalEquality
open import Generic.Heap.Lemmas Ty LValue

mutual

  -- Compute the domain of values and environment. This is the minimum
  -- size that the heap must have for all the heap addresses in these
  -- terms to be valid.
  ∥_∥ⱽ : ∀ {τ} → Value τ → ℕ
  ∥ （） ∥ⱽ = 0
  ∥ ⟨ e , θ ⟩ᶜ ∥ⱽ = ∥ θ ∥ᴱ
  ∥ ⟨ t , θ ⟩ᵀ ∥ⱽ = ∥ θ ∥ᴱ
  ∥ inl v ∥ⱽ = ∥ v ∥ⱽ
  ∥ inr v ∥ⱽ = ∥ v ∥ⱽ
  ∥ ⟨ v₁ , v₂ ⟩ ∥ⱽ = ∥ v₁ ∥ⱽ ⊔ᴺ ∥ v₂ ∥ⱽ
  ∥ Labeled ℓ v ∥ⱽ = ∥ v ∥ⱽ
  ∥ Refᴵ ℓ n ∥ⱽ = 0 -- Memory references do not contribute to the minimum size of the heap.
  ∥ Refˢ n ∥ⱽ = suc n
  ∥ ⌞ ℓ ⌟ ∥ⱽ = 0

  ∥_∥ᴱ : ∀ {Γ} → Env Γ → ℕ
  ∥ [] ∥ᴱ = 0
  ∥ v ∷ θ ∥ᴱ = ∥ v ∥ⱽ ⊔ᴺ ∥ θ ∥ᴱ

∥_∥ᴸ : ∀ {τ} → LValue τ → ℕ
∥ v ∧ ℓ ∥ᴸ = ∥ Labeled ℓ v ∥ⱽ

mutual

  Validᴱ : ∀ {Γ} → ℕ → Env Γ → Set
  Validᴱ n [] = ⊤
  Validᴱ n (v ∷ θ) = Validⱽ n v × Validᴱ n θ

  Validⱽ : ∀ {τ} → ℕ → Value τ → Set
  Validⱽ n （） = ⊤
  Validⱽ n ⟨ x , θ ⟩ᶜ = Validᴱ n θ
  Validⱽ n ⟨ t , θ ⟩ᵀ = Validᴱ n θ
  Validⱽ n (Labeled ℓ v) = Validⱽ n v
  Validⱽ n (inl v) = Validⱽ n v
  Validⱽ n (inr v) = Validⱽ n v
  Validⱽ n ⟨ v₁ , v₂ ⟩ = Validⱽ n v₁ × Validⱽ n v₂
  Validⱽ n (Refᴵ {τ = τ} ℓ m) = ⊤ -- Memory references need not to be valid.
  Validⱽ {τ} n (Refˢ m) = m < n -- Heap address m is valid for a heap of size n only if m < n
  Validⱽ n ⌞ ℓ ⌟ = ⊤

Validᴸ : ∀ {τ} → ℕ → LValue τ → Set
Validᴸ n (v ∧ ℓ) = Validⱽ n (Labeled ℓ v)

mutual

  validⱽ-≤ : ∀ {τ n} (v : Value τ) → Validⱽ n v → ∥ v ∥ⱽ ≤ n
  validⱽ-≤ （） isV = z≤n
  validⱽ-≤ ⟨ x , θ ⟩ᶜ isV = validᴱ-≤ θ isV
  validⱽ-≤ ⟨ t , θ ⟩ᵀ isV =  validᴱ-≤ θ isV
  validⱽ-≤ (Labeled ℓ v) isV = validⱽ-≤ v isV
  validⱽ-≤ (inl x) isV = validⱽ-≤ x isV
  validⱽ-≤ (inr x) isV = validⱽ-≤ x isV
  validⱽ-≤ ⟨ x , y ⟩ (isV₁ ∧ isV₂) = join-≤ (validⱽ-≤ x isV₁) (validⱽ-≤ y isV₂)
  validⱽ-≤ (Refᴵ x x₁) isV = z≤n
  validⱽ-≤ (Refˢ x) isV = isV
  validⱽ-≤ ⌞ x ⌟ isV = z≤n

  validᴱ-≤ : ∀ {Γ n} (θ : Env Γ) → Validᴱ n θ → ∥ θ ∥ᴱ ≤ n
  validᴱ-≤ [] tt = z≤n
  validᴱ-≤ {n = n} (v ∷ θ) (isVⱽ ∧ isVᴱ) = join-≤ (validⱽ-≤ v isVⱽ) (validᴱ-≤ θ isVᴱ)

validᴸ-≤ : ∀ {τ n} (v : LValue τ) → Validᴸ n v → ∥ v ∥ᴸ ≤ n
validᴸ-≤ (v ∧ ℓ) isV = validⱽ-≤ (Labeled ℓ v) isV

lookup-validⱽ : ∀ {τ Γ θ n} → (τ∈Γ : τ ∈ Γ) → Validᴱ n θ → Validⱽ n (θ !! τ∈Γ )
lookup-validⱽ {θ = _ ∷ θ} here (isV ∧ _) = isV
lookup-validⱽ {θ = _ ∷ θ} (there τ∈Γ) (_ ∧ isV) = lookup-validⱽ τ∈Γ isV

mutual

  -- TODO rename to valid-wken
  wken-validⱽ : ∀ {τ n n'} (v : Value τ) → n ≤ n' → Validⱽ n v → Validⱽ n' v
  wken-validⱽ （） ≤₁ isV = tt
  wken-validⱽ ⟨ x , θ ⟩ᶜ ≤₁ isV = wken-validᴱ θ ≤₁ isV
  wken-validⱽ ⟨ t , θ ⟩ᵀ ≤₁ isV = wken-validᴱ θ ≤₁ isV
  wken-validⱽ (Labeled ℓ v) ≤₁ isV = wken-validⱽ v ≤₁ isV
  wken-validⱽ (inl v) ≤₁ isV = wken-validⱽ v ≤₁ isV
  wken-validⱽ (inr v) ≤₁ isV = wken-validⱽ v ≤₁ isV
  wken-validⱽ ⟨ v₁ , v₂ ⟩ ≤₁ (isV₁ ∧ isV₂) = wken-validⱽ v₁ ≤₁ isV₁ ∧ wken-validⱽ v₂ ≤₁ isV₂
  wken-validⱽ (Refᴵ _ v) ≤₁ isV = tt
  wken-validⱽ (Refˢ v) ≤₁ isV = ≤-trans isV ≤₁
  wken-validⱽ ⌞ _ ⌟ ≤₁ isV = tt

  wken-validᴱ : ∀ {Γ n n'} (θ : Env Γ) → n ≤ n' → Validᴱ n θ → Validᴱ n' θ
  wken-validᴱ [] ≤₁ isV = tt
  wken-validᴱ (v ∷ θ) ≤₁ (isV₁ ∧ isV₂) = (wken-validⱽ v ≤₁ isV₁) ∧ (wken-validᴱ θ ≤₁ isV₂)

wken-validᴸ : ∀ {τ n n'} (v : LValue τ) → n ≤ n' → Validᴸ n v → Validᴸ n' v
wken-validᴸ (v ∧ ℓ) ≤₁ isV = wken-validⱽ (Labeled ℓ v) ≤₁ isV

open import Generic.Valid

instance
  isValidⱽ : IsValid Ty Value ∥_∥ⱽ
  isValidⱽ = record { Valid = Validⱽ ; wken-valid = wken-validⱽ ; valid-≤ = validⱽ-≤ }

  isValidᴱ : IsValid Ctx Env ∥_∥ᴱ
  isValidᴱ = record { Valid = Validᴱ ; wken-valid = wken-validᴱ ; valid-≤ = validᴱ-≤ }

  isValidᴸ : IsValid Ty LValue ∥_∥ᴸ
  isValidᴸ = record { Valid = Validᴸ ; wken-valid = wken-validᴸ ; valid-≤ = validᴸ-≤ }

open Conf
open import CG.Semantics
open import Generic.PState.Valid isValidⱽ isValidᴸ public

mutual

  step-≤ :  ∀ {τ Γ θ} {c : TConf Γ (LIO τ)} {c' : FConf τ} → c ⇓⟨ θ ⟩ c' → ∥ heap c ∥ᴴ ≤ ∥ heap c' ∥ᴴ
  step-≤ (Return x) = ≤-refl
  step-≤ (Bind x x₁) = ≤-trans (stepᶠ-≤ x) (stepᶠ-≤ x₁)
  step-≤ (Unlabel x eq) = ≤-refl
  step-≤ (ToLabeled x) = stepᶠ-≤ x
  step-≤ (LabelOf x x₁) = ≤-refl
  step-≤ GetLabel = ≤-refl
  step-≤ (Taint x x₁) = ≤-refl
  step-≤ (New x x₁) = ≤-refl
  step-≤ (Read x n∈M eq) = ≤-refl
  step-≤ (Write x x₁ x₂ x₃ up) = ≤-refl
  step-≤ (LabelOfRef x eq) = ≤-refl
  step-≤ (New-FS x x₁) = snoc-≤
  step-≤ (Read-FS x n∈μ eq) = ≤-refl
  step-≤ (Write-FS x x₁ n∈μ x₂ x₃ w) rewrite write-length-≡ w = ≤-refl
  step-≤ (LabelOfRef-FS x n∈μ eq) = ≤-refl

  stepᶠ-≤ :  ∀ {τ Γ θ} {c : EConf Γ (LIO τ)} {c' : FConf τ} → c ⇓ᶠ⟨ θ ⟩ c' → ∥ heap c ∥ᴴ ≤ ∥ heap c' ∥ᴴ
  stepᶠ-≤ (Force x x₁) = step-≤ x₁

Valid-Inputs : ∀ {F} {Γ} {τ} → Conf F Γ τ → Env Γ →  Set
Valid-Inputs ⟨ Σ , μ , _ , _ ⟩ θ = Validᴾ ⟨ Σ , μ ⟩ × Validᴱ ∥ μ ∥ᴴ θ

Valid-Outputs : ∀ {τ} → FConf τ → Set
Valid-Outputs ⟨ Σ , μ , _ , v ⟩ = Validᴾ ⟨ Σ , μ ⟩ × Validⱽ ∥ μ ∥ᴴ v

slice-validᴱ : ∀ {Γ Γ' n} (θ : Env Γ) → (p : Γ' ⊆ᶜ Γ) → Validᴱ n θ → Validᴱ n (slice θ p)
slice-validᴱ [] base isV = tt
slice-validᴱ (_ ∷ θ) (cons p) (isV₁ ∧ isV₂) = isV₁ ∧ slice-validᴱ θ p isV₂
slice-validᴱ (_ ∷ θ) (drop p) (_ ∧ isV) = slice-validᴱ θ p isV

validⱽ-⇓ᴾ : ∀ {τ Γ n} {e : Expr Γ τ} {θ : Env Γ} {v : Value τ} →
              e ⇓ᴾ⟨ θ ⟩ v →
              Validᴱ n θ →
              Validⱽ n v
validⱽ-⇓ᴾ Unit isV = tt
validⱽ-⇓ᴾ (Lbl ℓ) isV = tt
validⱽ-⇓ᴾ (Test₁ x x₁ x₂) isV = tt
validⱽ-⇓ᴾ (Test₂ x x₁ x₂) isV = tt
validⱽ-⇓ᴾ (Wken p x) isV = validⱽ-⇓ᴾ x (slice-validᴱ _ p isV)
validⱽ-⇓ᴾ (Var τ∈Γ) isV = lookup-validⱽ τ∈Γ isV
validⱽ-⇓ᴾ SThunk isV = isV
validⱽ-⇓ᴾ Fun isV = isV
validⱽ-⇓ᴾ (App x₁ x₂ x₃) isV = validⱽ-⇓ᴾ x₃ (isV₂ ∧ isV₁)
  where isV₁ = validⱽ-⇓ᴾ x₁ isV
        isV₂ = validⱽ-⇓ᴾ x₂ isV
validⱽ-⇓ᴾ (Inl x) isV = validⱽ-⇓ᴾ x isV
validⱽ-⇓ᴾ (Inr x) isV = validⱽ-⇓ᴾ x isV
validⱽ-⇓ᴾ (Case₁ x₁ x₂) isV = validⱽ-⇓ᴾ x₂ (isV₁ ∧ isV)
  where isV₁ = validⱽ-⇓ᴾ x₁ isV
validⱽ-⇓ᴾ (Case₂ x₁ x₂) isV = validⱽ-⇓ᴾ x₂ (isV₁ ∧ isV)
  where isV₁ = validⱽ-⇓ᴾ x₁ isV
validⱽ-⇓ᴾ (Pair x x₁) isV = (validⱽ-⇓ᴾ x isV) ∧ (validⱽ-⇓ᴾ x₁ isV)
validⱽ-⇓ᴾ (Fst x) isV = proj₁ (validⱽ-⇓ᴾ x isV)
validⱽ-⇓ᴾ (Snd x) isV = proj₂ (validⱽ-⇓ᴾ x isV)

open Validᴾ

mutual

  validᴼ-⇓ : ∀ {τ Γ} {θ : Env Γ} {c : TConf Γ (LIO τ)} {c' : FConf τ} →
               c ⇓⟨ θ ⟩ c' →
               let ⟨ Σ' , μ' , _  , v ⟩ = c' in
               Valid-Inputs c θ →
               Valid-Outputs c'
  validᴼ-⇓ (Return x) (isVᴾ ∧ isVᴱ) = (isVᴾ ∧ validⱽ-⇓ᴾ x isVᴱ) -- ∧ isVᴱ
  validᴼ-⇓ (Bind x₁ x₂) isV =
    let (isVᴾ ∧ isVⱽ ) = validᴼ-⇓ᶠ x₁ isV
        isVᴱ = wken-validᴱ _ (stepᶠ-≤ x₁) (proj₂ isV)
        (isVᴾ′ ∧ isVⱽ′) = validᴼ-⇓ᶠ x₂ (isVᴾ ∧ isVⱽ ∧ isVᴱ)
    in isVᴾ′ ∧ isVⱽ′

  validᴼ-⇓ (Unlabel x eq) (isVᴾ ∧ isVᴱ) = isVᴾ ∧ validⱽ-⇓ᴾ x isVᴱ

  validᴼ-⇓ (ToLabeled x) isV = validᴼ-⇓ᶠ x isV
  validᴼ-⇓ (LabelOf x x₁) (isVᴾ ∧ isVᴱ) = isVᴾ ∧ tt
  validᴼ-⇓ GetLabel (isVᴾ ∧ isVᴱ) = isVᴾ ∧ tt
  validᴼ-⇓ (Taint x x₁) (isVᴾ ∧ isVᴱ) = isVᴾ ∧ tt

  validᴼ-⇓ (New {μ = μ} x x₁) (⟨ isVˢ , isVᴴ ⟩ ∧ isVᴱ) = ⟨ isVˢ′ , isVᴴ ⟩ ∧ tt
    where isVᴹ = snoc-validᴹ  ∥ μ ∥ᴴ (isVˢ _) (validⱽ-⇓ᴾ x isVᴱ)
          isVˢ′ = update-validˢ ∥ μ ∥ᴴ isVˢ isVᴹ

  validᴼ-⇓ (Read {μ = μ} x ∈₁ eq) (isVᴾ ∧ isVᴱ) = isVᴾ ∧ read-validᴿ ∥ μ ∥ᴴ (validˢ isVᴾ _) ∈₁

  validᴼ-⇓ (Write {μ = μ} x₁ x₂ ⊑₁ ⊑₂ w) (⟨ isVˢ , isVᴴ ⟩ ∧ isVᴱ) = ⟨ isVˢ′ , isVᴴ ⟩ ∧ tt
    where isV = validⱽ-⇓ᴾ x₂ isVᴱ
          isVˢ′ = update-validˢ ∥ μ ∥ᴴ  isVˢ (write-validᴹ ∥ μ ∥ᴴ (isVˢ _) w isV)

  validᴼ-⇓ (LabelOfRef x eq) (isVᴾ ∧ isVᴱ) = isVᴾ ∧ tt

  validᴼ-⇓ (New-FS {μ = μ} {ℓ = ℓ} {v = v}  x _) (⟨ isVˢ , isVᴴ ⟩ ∧ isVᴱ) = ⟨ isVˢ′ , isVᴴ′ ⟩ ∧ ≤₁
    where lv = v ∧ ℓ
          eq = ∥snoc∥ μ lv
          ≤₁ : suc ∥ μ ∥ᴴ ≤ ∥ snocᴴ μ lv ∥ᴴ
          ≤₁ rewrite eq = s≤s ≤-refl
          isVˢ′ = validˢ-⊆ᴴ snoc-≤ isVˢ
          isV = validⱽ-⇓ᴾ x isVᴱ
          isVᴴ′ = snoc-validᴴ′ isVᴴ (wken-validⱽ v (≤-step ≤-refl) isV)

  validᴼ-⇓ (Read-FS {μ = μ} x ∈₁ eq) (isVᴾ ∧ isVᴱ) = isVᴾ ∧ read-validⱽ ∥ μ ∥ᴴ (validᴴ isVᴾ) ∈₁

  validᴼ-⇓ (Write-FS {μ' = μ} x₁ x₂ ∈₁ ⊑₁ eq w) (⟨ isVˢ , isVᴴ ⟩ ∧ isVᴱ)
    rewrite sym (write-length-≡ w) = ⟨ isVˢ , isVᴴ′ ⟩ ∧ tt
    where isV = validⱽ-⇓ᴾ x₂ isVᴱ
          isVᴴ′ = write-validᴴ ∥ μ ∥ᴴ isVᴴ w isV

  validᴼ-⇓ (LabelOfRef-FS x n∈μ eq) (isVᴾ ∧ isVᴱ) = isVᴾ ∧ tt

  validᴼ-⇓ᶠ :  ∀ {τ Γ} {θ : Env Γ} {c : EConf Γ (LIO τ)} {c' : FConf τ} →
                c ⇓ᶠ⟨ θ ⟩ c' →
                let ⟨ Σ' , μ' , _  , v ⟩ = c' in
                Valid-Inputs c θ →
                Valid-Outputs c'
  validᴼ-⇓ᶠ (Force x x₁) (isVᴾ ∧ isVᴱ) = validᴼ-⇓ x₁ (isVᴾ ∧ (validⱽ-⇓ᴾ x isVᴱ))

  valid-⇓ᶠ : ∀ {τ Γ} {θ : Env Γ} {c : EConf Γ (LIO τ)} {c' : FConf τ} →
                c ⇓ᶠ⟨ θ ⟩ c' →
                let ⟨ Σ' , μ' , _  , v ⟩ = c' in
                Valid-Inputs c θ →
                Validᴾ ⟨ Σ' , μ' ⟩ × Validᴱ ∥ μ' ∥ᴴ (v ∷ θ)
  valid-⇓ᶠ x isV =
    let isVᴾ ∧ isVⱽ = validᴼ-⇓ᶠ x isV
        isVᴱ = wken-validᴱ _ (stepᶠ-≤ x) (proj₂ isV)
    in isVᴾ ∧ (isVⱽ ∧ isVᴱ)
