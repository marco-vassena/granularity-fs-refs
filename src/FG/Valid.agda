open import Lattice

module FG.Valid {{𝑳 : Lattice}} where

open import FG.Types hiding (_×_) renaming ( _⊆_ to  _⊆ᶜ_) --  (Ty ; _⊆_ ; I ; S)
open import FG.Syntax
open import Data.Product as P renaming (_,_ to _∧_)
open import Data.Nat renaming (_⊔_ to _⊔ᴺ_) hiding (_^_)
open import Data.Nat.Properties
open import Data.Unit hiding (_≤_)
open import Relation.Binary.PropositionalEquality
open import Generic.Heap.Lemmas Ty Value

mutual

  -- "Size" of a value
  ∥_∥ⱽ : ∀ {τ} → Value τ → ℕ
  ∥ r ^ ℓ ∥ⱽ = ∥ r ∥ᴿ

  ∥_∥ᴿ : ∀ {τ} → Raw τ → ℕ
  ∥ （） ∥ᴿ = 0
  ∥ ⟨ x , θ ⟩ᶜ ∥ᴿ = ∥ θ ∥ᴱ
  ∥ inl x ∥ᴿ = ∥ x ∥ⱽ
  ∥ inr x ∥ᴿ = ∥ x ∥ⱽ
  ∥ ⟨ x , y ⟩ ∥ᴿ = ∥ x ∥ⱽ ⊔ᴺ ∥ y ∥ⱽ
  ∥ Refᴵ x n ∥ᴿ = 0 -- 0 because we only care about the domain of the refs in the heap (ℕ.suc n)a
  ∥ Refˢ n ∥ᴿ = suc n
  ∥ ⌞ x ⌟ ∥ᴿ = 0
  ∥ Id x ∥ᴿ = ∥ x ∥ⱽ

  ∥_∥ᴱ : ∀ {Γ} → Env Γ → ℕ
  ∥ [] ∥ᴱ = 0
  ∥ v ∷ θ ∥ᴱ = ∥ v ∥ⱽ ⊔ᴺ ∥ θ ∥ᴱ

-- Needed?
-- mutual

  Validᴱ : ∀ {Γ} → ℕ → Env Γ → Set
  Validᴱ n [] = ⊤
  Validᴱ n (v ∷ θ) = Validⱽ n v × Validᴱ n θ

  Validᴿ : ∀ {τ} → ℕ → Raw τ → Set
  Validᴿ n （） = ⊤
  Validᴿ n ⟨ x , θ ⟩ᶜ = Validᴱ n θ
  Validᴿ n (inl v) = Validⱽ n v
  Validᴿ n (inr v) = Validⱽ n v
  Validᴿ n ⟨ v₁ , v₂ ⟩ = Validⱽ n v₁ × Validⱽ n v₂
  -- TODO: there could be some (equivalent) alternatives.  E.g.,
  -- define a special (unlabelde) cell type for flow-insensitive
  -- references and ask that it has the right type.
  -- TODO: if we have a separate store do we need validity at all?
  -- Maybe just for the store?
  Validᴿ n (Refᴵ {τ = τ} ℓ m) = ⊤ -- This is ok because it is the store Σ
  -- TODO: should I have any requirement on the label of the cell for flow-sensitve refs?
  Validᴿ {τ} n (Refˢ m) = m < n -- This does not seem to be needed. Answer: It will be needed when we prove the invariant!
  Validᴿ n ⌞ ℓ ⌟ = ⊤
  Validᴿ n (Id v) = Validⱽ n v

  Validⱽ : ∀ {τ} → ℕ → Value τ → Set
  Validⱽ n (r ^ ℓ) = Validᴿ n r

join-≤ : ∀ {x y z} → x ≤ z → y ≤ z → x ⊔ᴺ y ≤ z
join-≤ {z = z} x≤z y≤z with ⊔-mono-≤ x≤z y≤z
... | ≤₁ rewrite m≤n⇒m⊔n≡n {z} ≤-refl = ≤₁

mutual

  validⱽ-≤ : ∀ {τ n} (v : Value τ) → Validⱽ n v → ∥ v ∥ⱽ ≤ n
  validⱽ-≤ (r ^ _) isV = validᴿ-≤ r isV

  validᴿ-≤ : ∀ {τ n} (r : Raw τ) → Validᴿ n r → ∥ r ∥ᴿ ≤ n
  validᴿ-≤ （） isV = z≤n
  validᴿ-≤ ⟨ x , θ ⟩ᶜ isV = validᴱ-≤ θ isV
  validᴿ-≤ (inl x) isV = validⱽ-≤ x isV
  validᴿ-≤ (inr x) isV = validⱽ-≤ x isV
  validᴿ-≤ ⟨ x , y ⟩ (isV₁ ∧ isV₂) = join-≤ (validⱽ-≤ x isV₁) (validⱽ-≤ y isV₂)
  validᴿ-≤ (Refᴵ x x₁) isV = z≤n
  validᴿ-≤ (Refˢ x) isV = isV
  validᴿ-≤ ⌞ x ⌟ isV = z≤n
  validᴿ-≤ (Id x) isV = validⱽ-≤ x isV

  validᴱ-≤ : ∀ {Γ n} (θ : Env Γ) → Validᴱ n θ → ∥ θ ∥ᴱ ≤ n
  validᴱ-≤ [] tt = z≤n
  validᴱ-≤ {n = n} (v ∷ θ) (isVⱽ ∧ isVᴱ) = join-≤ (validⱽ-≤ v isVⱽ) (validᴱ-≤ θ isVᴱ)

open Conf
open import FG.Semantics
open import Generic.PState.Base Ty Ty Raw Value
open import Generic.PState.Valid {Ty} {Ty} {Raw} {Value} Validᴿ Validⱽ public

-- record Valid-Conf {A τ} (c : Conf A) : Set where
--   constructor ⟨_,_⟩
--   field
--     validᴾ : Validᴾ ⟨ store c , heap c ⟩
--     validᵀ : Validᴱ ∥ heap c ∥ᴴ θ


-- record Valid-Inputs {Γ} {τ} (c : IConf Γ τ) (θ : Env Γ) : Set where
--   constructor ⟨_,_⟩
--   field
--     validᴾ : Validᴾ ⟨ store c , heap c ⟩
--     validᴱ : Validᴱ ∥ heap c ∥ᴴ θ

--  open Validᴾ

-- open Valid-Inputs {{...}} public

Valid-Inputs : ∀ {Γ} {τ} → IConf Γ τ → Env Γ →  Set
Valid-Inputs ⟨ Σ , μ , _ ⟩ θ = Validᴾ ⟨ Σ , μ ⟩ × Validᴱ ∥ μ ∥ᴴ θ

Valid-Outputs : ∀ {τ} → FConf τ → Set
Valid-Outputs ⟨ Σ , μ , v ⟩ = Validᴾ ⟨ Σ , μ ⟩ × Validⱽ ∥ μ ∥ᴴ v


-- record Valid-Outputs′ {τ} (c : FConf τ) : Set where
--   constructor ⟨_,_⟩
--   field
--     validᴾ : Validᴾ ⟨ store c , heap c ⟩
--     validⱽ : Validⱽ ∥ heap c ∥ᴴ (term c)

-- open Valid-Outputs′ {{...}} public

-- record Valid-Outputs {τ} (c : FConf τ) : Set where
--   constructor ⟨_,_⟩
--   field
--     validᴾ : Validᴾ ⟨ store c , heap c ⟩
--     validⱽ : Validⱽ ∥ heap c ∥ᴴ (term c)


lookup-validⱽ : ∀ {τ Γ θ n} → (τ∈Γ : τ ∈ Γ) → Validᴱ n θ → Validⱽ n (θ !! τ∈Γ )
lookup-validⱽ {θ = _ ∷ θ} here (isV ∧ _) = isV
lookup-validⱽ {θ = _ ∷ θ} (there τ∈Γ) (_ ∧ isV) = lookup-validⱽ τ∈Γ isV

-- postulate read-validᴿ : ∀ {ℓ τ μ n} {r : Raw τ} {M : Memory ℓ} → Validᴹ ∥ μ ∥ᴴ M → n ↦ r ∈ᴹ M → Validᴿ ∥ μ ∥ᴴ r

-- postulate read-validᴿ : ∀ {ℓ τ μ n} {r : Raw τ} {M : Memory ℓ} → Validᴹ ∥ μ ∥ᴴ M → n ↦ r ∈ᴹ M → Validᴿ ∥ μ ∥ᴴ r

-- postulate write-validᴹ : ∀ {ℓ τ μ n} {r : Raw τ} {M M' : Memory ℓ} → Validᴹ ∥ μ ∥ᴴ M → M' ≔ M [ n ↦ r ]ᴹ →
--                            Validᴿ ∥ μ ∥ᴴ r → Validᴹ ∥ μ ∥ᴴ M'

-- postulate new-validᴹ : ∀ {ℓ τ μ} {r : Raw τ} {M : Memory ℓ} → Validᴹ ∥ μ ∥ᴴ M →
--                            Validᴿ ∥ μ ∥ᴴ r → Validᴹ ∥ μ ∥ᴴ (snocᴹ M r)

-- TODO: maybe it'd be more convenient to take the big-step in the main proof
-- and use these in this module

step-≤ :  ∀ {τ Γ θ pc} {c : IConf Γ τ} {c' : FConf τ} → c ⇓⟨ θ , pc ⟩ c' → ∥ heap c ∥ᴴ ≤ ∥ heap c' ∥ᴴ
step-≤ (Var τ∈Γ x) = ≤-refl
step-≤ Unit = ≤-refl
step-≤ (Lbl ℓ) = ≤-refl
step-≤ (Test₁ x x₁ _ _) = ≤-trans (step-≤ x) (step-≤ x₁)
step-≤ (Test₂ x x₁ _ _) = ≤-trans (step-≤ x) (step-≤ x₁)
step-≤ Fun = ≤-refl
step-≤ (App x x₁ _ x₂) = ≤-trans (≤-trans (step-≤ x) (step-≤ x₁)) (step-≤ x₂)
step-≤ (Wken p x) = step-≤ x
step-≤ (Inl x) = step-≤ x
step-≤ (Inr x) = step-≤ x
step-≤ (Case₁ x _ x₁) = ≤-trans (step-≤ x) (step-≤ x₁)
step-≤ (Case₂ x _ x₁) = ≤-trans (step-≤ x) (step-≤ x₁)
step-≤ (Pair x x₁) = ≤-trans (step-≤ x) (step-≤ x₁)
step-≤ (Fst x x₁) = step-≤ x
step-≤ (Snd x x₁) = step-≤ x
step-≤ (LabelOf x) = step-≤ x
step-≤ GetLabel = ≤-refl
step-≤ (Taint eq x x₁ pc'⊑pc'') = ≤-trans (step-≤ x) (step-≤ x₁)
step-≤ (LabelOfRef x _) = step-≤ x
step-≤ (New x) = step-≤ x
step-≤ (Read x _ _) = step-≤ x
step-≤ (Write x _ x₁ _ _) = ≤-trans (step-≤ x) (step-≤ x₁)
step-≤ (LabelOfRef-FS x _ _) = step-≤ x
step-≤ (New-FS {μ' = μ'} {v = v} x) = ≤-trans (step-≤ x)  snoc-≤
step-≤ (Read-FS x _ _) = step-≤ x
step-≤ (Write-FS x x₁ _ _ _ w) rewrite write-length-≡ w = ≤-trans (step-≤ x) (step-≤ x₁)
step-≤ (Id x) = step-≤ x
step-≤ (UnId x _) = step-≤ x

mutual

  validᴿ-⊆ᴴ′ : ∀ {τ n n'} (r : Raw τ) → n ≤ n' → Validᴿ n r → Validᴿ n' r
  validᴿ-⊆ᴴ′ （） ≤₁ isV = tt
  validᴿ-⊆ᴴ′ ⟨ x , θ ⟩ᶜ ≤₁ isV = validᴱ-⊆ᴴ′ θ ≤₁ isV
  validᴿ-⊆ᴴ′ (inl v) ≤₁ isV = validⱽ-⊆ᴴ′ v ≤₁ isV
  validᴿ-⊆ᴴ′ (inr v) ≤₁ isV = validⱽ-⊆ᴴ′ v ≤₁ isV
  validᴿ-⊆ᴴ′ ⟨ v₁ , v₂ ⟩ ≤₁ (isV₁ ∧ isV₂) = validⱽ-⊆ᴴ′ v₁ ≤₁ isV₁ ∧ validⱽ-⊆ᴴ′ v₂ ≤₁ isV₂
  validᴿ-⊆ᴴ′ (Refᴵ _ v) ≤₁ isV = tt
  validᴿ-⊆ᴴ′ (Refˢ v) ≤₁ isV = ≤-trans isV ≤₁
  validᴿ-⊆ᴴ′ ⌞ _ ⌟ ≤₁ isV = tt
  validᴿ-⊆ᴴ′ (Id v) ≤₁ isV = validⱽ-⊆ᴴ′ v ≤₁ isV

  validⱽ-⊆ᴴ′ : ∀ {τ n n'} (v : Value τ) → n ≤ n' → Validⱽ n v → Validⱽ n' v
  validⱽ-⊆ᴴ′ (r ^ _) ≤₁ isV = validᴿ-⊆ᴴ′ r ≤₁ isV

  validᴱ-⊆ᴴ′ : ∀ {Γ n n'} (θ : Env Γ) → n ≤ n' → Validᴱ n θ → Validᴱ n' θ
  validᴱ-⊆ᴴ′ [] ≤₁ isV = tt
  validᴱ-⊆ᴴ′ (v ∷ θ) ≤₁ (isV₁ ∧ isV₂) = (validⱽ-⊆ᴴ′ v ≤₁ isV₁) ∧ (validᴱ-⊆ᴴ′ θ ≤₁ isV₂)

-- TODO: it'd seem more useful to use the above rather than ⊆
validᴿ-⊆ᴴ : ∀ {τ μ μ'} {r : Raw τ} → μ ⊆ᴴ μ' → Validᴿ ∥ μ ∥ᴴ r → Validᴿ ∥ μ' ∥ᴴ r
validᴿ-⊆ᴴ {r = r} ⊆₁ isV = validᴿ-⊆ᴴ′ r (⊆-≤ (⊆-⊆′ ⊆₁)) isV

-- TODO: remove this as well
postulate validⱽ-⊆ᴴ : ∀ {τ μ μ'} {v : Value τ} → μ ⊆ᴴ μ' → Validⱽ ∥ μ ∥ᴴ v → Validⱽ ∥ μ' ∥ᴴ v
postulate validᴱ-⊆ᴴ : ∀ {Γ μ μ'} {θ : Env Γ} → μ ⊆ᴴ μ' → Validᴱ ∥ μ ∥ᴴ θ → Validᴱ ∥ μ' ∥ᴴ θ
postulate step-⊆ᴴ :  ∀ {τ Γ θ pc} {c : IConf Γ τ} {c' : FConf τ} → c ⇓⟨ θ , pc ⟩ c' → (heap c) ⊆ᴴ (heap c')

slice-validᴱ : ∀ {Γ Γ' μ} (θ : Env Γ) → (p : Γ' ⊆ᶜ Γ) → Validᴱ ∥ μ ∥ᴴ θ → Validᴱ ∥ μ ∥ᴴ (slice θ p)
slice-validᴱ [] base isV = tt
slice-validᴱ (_ ∷ θ) (cons p) (isV₁ ∧ isV₂) = isV₁ ∧ slice-validᴱ θ p isV₂
slice-validᴱ (_ ∷ θ) (drop p) (_ ∧ isV) = slice-validᴱ θ p isV


valid-invariant : ∀ {τ Γ ℓ} {θ : Env Γ} {c : IConf Γ τ} {c' : FConf τ} →
                    c ⇓⟨ θ , ℓ ⟩ c' → Valid-Inputs c θ →
                    Validᴱ ∥ heap c' ∥ᴴ θ × Valid-Outputs c'
valid-invariant (Var {μ = μ} τ∈Γ x) (isVᴾ ∧ isVᴱ) = isVᴱ ∧ isVᴾ ∧ lookup-validⱽ τ∈Γ isVᴱ

valid-invariant Unit (isVᴾ ∧ isVᴱ) = isVᴱ ∧ isVᴾ ∧ tt

valid-invariant (Lbl ℓ) (isVᴾ ∧ isVᴱ) = isVᴱ ∧ isVᴾ ∧ tt

valid-invariant (Test₁ x₁ x₂ _ _) (isVᴾ ∧ isVᴱ) =
  let (isVᴱ′ ∧ isVᴾ′ ∧ isVⱽ) = valid-invariant x₁ (isVᴾ ∧ isVᴱ)
      (isVᴱ′′ ∧ isVᴾ′′ ∧ isVⱽ′) = valid-invariant x₂ (isVᴾ′ ∧ isVᴱ′)
  in isVᴱ′′ ∧ isVᴾ′′ ∧ tt

valid-invariant (Test₂ x₁ x₂ _ _) (isVᴾ ∧ isVᴱ) =
  let (isVᴱ′ ∧ isVᴾ′ ∧ isVⱽ) = valid-invariant x₁ (isVᴾ ∧ isVᴱ)
      (isVᴱ′′ ∧ isVᴾ′′ ∧ isVⱽ′) = valid-invariant x₂ (isVᴾ′ ∧ isVᴱ′)
  in isVᴱ′′ ∧ isVᴾ′′ ∧ tt

valid-invariant Fun (isVᴾ ∧ isVᴱ) = isVᴱ ∧ isVᴾ ∧ isVᴱ

valid-invariant (App x₁ x₂ _ x₃) (isVᴾ ∧ isVᴱ) =
  let (isVᴱ′ ∧ isVᴾ′ ∧ isVⱽ) = valid-invariant x₁ (isVᴾ ∧ isVᴱ)
      (isVᴱ′′ ∧ isVᴾ′′ ∧ isVⱽ′) = valid-invariant x₂ (isVᴾ′ ∧ isVᴱ′)
      isVᴱ′′′ = validᴱ-⊆ᴴ (step-⊆ᴴ x₂) isVⱽ
      (_ ∧ isVᴾ′′ ∧ isVⱽ′′) = valid-invariant x₃ (isVᴾ′′ ∧ isVⱽ′ ∧ isVᴱ′′′)
  in validᴱ-⊆ᴴ (step-⊆ᴴ x₃) isVᴱ′′ ∧ isVᴾ′′ ∧ isVⱽ′′

valid-invariant (Wken {μ' = μ'} p x) (isVᴾ ∧ isVᴱ) =
  let (isVᴱ′ ∧ isVᴾ′ ∧ isVⱽ) = valid-invariant x (isVᴾ ∧ slice-validᴱ _ p isVᴱ)
  in validᴱ-⊆ᴴ (step-⊆ᴴ x) isVᴱ ∧ isVᴾ′ ∧ isVⱽ

valid-invariant (Inl x) (isVᴾ ∧ isVᴱ) =
  let (isVᴱ′ ∧ isVᴾ′ ∧ isVⱽ) = valid-invariant x (isVᴾ ∧ isVᴱ)
  in isVᴱ′ ∧ isVᴾ′ ∧ isVⱽ

valid-invariant (Inr x) (isVᴾ ∧ isVᴱ) =
  let (isVᴱ′ ∧ isVᴾ′ ∧ isVⱽ) = valid-invariant x (isVᴾ ∧ isVᴱ)
  in validᴱ-⊆ᴴ (step-⊆ᴴ x) isVᴱ ∧ isVᴾ′ ∧ isVⱽ

valid-invariant (Case₁ x₁ _ x₂) (isVᴾ ∧ isVᴱ) =
  let (isVᴱ′ ∧ isVᴾ′ ∧ isVⱽ) = valid-invariant x₁ (isVᴾ ∧ isVᴱ)
      (isVᴱ′′ ∧ isVᴾ′′ ∧ isVⱽ′) = valid-invariant x₂ (isVᴾ′ ∧ isVⱽ ∧ isVᴱ′)
  in proj₂ isVᴱ′′ ∧ isVᴾ′′ ∧ isVⱽ′

valid-invariant (Case₂ x₁ _ x₂) (isVᴾ ∧ isVᴱ) =
  let (isVᴱ′ ∧ isVᴾ′ ∧ isVⱽ) = valid-invariant x₁ (isVᴾ ∧ isVᴱ)
      (isVᴱ′′ ∧ isVᴾ′′ ∧ isVⱽ′) = valid-invariant x₂ (isVᴾ′ ∧ isVⱽ ∧ isVᴱ′)
  in proj₂ isVᴱ′′ ∧ isVᴾ′′ ∧ isVⱽ′

valid-invariant (Pair {v₁ = v₁} x₁ x₂) (isVᴾ ∧ isVᴱ) =
  let (isVᴱ′ ∧ isVᴾ′ ∧ isVⱽ) = valid-invariant x₁ (isVᴾ ∧ isVᴱ)
      (isVᴱ′′ ∧ isVᴾ′′ ∧ isVⱽ′) = valid-invariant x₂ (isVᴾ′ ∧ isVᴱ′)
  in isVᴱ′′ ∧ isVᴾ′′ ∧ (validⱽ-⊆ᴴ {v = v₁} (step-⊆ᴴ x₂) isVⱽ ∧ isVⱽ′)

valid-invariant (Fst x _) (isVᴾ ∧ isVᴱ) =
  let (isVᴱ′ ∧ isVᴾ′ ∧ (isVⱽ ∧ _)) = valid-invariant x (isVᴾ ∧ isVᴱ)
  in isVᴱ′ ∧ isVᴾ′ ∧ isVⱽ

valid-invariant (Snd x _) (isVᴾ ∧ isVᴱ) =
  let (isVᴱ′ ∧ isVᴾ′ ∧ (_ ∧ isVⱽ)) = valid-invariant x (isVᴾ ∧ isVᴱ)
  in isVᴱ′ ∧ isVᴾ′ ∧ isVⱽ

valid-invariant (LabelOf x) (isVᴾ ∧ isVᴱ) =
  let (isVᴱ′ ∧ isVᴾ′ ∧ _) = valid-invariant x (isVᴾ ∧ isVᴱ)
  in isVᴱ′ ∧ isVᴾ′ ∧ tt

valid-invariant GetLabel (isVᴾ ∧ isVᴱ) = isVᴱ ∧ isVᴾ ∧ tt

valid-invariant (Taint eq x₁ x₂ _) (isVᴾ ∧ isVᴱ) =
  let (isVᴱ′ ∧ isVᴾ′ ∧ isVⱽ) = valid-invariant x₁ (isVᴾ ∧ isVᴱ)
      (isVᴱ′′ ∧ isVᴾ′′ ∧ isVⱽ′) = valid-invariant x₂ (isVᴾ′ ∧ isVᴱ′)
  in isVᴱ′′ ∧ isVᴾ′′ ∧ isVⱽ′

valid-invariant (LabelOfRef x eq) (isVᴾ ∧ isVᴱ) =
  let (isVᴱ′ ∧ isVᴾ′ ∧ _) = valid-invariant x (isVᴾ ∧ isVᴱ)
  in isVᴱ′ ∧ isVᴾ′ ∧ tt

valid-invariant (New {μ' = μ'}  x) (isVᴾ ∧ isVᴱ) =
  let (isVᴱ′ ∧ ⟨ isVˢ , isVᴴ ⟩ ∧ isV) = valid-invariant x (isVᴾ ∧ isVᴱ)
  in isVᴱ′ ∧ ⟨ update-validˢ ∥ μ' ∥ᴴ isVˢ (snoc-validᴹ  ∥ μ' ∥ᴴ (isVˢ _) isV) , isVᴴ ⟩ ∧ tt

valid-invariant (Read {μ' = μ} x ∈₁ _) (isVᴾ ∧ isVᴱ) =
  let (isVᴱ′ ∧ ⟨ isVˢ , isVᴴ ⟩ ∧ isV) = valid-invariant x (isVᴾ ∧ isVᴱ)
  in isVᴱ′ ∧  ⟨ isVˢ , isVᴴ ⟩ ∧ read-validᴿ ∥ μ ∥ᴴ (isVˢ _) ∈₁

valid-invariant (Write {μ₃ = μ} x₁ _ x₂ _ w) (isVᴾ ∧ isVᴱ) =
  let (isVᴱ′ ∧ isVᴾ′ ∧ isV) = valid-invariant x₁ (isVᴾ ∧ isVᴱ)
      (isVᴱ′′ ∧ ⟨ isVˢ , isVᴴ ⟩ ∧ isVⱽ′) = valid-invariant x₂ (isVᴾ′ ∧ isVᴱ′)
  in isVᴱ′′ ∧ ⟨ update-validˢ ∥ μ ∥ᴴ  isVˢ (write-validᴹ ∥ μ ∥ᴴ (isVˢ _) w isVⱽ′) , isVᴴ ⟩ ∧ tt

valid-invariant (LabelOfRef-FS x _ _) (isVᴾ ∧ isVᴱ) =
  let (isVᴱ′ ∧ isVᴾ′ ∧ _) = valid-invariant x (isVᴾ ∧ isVᴱ)
  in isVᴱ′ ∧ isVᴾ′ ∧ tt

valid-invariant (New-FS {Σ' = Σ'} {μ' = μ'} {v = v} x) (isVᴾ ∧ isVᴱ) with valid-invariant x (isVᴾ ∧ isVᴱ)
... | (isVᴱ′ ∧ ⟨ isVˢ , isVᴴ ⟩ ∧ isV)
  = (validᴱ-⊆ᴴ ⊆₁ isVᴱ′) ∧ new-fs refl (sym eq) isV′ isVˢ′ isVᴴ ∧ ≤₁
  where eq = ∥snoc∥ μ' v
        ≤₁ : suc ∥ μ' ∥ᴴ ≤ ∥ snocᴴ μ' v ∥ᴴ
        ≤₁ rewrite eq = s≤s ≤-refl
        ⊆₁ = snoc-⊆ᴴ μ' v
        isVˢ′ : Validˢ (suc ∥ μ' ∥ᴴ) Σ'
        isVˢ′ = validˢ-⊆ᴴ (≤-step ≤-refl) isVˢ
        isV′ : Validⱽ (suc ∥ μ' ∥ᴴ) v
        isV′ = validⱽ-⊆ᴴ′ v (≤-step ≤-refl) isV

        new-fs : ∀ {μ n Σ τ} {v : Value τ} → n ≡ ∥ μ ∥ᴴ → suc n ≡ ∥ snocᴴ μ v ∥ᴴ →
                 Validⱽ (suc n) v → Validˢ (suc n) Σ → Validᴴ μ → Validᴾ ⟨ Σ , snocᴴ μ v ⟩
        new-fs {v = v} refl eq isV isVˢ isVᴴ with snoc-validᴴ′ {v = v} isVᴴ isV
        ... | isV′ rewrite eq = ⟨ isVˢ , isV′ ⟩

valid-invariant (Read-FS {μ' = μ} x ∈₁ _) (isVᴾ ∧ isVᴱ) =
  let (isVᴱ′ ∧ ⟨ isVˢ , isVᴴ ⟩ ∧ isV) = valid-invariant x (isVᴾ ∧ isVᴱ)
  in isVᴱ′ ∧  ⟨ isVˢ , isVᴴ ⟩ ∧ read-validⱽ ∥ μ ∥ᴴ isVᴴ ∈₁

valid-invariant (Write-FS {μ₃' = μ} x₁ x₂ _ _ _ w) (isVᴾ ∧ isVᴱ) with valid-invariant x₁ (isVᴾ ∧ isVᴱ)
... | isVᴱ′ ∧ isVᴾ′ ∧ isV with  valid-invariant x₂ (isVᴾ′ ∧ isVᴱ′)
... | isVᴱ′′ ∧ ⟨ isVˢ , isVᴴ ⟩ ∧ isVⱽ′ with write-length-≡ w
... | eq rewrite sym eq =  isVᴱ′′ ∧ ⟨ isVˢ , write-validᴴ ∥ μ ∥ᴴ isVᴴ w isVⱽ′ ⟩ ∧ tt

valid-invariant (Id x) (isVᴾ ∧ isVᴱ) =
  let (isVᴱ′ ∧ isVᴾ′ ∧ isVⱽ) = valid-invariant x (isVᴾ ∧ isVᴱ)
  in isVᴱ′ ∧ isVᴾ′ ∧ isVⱽ

valid-invariant (UnId x _) (isVᴾ ∧ isVᴱ) =
  let (isVᴱ′ ∧ isVᴾ′ ∧ isVⱽ) = valid-invariant x (isVᴾ ∧ isVᴱ)
  in isVᴱ′ ∧ isVᴾ′ ∧ isVⱽ

validᴾ-⇓ : ∀ {τ Γ ℓ} {θ : Env Γ} {c : IConf Γ τ} {c' : FConf τ} →
                              c ⇓⟨ θ , ℓ ⟩ c' →
                              Valid-Inputs c θ → Validᴾ ⟨ store c' , heap c' ⟩
validᴾ-⇓ x vi with valid-invariant x vi
... | _ ∧ isV ∧ _ = isV

-- postulate valid-invariant′ : ∀ {τ Γ ℓ} {θ : Env Γ} {c : IConf Γ τ} {c' : FConf τ} →
--                               c ⇓⟨ θ , ℓ ⟩ c' →
--                               Valid-Inputs c θ → Valid-Outputs′ c'

-- postulate valid-invariant′ : ∀ {τ Γ ℓ} {θ : Env Γ} {c : IConf Γ τ} {c' : FConf τ} →
--                               c ⇓⟨ θ , ℓ ⟩ c' →
--                               Valid-Inputs c θ → Valid-Outputs c'

-- -- Validᶜ c'

--   -- postulate validⱽ-⇓ :  ∀ {τ Γ ℓ} {θ : Env Γ} {c : IConf Γ τ} {c' : FConf τ} →

--   --                             c ⇓⟨ θ , ℓ ⟩ c' →
--   --                             Valid-Inputs c θ → Validᴱ (store c') θ

-- import Generic.Store Ty Raw as S


-- -- Do we need this?
-- postulate step-≤ : ∀ {τ Γ ℓ} {θ : Env Γ} {c : IConf Γ τ} {c' : FConf τ} →
--                               c ⇓⟨ θ , ℓ ⟩ c' → ∥ store c ∥ ≤ ∥ store c' ∥

-- record _⇓⟨_,_⟩ⱽ_ {Γ τ} (c : IConf Γ τ) (θ : Env Γ) (pc : Label) (c' : FConf τ) : Set where
--   constructor ⟨_,_,_⟩
--   field
--     step : c ⇓⟨ θ , pc ⟩ c'
--     validᴵ : Validᴾ ⟨ store c , heap c ⟩
--     validᴱ : Validᴱ ∥ heap c ∥ᴴ θ
--     validᶠ : Valid-Outputs
