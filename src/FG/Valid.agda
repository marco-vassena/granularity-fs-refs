open import Lattice

module FG.Valid {{𝑳 : Lattice}} where

open import FG.Types hiding (_×_) renaming ( _⊆_ to  _⊆ᶜ_) --  (Ty ; _⊆_ ; I ; S)
open import FG.Syntax
open import Data.Product as P hiding (_,_)
open import Data.Nat renaming (_⊔_ to _⊔ᴺ_) hiding (_^_)
open import Data.Unit hiding (_≤_)

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
  ∥ Refᴵ x n ∥ᴿ = ℕ.suc n
  ∥ Refˢ n ∥ᴿ = ℕ.suc n
  ∥ ⌞ x ⌟ ∥ᴿ = 0
  ∥ Id x ∥ᴿ = ∥ x ∥ⱽ

  ∥_∥ᴱ : ∀ {Γ} → Env Γ → ℕ
  ∥ [] ∥ᴱ = 0
  ∥ v ∷ θ ∥ᴱ = ∥ v ∥ⱽ ⊔ᴺ ∥ θ ∥ᴱ

-- Needed?
mutual

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
  Validᴿ {τ} n (Refˢ m) = ⊤ -- This does not seem to be needed. Answer: It will be needed when we prove the invariant!
  Validᴿ n ⌞ ℓ ⌟ = ⊤
  Validᴿ n (Id v) = Validⱽ n v

  Validⱽ : ∀ {τ} → ℕ → Value τ → Set
  Validⱽ n (r ^ ℓ) = Validᴿ n r

-- -- TODO: If we split the store for FS from FI all these definitions can be substituted by ∥ v ∥ ≤ ∥ Σ ∥

open Conf
-- open import Generic.Heap.Valid Ty Value ∥_∥ⱽ public
-- open import Generic.Store.Valid Ty Raw ∥_∥ᴿ public

-- record Valid-Conf (A : Set) (Validᵗ : A → Set) (c : Conf A) : Set where
--   constructor ⟨_,_⟩
--   field
--     validˢ : Validˢ (store c)
--     validᵗ : Validᵗ (term c)

-- open Valid-Conf {{...}} public

-- Validᴵ : ∀ {Γ τ} → IConf Γ τ → Set
-- Validᴵ c = Validˢ (store c)
-- Valid-Conf (Expr _ _) (λ _ → ⊤) c

-- Validᶜ : ∀ {τ} → FConf τ → Set
-- Validᶜ c = Valid-Conf (Value _) (Validⱽ ∥ store c ∥) c

open import FG.Semantics

open import Generic.PState.Base Ty Ty Raw Value
open import Generic.PState.Valid {Ty} {Ty} {Raw} {Value} ∥_∥ᴿ ∥_∥ⱽ public

record Valid-Inputs {Γ} {τ} (c : IConf Γ τ) (θ : Env Γ) : Set where
  constructor ⟨_,_⟩
  field
    validᴾ : Validᴾ ⟨ store c , heap c ⟩
    validᴱ : Validᴱ ∥ heap c ∥ᴴ θ

--  open Validᴾ

-- open Valid-Inputs {{...}} public

Valid-Outputs : ∀ {τ} → FConf τ → Set
Valid-Outputs ⟨ Σ , μ , v ⟩ = Validᴾ ⟨ Σ , μ ⟩ × Validⱽ ∥ μ ∥ᴴ v


record Valid-Outputs′ {τ} (c : FConf τ) : Set where
  constructor ⟨_,_⟩
  field
    validᴾ : Validᴾ ⟨ store c , heap c ⟩
    validⱽ : Validⱽ ∥ heap c ∥ᴴ (term c)

-- open Valid-Outputs′ {{...}} public

-- record Valid-Outputs {τ} (c : FConf τ) : Set where
--   constructor ⟨_,_⟩
--   field
--     validᴾ : Validᴾ ⟨ store c , heap c ⟩
--     validⱽ : Validⱽ ∥ heap c ∥ᴴ (term c)


-- TODO: prove
postulate valid-invariant : ∀ {τ Γ ℓ} {θ : Env Γ} {c : IConf Γ τ} {c' : FConf τ} →
                              c ⇓⟨ θ , ℓ ⟩ c' →
                              Valid-Inputs c θ → Validᴱ ∥ heap c' ∥ᴴ θ × Valid-Outputs c'

-- postulate valid-invariant′ : ∀ {τ Γ ℓ} {θ : Env Γ} {c : IConf Γ τ} {c' : FConf τ} →
--                               c ⇓⟨ θ , ℓ ⟩ c' →
--                               Valid-Inputs c θ → Valid-Outputs′ c'

postulate validᴾ-⇓ : ∀ {τ Γ ℓ} {θ : Env Γ} {c : IConf Γ τ} {c' : FConf τ} →
                              c ⇓⟨ θ , ℓ ⟩ c' →
                              Valid-Inputs c θ → Validᴾ ⟨ store c' , heap c' ⟩

postulate valid-lookup : ∀ {τ Γ θ n} → (τ∈Γ : τ ∈ Γ) → Validᴱ n θ → Validⱽ n (θ !! τ∈Γ )

-- postulate valid-invariant′ : ∀ {τ Γ ℓ} {θ : Env Γ} {c : IConf Γ τ} {c' : FConf τ} →
--                               c ⇓⟨ θ , ℓ ⟩ c' →
--                               Valid-Inputs c θ → Valid-Outputs c'

-- -- Validᶜ c'

--   -- postulate validⱽ-⇓ :  ∀ {τ Γ ℓ} {θ : Env Γ} {c : IConf Γ τ} {c' : FConf τ} →

--   --                             c ⇓⟨ θ , ℓ ⟩ c' →
--   --                             Valid-Inputs c θ → Validᴱ (store c') θ

-- import Generic.Store Ty Raw as S

-- TODO: maybe it'd be more convenient to take the big-step in the main proof
-- and use these in this module
postulate validᴿ-⊆ᴴ : ∀ {τ μ μ'} {r : Raw τ} → μ ⊆ᴴ μ' → Validᴿ ∥ μ ∥ᴴ r → Validᴿ ∥ μ' ∥ᴴ r

postulate validⱽ-⊆ᴴ : ∀ {τ μ μ'} {v : Value τ} → μ ⊆ᴴ μ' → Validⱽ ∥ μ ∥ᴴ v → Validⱽ ∥ μ' ∥ᴴ v

postulate validᴱ-⊆ᴴ : ∀ {Γ μ μ'} {θ : Env Γ} → μ ⊆ᴴ μ' → Validᴱ ∥ μ ∥ᴴ θ → Validᴱ ∥ μ' ∥ᴴ θ

postulate validᴱ-⊆ᶜ : ∀ {Γ Γ' μ} {θ : Env Γ} → (p : Γ' ⊆ᶜ Γ) → Validᴱ ∥ μ ∥ᴴ θ → Validᴱ ∥ μ ∥ᴴ (slice θ p)

postulate validˢ-⊆ᴴ : ∀ {Σ μ μ'} → μ ⊆ᴴ μ' → Validˢ ∥ μ ∥ᴴ Σ → Validˢ ∥ μ' ∥ᴴ Σ

-- -- Do we need this?
-- postulate step-≤ : ∀ {τ Γ ℓ} {θ : Env Γ} {c : IConf Γ τ} {c' : FConf τ} →
--                               c ⇓⟨ θ , ℓ ⟩ c' → ∥ store c ∥ ≤ ∥ store c' ∥
postulate step-⊆ᴴ :  ∀ {τ Γ θ pc} {c : IConf Γ τ} {c' : FConf τ} → c ⇓⟨ θ , pc ⟩ c' → (heap c) ⊆ᴴ (heap c')

-- record _⇓⟨_,_⟩ⱽ_ {Γ τ} (c : IConf Γ τ) (θ : Env Γ) (pc : Label) (c' : FConf τ) : Set where
--   constructor ⟨_,_,_⟩
--   field
--     step : c ⇓⟨ θ , pc ⟩ c'
--     validᴵ : Validᴾ ⟨ store c , heap c ⟩
--     validᴱ : Validᴱ ∥ heap c ∥ᴴ θ
--     validᶠ : Valid-Outputs
