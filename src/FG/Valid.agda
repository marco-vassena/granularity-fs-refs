open import Lattice

module FG.Valid {{𝑳 : Lattice}} where

open import FG.Types using (Ty ; _⊆_ ; I ; S)
open import FG.Syntax
open import Data.Product as P
open import Data.Nat renaming (_⊔_ to _⊔ᴺ_)
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

  Validᴱ : ∀ {Γ} → Store → Env Γ → Set
  Validᴱ Σ [] = ⊤
  Validᴱ Σ (v ∷ θ) = Validⱽ Σ v × Validᴱ Σ θ

  Validᴿ : ∀ {τ} → Store → Raw τ → Set
  Validᴿ Σ （） = ⊤
  Validᴿ Σ ⟨ x , θ ⟩ᶜ = Validᴱ Σ θ
  Validᴿ Σ (inl v) = Validⱽ Σ v
  Validᴿ Σ (inr v) = Validⱽ Σ v
  Validᴿ Σ ⟨ v₁ , v₂ ⟩ = Validⱽ Σ v₁ × Validⱽ Σ v₂
  -- TODO: there could be some (equivalent) alternatives.  E.g.,
  -- define a special (unlabelde) cell type for flow-insensitive
  -- references and ask that it has the right type.
  -- TODO: if we have a separate store do we need validity at all?
  -- Maybe just for the store?
  Validᴿ Σ (Refᴵ {τ = τ} ℓ m) = P.Σ (Raw τ) (λ v → m ↦ (v , ℓ) ∈ Σ )
  -- TODO: should I have any requirement on the label of the cell for flow-sensitve refs?
  Validᴿ {τ} Σ (Refˢ m) = ⊤ -- P.Σ (Cell τ) (λ c → m ↦ c ∈ Σ) -- Probably this is not needed.
  Validᴿ Σ ⌞ ℓ ⌟ = ⊤
  Validᴿ Σ (Id v) = Validⱽ Σ v

  Validⱽ : ∀ {τ} → Store → Value τ → Set
  Validⱽ Σ (r ^ ℓ) = Validᴿ Σ r

-- TODO: If we split the store for FS from FI all these definitions can be substituted by ∥ v ∥ ≤ ∥ Σ ∥

open Conf
open import Generic.Store.Valid Ty Raw ∥_∥ᴿ hiding (Validᶜ)

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

record Valid-Inputs {Γ} {τ} (c : IConf Γ τ) (θ : Env Γ) : Set where
  constructor ⟨_,_⟩
  field
    validˢ : Validˢ (store c)
    validᴱ : Validᴱ (store c) θ

-- open Valid-Inputs {{...}} public

Valid-Outputs : ∀ {τ} → FConf τ → Set
Valid-Outputs ⟨ Σ , v ⟩ = Validˢ Σ × Validⱽ Σ v

-- TODO: prove
instance
  postulate valid-invariant : ∀ {τ Γ ℓ} {θ : Env Γ} {c : IConf Γ τ} {c' : FConf τ} →
                              c ⇓⟨ θ , ℓ ⟩ c' →
                              Valid-Inputs c θ → Validᴱ (store c') θ × Valid-Outputs c'
-- Validᶜ c'

  -- postulate validⱽ-⇓ :  ∀ {τ Γ ℓ} {θ : Env Γ} {c : IConf Γ τ} {c' : FConf τ} →

  --                             c ⇓⟨ θ , ℓ ⟩ c' →
  --                             Valid-Inputs c θ → Validᴱ (store c') θ

import Generic.Store Ty Raw as S

postulate validᴿ-⊆ : ∀ {τ Σ Σ'} {r : Raw τ} → Σ S.⊆ Σ' → Validᴿ Σ r → Validᴿ Σ' r

postulate validⱽ-⊆ : ∀ {τ Σ Σ'} {v : Value τ} → Σ S.⊆ Σ' → Validⱽ Σ v → Validⱽ Σ' v

postulate validᴱ-⊆ : ∀ {Γ Σ Σ'} {θ : Env Γ} → Σ S.⊆ Σ' → Validᴱ Σ θ → Validᴱ Σ' θ

postulate validᴱ-⊆ᶜ : ∀ {Γ Γ' Σ} {θ : Env Γ} → (p : Γ' ⊆ Γ) → Validᴱ Σ θ → Validᴱ Σ (slice θ p)

-- Do we need this?
postulate step-≤ : ∀ {τ Γ ℓ} {θ : Env Γ} {c : IConf Γ τ} {c' : FConf τ} →
                              c ⇓⟨ θ , ℓ ⟩ c' → ∥ store c ∥ ≤ ∥ store c' ∥

postulate step-⊆ :  ∀ {τ Γ θ pc} {c : IConf Γ τ} {c' : FConf τ} →
               c ⇓⟨ θ , pc ⟩ c' → (store c) S.⊆ (store c')
