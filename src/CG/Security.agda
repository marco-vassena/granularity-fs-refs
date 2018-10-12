-- This module proves security of CG i.e., termination-insensitive
-- non-interference (TINI).  The proof consists in showing that the
-- big-step semantics preserves L-equivalence.
--
-- This module is parametric in the security lattice 𝑳 = (𝓛, ⊑) and in
-- the attacker's security A ∈ 𝓛.

open import Lattice

module CG.Security {{𝑳 : Lattice}} (A : Label) where

open import Data.Empty
open import CG.Types
open import CG.Syntax
open import CG.Semantics
open import CG.LowEq A public
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

--------------------------------------------------------------------------------
-- Lemmas on L-equivalent environments.

-- Lookup in L-equivalent envs gives L-equivalent values
lookup-≈ⱽ : ∀ {τ Γ θ₁ θ₂} → (τ∈Γ : τ ∈ Γ) → θ₁ ≈ᴱ θ₂ → (θ₁ !! τ∈Γ) ≈ⱽ (θ₂ !! τ∈Γ)
lookup-≈ⱽ {θ₁ = v₁ ∷ θ₁} {v₂ ∷ θ₂} here (v₁≈v₂ ∷ θ₁≈θ₂) = v₁≈v₂
lookup-≈ⱽ {θ₁ = v₁ ∷ θ₁} {v₂ ∷ θ₂} (there τ∈Γ) (v₁≈v₂ ∷ θ₁≈θ₂) = lookup-≈ⱽ τ∈Γ θ₁≈θ₂

-- Slicing L-equivalent envs gives gives L-equivalent envs.
slice-≈ᴱ : ∀ {Γ₁ Γ₂} {θ₁ θ₂ : Env Γ₂} →
                 θ₁ ≈ᴱ θ₂ →
                 (Γ₁⊆Γ₂ : Γ₁ ⊆ Γ₂) →
                 slice θ₁ Γ₁⊆Γ₂ ≈ᴱ slice θ₂ Γ₁⊆Γ₂
slice-≈ᴱ [] base = []
slice-≈ᴱ (v₁≈v₂ ∷ θ₁≈θ₂) (cons p) = v₁≈v₂ ∷ slice-≈ᴱ θ₁≈θ₂ p
slice-≈ᴱ (v₁≈v₂ ∷ θ₁≈θ₂) (drop p) = slice-≈ᴱ θ₁≈θ₂ p

--------------------------------------------------------------------------------
mutual

  -- High forcing steps preserve low-equivalence of stores
  stepᶠ-≈ˢ : ∀ {τ Γ θ} {c : EConf Γ (LIO τ)} {c' : FConf τ} →
               let ⟨ Σ , pc , e ⟩ = c
                   ⟨ Σ' , _ , _ ⟩ = c' in
                 c ⇓ᶠ⟨ θ ⟩ c' →
                 pc ⋤ A →
                 Σ ≈ˢ Σ'
  stepᶠ-≈ˢ (Force x x₁) pc⋤A = step-≈ˢ x₁ pc⋤A

  -- High steps preserve low-equivalence of stores
  step-≈ˢ : ∀ {τ Γ θ} {c : TConf Γ (LIO τ)} {c' : FConf τ} →
               let ⟨ Σ , pc , t ⟩ = c
                   ⟨ Σ' , _ , _ ⟩ = c' in
                 c ⇓⟨ θ ⟩ c' →
                 pc ⋤ A →
                 Σ ≈ˢ Σ'
  step-≈ˢ (Return x) pc⋤A = refl-≈ˢ
  step-≈ˢ (Bind x x₁) pc⋤A = trans-≈ˢ (stepᶠ-≈ˢ x pc⋤A) (stepᶠ-≈ˢ x₁ (trans-⋤ (stepᶠ-⊑ x) pc⋤A))
  step-≈ˢ (Unlabel x eq) pc⋤A = refl-≈ˢ
  step-≈ˢ (ToLabeled x) pc⋤A = stepᶠ-≈ˢ x pc⋤A
  step-≈ˢ (LabelOf x x₁) pc⋤A = refl-≈ˢ
  step-≈ˢ GetLabel pc⋤A = refl-≈ˢ
  step-≈ˢ (Taint x x₁) pc⋤A = refl-≈ˢ
  step-≈ˢ (New x pc⊑ℓ) pc⋤A = updateᴴ-≈ˢ _ _ (trans-⋤ pc⊑ℓ pc⋤A)
  step-≈ˢ (Read x n∈M eq) pc⋤A = refl-≈ˢ
  step-≈ˢ (Write x x₁ pc⊑ℓ x₃ up) pc⋤A = updateᴴ-≈ˢ _ _ (trans-⋤ pc⊑ℓ pc⋤A)
  step-≈ˢ (LabelOfRef x eq) pc⋤A = refl-≈ˢ


--------------------------------------------------------------------------------
-- TINI for pure reductions

tiniᴾ : ∀ {τ Γ θ₁ θ₂ v₁ v₂} {e : Expr Γ τ} →
         e ⇓ᴾ⟨ θ₁ ⟩ v₁ →
         e ⇓ᴾ⟨ θ₂ ⟩ v₂ →
         θ₁ ≈ᴱ θ₂ →
         v₁ ≈ⱽ v₂
tiniᴾ Unit Unit θ₁≈θ₂ = Unit
tiniᴾ (Lbl ℓ) (Lbl .ℓ) θ₁≈θ₂ = Lbl ℓ
tiniᴾ (Wken p x) (Wken .p x₁) θ₁≈θ₂ = tiniᴾ x x₁ (slice-≈ᴱ θ₁≈θ₂ p)
tiniᴾ (Var τ∈Γ) (Var .τ∈Γ) θ₁≈θ₂ = lookup-≈ⱽ τ∈Γ θ₁≈θ₂
tiniᴾ SThunk SThunk θ₁≈θ₂ = Thunk′ θ₁≈θ₂
tiniᴾ Fun Fun θ₁≈θ₂ = Fun θ₁≈θ₂
tiniᴾ (App x x₁ x₂) (App x₃ x₄ x₅) θ₁≈θ₂ with tiniᴾ x x₃ θ₁≈θ₂
... | Fun θ₁'≈θ₂'  with tiniᴾ x₁ x₄ θ₁≈θ₂
... | v₁≈v₂ = tiniᴾ x₂ x₅ (v₁≈v₂ ∷ θ₁'≈θ₂')
tiniᴾ (Inl x) (Inl x₁) θ₁≈θ₂ = Inl (tiniᴾ x x₁ θ₁≈θ₂)
tiniᴾ (Inr x) (Inr x₁) θ₁≈θ₂ = Inr (tiniᴾ x x₁ θ₁≈θ₂)
tiniᴾ (Case₁ x x₁) (Case₁ x₂ x₃) θ₁≈θ₂ with tiniᴾ x x₂ θ₁≈θ₂
tiniᴾ (Case₁ x x₁) (Case₁ x₂ x₃) θ₁≈θ₂ | Inl v₁≈v₂ = tiniᴾ x₁ x₃ (v₁≈v₂ ∷ θ₁≈θ₂)
tiniᴾ (Case₁ x x₁) (Case₂ x₂ x₃) θ₁≈θ₂ with tiniᴾ x x₂ θ₁≈θ₂
tiniᴾ (Case₁ x x₁) (Case₂ x₂ x₃) θ₁≈θ₂ | ()
tiniᴾ (Case₂ x x₁) (Case₁ x₂ x₃) θ₁≈θ₂ with tiniᴾ x x₂ θ₁≈θ₂
tiniᴾ (Case₂ x x₁) (Case₁ x₂ x₃) θ₁≈θ₂ | ()
tiniᴾ (Case₂ x x₁) (Case₂ x₂ x₃) θ₁≈θ₂ with tiniᴾ x x₂ θ₁≈θ₂
tiniᴾ (Case₂ x x₁) (Case₂ x₂ x₃) θ₁≈θ₂ | Inr v₁≈v₂ = tiniᴾ x₁ x₃ (v₁≈v₂ ∷ θ₁≈θ₂)
tiniᴾ (Pair x x₁) (Pair x₂ x₃) θ₁≈θ₂ = Pair (tiniᴾ x x₂ θ₁≈θ₂) (tiniᴾ x₁ x₃ θ₁≈θ₂)
tiniᴾ (Fst x) (Fst x₁) θ₁≈θ₂ with tiniᴾ x x₁ θ₁≈θ₂
tiniᴾ (Fst x) (Fst x₁) θ₁≈θ₂ | Pair v₁≈v₁' v₂≈v₂' = v₁≈v₁'
tiniᴾ (Snd x) (Snd x₁) θ₁≈θ₂ with tiniᴾ x x₁ θ₁≈θ₂
tiniᴾ (Snd x) (Snd x₁) θ₁≈θ₂ | Pair v₁≈v₂ v₁≈v₃ = v₁≈v₃

--------------------------------------------------------------------------------

mutual

  -- TINI for low steps
  tiniᴸ : ∀ {pc τ Γ Σ₁ Σ₂ θ₁ θ₂} {t : Thunk Γ (LIO τ)} {c₁' c₂' : FConf τ} →
           ⟨ Σ₁ , pc , t ⟩ ⇓⟨ θ₁ ⟩ c₁' →
           ⟨ Σ₂ , pc , t ⟩ ⇓⟨ θ₂ ⟩ c₂' →
           Σ₁ ≈ˢ Σ₂ →
           θ₁ ≈ᴱ θ₂ →
           pc ⊑ A →
           c₁' ≈ᶜ c₂'

  tiniᴸ (Return x) (Return x₁) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A = pcᴸ Σ₁≈Σ₂ pc⊑A (tiniᴾ x x₁ θ₁≈θ₂)

  tiniᴸ (Bind x x₁) (Bind x₂ x₃) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A  with tiniᶠ x x₂ ⟨ Σ₁≈Σ₂ , refl , refl ⟩ θ₁≈θ₂
  ... | pcᴸ Σ₁'≈Σ₂' pc'⊑A v₁≈v₂ = tiniᶠ x₁ x₃ ⟨ Σ₁'≈Σ₂' , refl , refl ⟩ (v₁≈v₂ ∷ θ₁≈θ₂)
  ... | pcᴴ Σ₁'≈Σ₂' pc₁'⋤A pc₂'⋤A = tiniᶠᴴ x₁ x₃ Σ₁'≈Σ₂' pc₁'⋤A pc₂'⋤A

  tiniᴸ (Unlabel x refl) (Unlabel x₁ refl) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A with tiniᴾ x x₁ θ₁≈θ₂
  ... | Labeledᴸ ℓ⊑A r = pcᴸ Σ₁≈Σ₂ (join-⊑' pc⊑A ℓ⊑A) r
  ... | Labeledᴴ pc₁'⋤A pc₂'⋤A = pcᴴ Σ₁≈Σ₂ (trans-⋤ (join-⊑₂ _ _) pc₁'⋤A) ((trans-⋤ (join-⊑₂ _ _) pc₂'⋤A))

  tiniᴸ (ToLabeled x) (ToLabeled x₁) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A with tiniᶠ x x₁ ⟨ Σ₁≈Σ₂ , refl , refl ⟩ θ₁≈θ₂
  ... | pcᴸ Σ₁'≈Σ₂' pc⊑A' v₁≈v₂ = pcᴸ Σ₁'≈Σ₂' pc⊑A (Labeledᴸ pc⊑A' v₁≈v₂)
  ... | pcᴴ Σ₁'≈Σ₂' pc₁'⋤A pc₂'⋤A = pcᴸ Σ₁'≈Σ₂' pc⊑A (Labeledᴴ pc₁'⋤A pc₂'⋤A)

  tiniᴸ (LabelOf x refl) (LabelOf x₂ refl) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A with tiniᴾ x x₂ θ₁≈θ₂
  ... | Labeledᴸ ℓ⊑A r = pcᴸ Σ₁≈Σ₂ (join-⊑' pc⊑A ℓ⊑A) (Lbl _)
  ... | Labeledᴴ ℓ⋤A ℓ₁⋤A = pcᴴ Σ₁≈Σ₂ (join-⋤₂ ℓ⋤A) (join-⋤₂ ℓ₁⋤A)

  tiniᴸ GetLabel GetLabel Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A = pcᴸ Σ₁≈Σ₂ pc⊑A (Lbl _)

  tiniᴸ {pc = pc} (Taint x refl) (Taint x₂ refl) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A with tiniᴾ x x₂ θ₁≈θ₂
  ... | Lbl ℓ with (pc ⊔ ℓ) ⊑? A
  ... | yes pc'⊑A = pcᴸ Σ₁≈Σ₂ pc'⊑A Unit
  ... | no pc'⋤A = pcᴴ Σ₁≈Σ₂ pc'⋤A pc'⋤A

  tiniᴸ (New x x₁) (New x₂ x₃) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A with tiniᴾ x x₂ θ₁≈θ₂
  ... | Labeledᴸ ℓ⊑A v₁≈v₂ = pcᴸ Σ₁'≈Σ₂' pc⊑A r₁≈r₂
    where M₁≈M₂ = getᴸ Σ₁≈Σ₂ ℓ⊑A
          r₁≈r₂ = Refᴸ′ ℓ⊑A ∥ M₁≈M₂ ∥-≡
          Σ₁'≈Σ₂' = updateᴸ-≈ˢ Σ₁≈Σ₂ (new-≈ᴹ M₁≈M₂ v₁≈v₂)
  ... | Labeledᴴ ℓ₁⋤A ℓ₂⋤A  = pcᴸ Σ₁'≈Σ₂' pc⊑A r₁≈r₂
    where r₁≈r₂ = Refᴴ ℓ₁⋤A ℓ₂⋤A
          Σ₁'≈Σ₂' = square-≈ˢ Σ₁≈Σ₂ (updateᴴ-≈ˢ _ _ ℓ₁⋤A) (updateᴴ-≈ˢ _ _ ℓ₂⋤A)

  tiniᴸ (Read x₁ n∈M₁ refl) (Read x₂ n∈M₂ refl) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A with tiniᴾ x₁ x₂ θ₁≈θ₂
  ... | Refᴸ ℓ⊑A n = pcᴸ Σ₁≈Σ₂ (join-⊑' pc⊑A ℓ⊑A) (read-≈ᴹ (getᴸ Σ₁≈Σ₂ ℓ⊑A) n∈M₁ n∈M₂)
  ... | Refᴴ ℓ₁⋤A ℓ₂⋤A = pcᴴ Σ₁≈Σ₂ (trans-⋤ (join-⊑₂ _ _) ℓ₁⋤A) (trans-⋤ (join-⊑₂ _ _) ℓ₂⋤A)

  tiniᴸ (Write x₁ x₂ pc⊑ℓ₁ ℓ'⊑ℓ₁ u₁) (Write x₁' x₂' pc⊑ℓ₂ ℓ''⊑ℓ₂ u₂) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
    with tiniᴾ x₁ x₁' θ₁≈θ₂ | tiniᴾ x₂ x₂' θ₁≈θ₂
  ... | Refᴴ ℓ₁⋤A ℓ₂⋤A | v₁≈v₂ = pcᴸ Σ₁'≈Σ₂' pc⊑A Unit
    where Σ₁'≈Σ₂' = square-≈ˢ Σ₁≈Σ₂ (updateᴴ-≈ˢ _ _ ℓ₁⋤A) (updateᴴ-≈ˢ _ _ ℓ₂⋤A)
  ... | Refᴸ ℓ⊑A n | Labeledᴴ ℓ'⋤A ℓ''⋤A  = ⊥-elim (trans-⋤ ℓ'⊑ℓ₁ ℓ'⋤A ℓ⊑A)
  ... | Refᴸ ℓ⊑A n | Labeledᴸ x v₁≈v₂ = pcᴸ Σ₁'≈Σ₂' pc⊑A Unit
    where Σ₁'≈Σ₂' = updateᴸ-≈ˢ Σ₁≈Σ₂ (update-≈ᴹ (getᴸ Σ₁≈Σ₂ ℓ⊑A) v₁≈v₂ u₁ u₂)

  tiniᴸ (LabelOfRef x refl) (LabelOfRef x₁ refl) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A with tiniᴾ x x₁ θ₁≈θ₂
  ... | Refᴸ ℓ⊑A n = pcᴸ Σ₁≈Σ₂ (join-⊑' pc⊑A ℓ⊑A) (Lbl _)
  ... | Refᴴ ℓ₁⋤A ℓ₂⋤A = pcᴴ Σ₁≈Σ₂ (trans-⋤ (join-⊑₂ _ _) ℓ₁⋤A) (trans-⋤ (join-⊑₂ _ _) ℓ₂⋤A)

  -- TINI for high-forcing steps
  tiniᶠᴴ : ∀ {τ Γ₁ Γ₂ θ₁ θ₂} {c₁ : EConf Γ₁ (LIO τ)} {c₂ : EConf Γ₂ (LIO τ)} {c₁' c₂' : FConf τ} →
           let ⟨ Σ₁ , pc₁ , t₁ ⟩ = c₁
               ⟨ Σ₂ , pc₂ , t₂ ⟩ = c₂ in
           c₁ ⇓ᶠ⟨ θ₁ ⟩ c₁' →
           c₂ ⇓ᶠ⟨ θ₂ ⟩ c₂' →
           Σ₁ ≈ˢ Σ₂ →
           pc₁ ⋤ A →
           pc₂ ⋤ A →
           c₁' ≈ᶜ c₂'
  tiniᶠᴴ (Force x x₁) (Force x₂ x₃) = tiniᴴ x₁ x₃


  -- TINI for high steps. The computations depend on a secret and thus
  -- might produce different results and code. We then prove TINI by
  -- showing that the program counter can only remain secret and that
  -- each high step preserves low-equivalence of stores.  In
  -- particular we proce that the final stores are low-equivalent (Σ₁'
  -- ≈ Σ₂'), i.e., the square:
  --
  -- Σ₁ ≈ˢ Σ₁'
  -- ≈ˢ    ≈ˢ
  -- Σ₂ ≈ˢ Σ₂'
  --
  -- using transitivity and symmetry of ≈ˢ
  tiniᴴ : ∀ {τ Γ₁ Γ₂ θ₁ θ₂} {c₁ : TConf Γ₁ (LIO τ)} {c₂ : TConf Γ₂ (LIO τ)} {c₁' c₂' : FConf τ} →
           let ⟨ Σ₁ , pc₁ , t₁ ⟩ = c₁
               ⟨ Σ₂ , pc₂ , t₂ ⟩ = c₂ in
           c₁ ⇓⟨ θ₁ ⟩ c₁' →
           c₂ ⇓⟨ θ₂ ⟩ c₂' →
           Σ₁ ≈ˢ Σ₂ →
           pc₁ ⋤ A →
           pc₂ ⋤ A →
           c₁' ≈ᶜ c₂'
  tiniᴴ x₁ x₂ Σ₁≈Σ₂ pc₁⋤A pc₂⋤A = pcᴴ Σ₁'≈Σ₂' (trans-⋤ (step-⊑ x₁) pc₁⋤A) (trans-⋤ (step-⊑ x₂) pc₂⋤A)
    where Σ₁≈Σ₁' = step-≈ˢ x₁ pc₁⋤A
          Σ₂≈Σ₂' = step-≈ˢ x₂ pc₂⋤A
          Σ₁'≈Σ₂' = square-≈ˢ Σ₁≈Σ₂ Σ₁≈Σ₁' Σ₂≈Σ₂'

  --------------------------------------------------------------------------------
  -- TINI (top-level theorems) for thunk and forcing semantics.

  tini : ∀ {τ Γ θ₁ θ₂} {c₁ c₂ : TConf Γ (LIO τ)} {c₁' c₂' : FConf τ} →
           c₁ ⇓⟨ θ₁ ⟩ c₁' →
           c₂ ⇓⟨ θ₂ ⟩ c₂' →
           c₁ ≈ᵀ c₂ →
           θ₁ ≈ᴱ θ₂ →
           c₁' ≈ᶜ c₂'
  tini {c₁ = ⟨ _ , pc , _ ⟩} x₁ x₂ ⟨ Σ₁≈Σ₂ , refl , refl ⟩ θ₁≈θ₂ with pc ⊑? A
  ... | yes pc⊑A = tiniᴸ x₁ x₂ Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
  ... | no pc⋤A = tiniᴴ x₁ x₂ Σ₁≈Σ₂ pc⋤A pc⋤A

  tiniᶠ : ∀ {τ Γ θ₁ θ₂} {c₁ c₂ : EConf Γ (LIO τ)} {c₁' c₂' : FConf τ} →
           c₁ ⇓ᶠ⟨ θ₁ ⟩ c₁' →
           c₂ ⇓ᶠ⟨ θ₂ ⟩ c₂' →
           c₁ ≈ᴵ c₂ →
           θ₁ ≈ᴱ θ₂ →
           c₁' ≈ᶜ c₂'
  tiniᶠ (Force x x₁) (Force x₂ x₃) ⟨ Σ≈ , refl , refl ⟩ θ₁≈θ₂ with tiniᴾ x x₂ θ₁≈θ₂
  ... | Thunk′ θ₁≈θ₂' = tini x₁ x₃ ⟨ Σ≈ , refl , refl ⟩ θ₁≈θ₂'
