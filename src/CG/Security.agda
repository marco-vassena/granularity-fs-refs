-- This module proves security of CG i.e., termination-insensitive
-- non-interference (TINI).  The proof consists in showing that the
-- big-step semantics preserves L-equivalence.
--
-- This module is parametric in the security lattice 𝑳 = (𝓛, ⊑) and in
-- the attacker's security A ∈ 𝓛.

open import Lattice

module CG.Security {{𝑳 : Lattice}} (A : Label) where

open import Data.Empty
open import CG.Types hiding (_×_) renaming (_⊆_ to _⊆ᶜ_) hiding (refl-⊆)
open import CG.Syntax
open import CG.Semantics
open import CG.LowEq A public
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Generic.Bijection
open import Data.Product renaming (_,_ to _∧_) hiding (,_)

open import CG.Valid
open import Generic.Valid
open IsValid isValidᴱ
open Validᴾ

--------------------------------------------------------------------------------
-- Moved to CG.LowEq
-- Lemmas on L-equivalent environments.

-- Lookup in L-equivalent envs gives L-equivalent values
-- lookup-≈ⱽ : ∀ {τ Γ θ₁ θ₂} → (τ∈Γ : τ ∈ Γ) → θ₁ ≈ᴱ θ₂ → (θ₁ !! τ∈Γ) ≈ⱽ (θ₂ !! τ∈Γ)
-- lookup-≈ⱽ {θ₁ = v₁ ∷ θ₁} {v₂ ∷ θ₂} here (v₁≈v₂ ∷ θ₁≈θ₂) = v₁≈v₂
-- lookup-≈ⱽ {θ₁ = v₁ ∷ θ₁} {v₂ ∷ θ₂} (there τ∈Γ) (v₁≈v₂ ∷ θ₁≈θ₂) = lookup-≈ⱽ τ∈Γ θ₁≈θ₂

-- -- Slicing L-equivalent envs gives gives L-equivalent envs.
-- slice-≈ᴱ : ∀ {Γ₁ Γ₂} {θ₁ θ₂ : Env Γ₂} →
--                  θ₁ ≈ᴱ θ₂ →
--                  (Γ₁⊆Γ₂ : Γ₁ ⊆ Γ₂) →
--                  slice θ₁ Γ₁⊆Γ₂ ≈ᴱ slice θ₂ Γ₁⊆Γ₂
-- slice-≈ᴱ [] base = []
-- slice-≈ᴱ (v₁≈v₂ ∷ θ₁≈θ₂) (cons p) = v₁≈v₂ ∷ slice-≈ᴱ θ₁≈θ₂ p
-- slice-≈ᴱ (v₁≈v₂ ∷ θ₁≈θ₂) (drop p) = slice-≈ᴱ θ₁≈θ₂ p

--------------------------------------------------------------------------------
mutual

  -- High forcing steps preserve low-equivalence of stores
  stepᶠ-≈ᴾ : ∀ {τ Γ θ} {c : EConf Γ (LIO τ)} {c' : FConf τ} →
               let ⟨ Σ , μ , pc , e ⟩ = c
                   ⟨ Σ' , μ' , _ , _ ⟩ = c' in
               {{validᴾ : Validᴾ ⟨ Σ , μ ⟩ }} {{validᴱ : Validᴱ ∥ μ ∥ᴴ θ}} →
               c ⇓ᶠ⟨ θ ⟩ c' →
               pc ⋤ A →
               ⟨ Σ , μ ⟩ ≈⟨ ι ∥ μ ∥ᴴ ⟩ᴾ ⟨ Σ' , μ' ⟩
  stepᶠ-≈ᴾ {{isVᴾ}} {{isVᴱ}} (Force x y) pc⋤A = step-≈ᴾ {{isVᴾ}} {{ isVᴱ′ }} y pc⋤A
    where isVᴱ′ = validⱽ-⇓ᴾ x isVᴱ

  -- High steps preserve low-equivalence of stores
  step-≈ᴾ : ∀ {τ Γ θ} {c : TConf Γ (LIO τ)} {c' : FConf τ} →
               let ⟨ Σ , μ , pc , t ⟩ = c
                   ⟨ Σ' , μ' ,  _ , _ ⟩ = c' in
               {{validᴾ : Validᴾ ⟨ Σ , μ ⟩ }} {{validᴱ : Validᴱ ∥ μ ∥ᴴ θ}} →
               c ⇓⟨ θ ⟩ c' →
               pc ⋤ A →
               ⟨ Σ , μ ⟩ ≈⟨ ι ∥ μ ∥ᴴ ⟩ᴾ ⟨ Σ' , μ' ⟩
  step-≈ᴾ (Return x) pc⋤A = refl-≈ᴾ

  step-≈ᴾ {{isVᴾ}} {{isVᴱ}} (Bind x x₁) pc⋤A =
    let isVᴾ′ ∧ isVᴱ′′ = valid-⇓ᶠ x (isVᴾ ∧ isVᴱ)
        ≈ᴾ′ = stepᶠ-≈ᴾ x pc⋤A
        ≈ᴾ′′ = stepᶠ-≈ᴾ {{ isVᴾ′ }} {{ isVᴱ′′ }} x₁ (trans-⋤ (stepᶠ-⊑ x) pc⋤A)
    in trans-≈ᴾ-ι ≈ᴾ′ ≈ᴾ′′

  step-≈ᴾ (Unlabel x eq) pc⋤A = refl-≈ᴾ
  step-≈ᴾ (ToLabeled x) pc⋤A = stepᶠ-≈ᴾ x pc⋤A
  step-≈ᴾ (LabelOf x x₁) pc⋤A = refl-≈ᴾ
  step-≈ᴾ GetLabel pc⋤A = refl-≈ᴾ
  step-≈ᴾ (Taint x x₁) pc⋤A = refl-≈ᴾ

  step-≈ᴾ {{isVᴾ}} (New x pc⊑ℓ) pc⋤A = ⟨ ≈ˢ , ≈ᴴ ⟩
    where ≈ˢ = updateᴴ-≈ˢ {{ validˢ isVᴾ }} (trans-⋤ pc⊑ℓ pc⋤A)
          ≈ᴴ = refl-≈ᴴ {{ validᴴ isVᴾ }}

  step-≈ᴾ (Read x n∈M eq) pc⋤A = refl-≈ᴾ

  step-≈ᴾ {{isVᴾ}} (Write x x₁ pc⊑ℓ x₃ up) pc⋤A = ⟨ ≈ˢ , ≈ᴴ ⟩
    where ≈ˢ = updateᴴ-≈ˢ {{ validˢ isVᴾ }} (trans-⋤ pc⊑ℓ pc⋤A)
          ≈ᴴ = refl-≈ᴴ {{ validᴴ isVᴾ }}

  step-≈ᴾ (LabelOfRef x eq) pc⋤A = refl-≈ᴾ

  step-≈ᴾ {{isVᴾ}} (New-FS x x₁) pc⋤A = ⟨ ≈ˢ , ≈ᴴ ⟩
    where ≈ˢ = refl-≈ˢ {{ validˢ isVᴾ }}
          ≈ᴴ = snoc-≈ᴴ _ (refl-≈ᴴ {{validᴴ isVᴾ}} )

  step-≈ᴾ (Read-FS x n∈μ eq) pc⋤A = refl-≈ᴾ

  step-≈ᴾ {{isVᴾ}} (Write-FS x x₁ n∈μ ⊑₁ refl w) pc⋤A = ⟨ ≈ˢ , ≈ᴴ ⟩
    where ≈ˢ = refl-≈ˢ {{ validˢ isVᴾ }}
          v≈ = Labeledᴴ (trans-⋤ ⊑₁ pc⋤A) (join-⋤₁ pc⋤A)
          ≈ᴴ = writeᴴ-≈ᴴ {{ validᴴ isVᴾ }} n∈μ w v≈

  step-≈ᴾ (LabelOfRef-FS x n∈μ eq) pc⋤A = refl-≈ᴾ

--------------------------------------------------------------------------------
-- TINI for pure reductions

tiniᴾ : ∀ {τ Γ θ₁ θ₂ v₁ v₂ β} {e : Expr Γ τ} →
         e ⇓ᴾ⟨ θ₁ ⟩ v₁ →
         e ⇓ᴾ⟨ θ₂ ⟩ v₂ →
         θ₁ ≈⟨ β ⟩ᴱ θ₂ →
         v₁ ≈⟨ β ⟩ⱽ v₂
tiniᴾ Unit Unit θ₁≈θ₂ = Unit
tiniᴾ (Lbl ℓ) (Lbl .ℓ) θ₁≈θ₂ = Lbl ℓ
tiniᴾ (Test₁ _ _ ℓ₁⊑ℓ₂) (Test₁ _ _ _) _ = Inl Unit
tiniᴾ (Test₂ x₁ x₂ ℓ₁⋤ℓ₂) (Test₁ x₃ x₄  ℓ₁⊑ℓ₂) θ₁≈θ₂ with tiniᴾ x₁ x₃ θ₁≈θ₂ | tiniᴾ x₂ x₄ θ₁≈θ₂
... | Lbl ℓ₁ | Lbl ℓ₂ = ⊥-elim (ℓ₁⋤ℓ₂ ℓ₁⊑ℓ₂)
tiniᴾ (Test₁ x₁ x₂ ℓ₁⊑ℓ₂) (Test₂ x₃ x₄ ℓ₁⋤ℓ₂) θ₁≈θ₂ with tiniᴾ x₁ x₃ θ₁≈θ₂ | tiniᴾ x₂ x₄ θ₁≈θ₂
... | Lbl ℓ₁ | Lbl ℓ₂ = ⊥-elim (ℓ₁⋤ℓ₂ ℓ₁⊑ℓ₂)
tiniᴾ (Test₂ _ _ _) (Test₂ _ _ _) _ = Inr Unit
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

wken-∃ : ∀ {τ β β'} {c₁ c₂ : FConf τ} →
         β ⊆ β' → (x : ∃ (λ β'' → β' ⊆ β'' × c₁ ≈⟨ β'' ⟩ᶜ c₂)) →
         ∃ (λ β'' → β ⊆ β'' × c₁ ≈⟨ β'' ⟩ᶜ c₂)
wken-∃ β⊆β' (β'' ∧ β'⊆β'' ∧ ≈₁)  = β'' ∧ (trans-⊆ β⊆β' β'⊆β'') ∧ ≈₁

mutual

  -- TINI for low steps
  tiniᴸ : ∀ {pc τ Γ Σ₁ Σ₂ μ₁ μ₂ θ₁ θ₂ β} {t : Thunk Γ (LIO τ)} {c₁' c₂' : FConf τ} →
                    let c₁ = ⟨ Σ₁ , μ₁ , pc , t ⟩
                        c₂ = ⟨ Σ₂ , μ₂ , pc , t ⟩ in
                   {{valid₁ : Valid-Inputs c₁ θ₁}} {{valid₂ : Valid-Inputs c₂ θ₂}} →
                      c₁ ⇓⟨ θ₁ ⟩ c₁' →
                      c₂ ⇓⟨ θ₂ ⟩ c₂' →
                      ⟨ Σ₁ , μ₁ ⟩ ≈⟨ β ⟩ᴾ ⟨ Σ₂ , μ₂ ⟩ →
                      θ₁ ≈⟨ β ⟩ᴱ θ₂ →
                      pc ⊑ A →
                      ∃ (λ β' → β ⊆ β' × c₁' ≈⟨ β' ⟩ᶜ c₂')

  tiniᴸ (Return x) (Return x₁) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A = _ ∧ refl-⊆ ∧ pcᴸ Σ₁≈Σ₂ pc⊑A (tiniᴾ x x₁ θ₁≈θ₂)

  tiniᴸ {{isV₁}} {{isV₂}} (Bind x₁ y₁) (Bind x₂ y₂) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
    with valid-⇓ᶠ x₁ isV₁ | valid-⇓ᶠ x₂ isV₂ | tiniᶠ x₁ x₂ ⟨ Σ₁≈Σ₂ , refl , refl ⟩ θ₁≈θ₂

  ... | isV₁′ | isV₂′ | β' ∧ β⊆β' ∧ pcᴸ Σ₁'≈Σ₂' pc'⊑A v₁≈v₂
    = wken-∃ β⊆β' (tiniᶠ {{ isV₁′ }} {{isV₂′}} y₁ y₂ ⟨ Σ₁'≈Σ₂' , refl , refl ⟩ (v₁≈v₂ ∷ wken-≈ᴱ β⊆β' θ₁≈θ₂))

  ... | isV₁′ | isV₂′ | β' ∧ β⊆β' ∧ pcᴴ Σ₁'≈Σ₂' pc₁'⋤A pc₂'⋤A
    = wken-∃ β⊆β' ( tiniᶠᴴ {{ isV₁′ }} {{isV₂′}} y₁ y₂ Σ₁'≈Σ₂' pc₁'⋤A pc₂'⋤A)

  tiniᴸ (Unlabel x refl) (Unlabel x₁ refl) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A with tiniᴾ x x₁ θ₁≈θ₂
  ... | Labeledᴸ ℓ⊑A r = _ ∧ refl-⊆ ∧ pcᴸ Σ₁≈Σ₂ (join-⊑' pc⊑A ℓ⊑A) r
  ... | Labeledᴴ pc₁'⋤A pc₂'⋤A = _ ∧ refl-⊆ ∧ pcᴴ Σ₁≈Σ₂ (trans-⋤ (join-⊑₂ _ _) pc₁'⋤A) ((trans-⋤ (join-⊑₂ _ _) pc₂'⋤A))

  tiniᴸ (ToLabeled x) (ToLabeled x₁) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A with tiniᶠ x x₁ ⟨ Σ₁≈Σ₂ , refl , refl ⟩ θ₁≈θ₂
  ... | β' ∧ β⊆β' ∧ pcᴸ Σ₁'≈Σ₂' pc⊑A' v₁≈v₂ = β' ∧ β⊆β' ∧ pcᴸ Σ₁'≈Σ₂' pc⊑A (Labeledᴸ pc⊑A' v₁≈v₂)
  ... | β' ∧ β⊆β' ∧ pcᴴ Σ₁'≈Σ₂' pc₁'⋤A pc₂'⋤A = β' ∧ β⊆β' ∧ pcᴸ Σ₁'≈Σ₂' pc⊑A (Labeledᴴ pc₁'⋤A pc₂'⋤A)

  tiniᴸ (LabelOf x refl) (LabelOf x₂ refl) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A with tiniᴾ x x₂ θ₁≈θ₂
  ... | Labeledᴸ ℓ⊑A r = _ ∧ refl-⊆ ∧ pcᴸ Σ₁≈Σ₂ (join-⊑' pc⊑A ℓ⊑A) (Lbl _)
  ... | Labeledᴴ ℓ⋤A ℓ₁⋤A = _ ∧ refl-⊆ ∧ pcᴴ Σ₁≈Σ₂ (join-⋤₂ ℓ⋤A) (join-⋤₂ ℓ₁⋤A)

  tiniᴸ GetLabel GetLabel Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A = _ ∧ refl-⊆ ∧ pcᴸ Σ₁≈Σ₂ pc⊑A (Lbl _)

  tiniᴸ {pc = pc} (Taint x refl) (Taint x₂ refl) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A with tiniᴾ x x₂ θ₁≈θ₂
  ... | Lbl ℓ with (pc ⊔ ℓ) ⊑? A
  ... | yes pc'⊑A = _ ∧ refl-⊆ ∧  pcᴸ Σ₁≈Σ₂ pc'⊑A Unit
  ... | no pc'⋤A = _ ∧ refl-⊆ ∧ pcᴴ Σ₁≈Σ₂ pc'⋤A pc'⋤A

  tiniᴸ {{isV₁ᴾ ∧ _}} {{isV₂ᴾ ∧ _}} (New x x₁) (New x₂ x₃) ⟨ Σ₁≈Σ₂ , μ≈ ⟩ θ₁≈θ₂ pc⊑A with tiniᴾ x x₂ θ₁≈θ₂
  ... | Labeledᴸ ℓ⊑A v₁≈v₂ = _ ∧ refl-⊆ ∧ pcᴸ ⟨ Σ₁'≈Σ₂' , μ≈ ⟩ pc⊑A r₁≈r₂
    where M₁≈M₂ = getᴸ Σ₁≈Σ₂ ℓ⊑A
          r₁≈r₂ = Refᴸ′ ℓ⊑A ∥ M₁≈M₂ ∥-≡
          Σ₁'≈Σ₂' = updateᴸ-≈ˢ Σ₁≈Σ₂ (new-≈ᴹ M₁≈M₂ v₁≈v₂)
  ... | Labeledᴴ ℓ₁⋤A ℓ₂⋤A  = _ ∧ refl-⊆ ∧ pcᴸ ⟨ Σ₁'≈Σ₂' , μ≈ ⟩ pc⊑A r₁≈r₂
    where open _≈⟨_⟩ᴴ_ μ≈
          r₁≈r₂ = Ref-Iᴴ ℓ₁⋤A ℓ₂⋤A
          Σ₁≈Σ₁′ = updateᴴ-≈ˢ {{validˢ isV₁ᴾ}} ℓ₁⋤A
          Σ₂≈Σ₂′ = updateᴴ-≈ˢ {{validˢ isV₂ᴾ}} ℓ₂⋤A
          Σ₁'≈Σ₂' = square-≈ˢ-ι Σ₁≈Σ₂ Σ₁≈Σ₁′ Σ₂≈Σ₂′ ⊆ᴿ-ι ⊆ᴰ-ι

  tiniᴸ (Read x₁ n∈M₁ refl) (Read x₂ n∈M₂ refl) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A with tiniᴾ x₁ x₂ θ₁≈θ₂
  ... | Ref-Iᴸ ℓ⊑A n = _ ∧ refl-⊆ ∧ pcᴸ Σ₁≈Σ₂ (join-⊑' pc⊑A ℓ⊑A) v≈
    where open _≈⟨_⟩ᴾ_
          Σ≈ = store-≈ˢ Σ₁≈Σ₂
          v≈ = read-≈ᴹ (getᴸ Σ≈ ℓ⊑A) n∈M₁ n∈M₂

  ... | Ref-Iᴴ ℓ₁⋤A ℓ₂⋤A = _ ∧ refl-⊆ ∧ pcᴴ Σ₁≈Σ₂ (trans-⋤ (join-⊑₂ _ _) ℓ₁⋤A) (trans-⋤ (join-⊑₂ _ _) ℓ₂⋤A)

  tiniᴸ {{isV₁ᴾ ∧ _}} {{isV₂ᴾ ∧ _}} (Write x₁ x₂ pc⊑ℓ₁ ℓ'⊑ℓ₁ u₁) (Write x₁' x₂' pc⊑ℓ₂ ℓ''⊑ℓ₂ u₂) ⟨ Σ₁≈Σ₂ , μ≈ ⟩ θ₁≈θ₂ pc⊑A
    with tiniᴾ x₁ x₁' θ₁≈θ₂ | tiniᴾ x₂ x₂' θ₁≈θ₂
  ... | Ref-Iᴴ ℓ₁⋤A ℓ₂⋤A | v₁≈v₂ = _ ∧ refl-⊆ ∧ pcᴸ ⟨ Σ₁'≈Σ₂' , μ≈ ⟩ pc⊑A Unit
    where open _≈⟨_⟩ᴴ_ μ≈
          Σ₁≈Σ₁′ = updateᴴ-≈ˢ {{validˢ isV₁ᴾ}} ℓ₁⋤A
          Σ₂≈Σ₂′ = updateᴴ-≈ˢ {{validˢ isV₂ᴾ}} ℓ₂⋤A
          Σ₁'≈Σ₂' = square-≈ˢ-ι Σ₁≈Σ₂ Σ₁≈Σ₁′ Σ₂≈Σ₂′ ⊆ᴿ-ι ⊆ᴰ-ι
  ... | Ref-Iᴸ ℓ⊑A n | Labeledᴴ ℓ'⋤A ℓ''⋤A  = ⊥-elim (trans-⋤ ℓ'⊑ℓ₁ ℓ'⋤A ℓ⊑A)
  ... | Ref-Iᴸ ℓ⊑A n | Labeledᴸ x v₁≈v₂ = _ ∧ refl-⊆ ∧ pcᴸ ⟨ Σ₁'≈Σ₂' , μ≈ ⟩ pc⊑A Unit
    where Σ₁'≈Σ₂' = updateᴸ-≈ˢ Σ₁≈Σ₂ (update-≈ᴹ (getᴸ Σ₁≈Σ₂ ℓ⊑A) v₁≈v₂ u₁ u₂)

  tiniᴸ (LabelOfRef x refl) (LabelOfRef x₁ refl) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A with tiniᴾ x x₁ θ₁≈θ₂
  ... | Ref-Iᴸ ℓ⊑A n = _ ∧ refl-⊆ ∧ pcᴸ Σ₁≈Σ₂ (join-⊑' pc⊑A ℓ⊑A) (Lbl _)
  ... | Ref-Iᴴ ℓ₁⋤A ℓ₂⋤A = _ ∧ refl-⊆ ∧ pcᴴ Σ₁≈Σ₂ (trans-⋤ (join-⊑₂ _ _) ℓ₁⋤A) (trans-⋤ (join-⊑₂ _ _) ℓ₂⋤A)

  tiniᴸ {β = β} (New-FS {μ = μ₁} x₁ ⊑₁) (New-FS {μ = μ₂} x₂ ⊑₂) ⟨ Σ≈ , μ≈ ⟩ θ₁≈θ₂ pc⊑A
    = β′′ ∧ ⊆₁ ∧ pcᴸ ⟨ wken-≈ˢ ⊆₁ Σ≈ , μ≈′ ⟩ pc⊑A (wken-≈ⱽ ⊆₂ v≈)
    where
      instance _ = _≟_
               _ = ≈-# μ≈
      β′ =  ∥ μ₁ ∥ᴴ ↔ ∥ μ₂ ∥ᴴ
      β′′ = β ∣ᴮ β′
      ⊆₁ = ∣ᴮ-⊆₁ β β′
      ⊆₂ = ∣ᴮ-⊆₂ β β′
      μ≈′ = newᴸ-≈ᴴ (tiniᴾ x₁ x₂ θ₁≈θ₂) μ≈
      v≈ = Ref-S (↔-∈ᵗ ∥ μ₁ ∥ᴴ ∥ μ₂ ∥ᴴ)

  tiniᴸ (Read-FS x₁ ∈₁ refl) (Read-FS x₂ ∈₂ refl) ≈ᴾ θ₁≈θ₂ pc⊑A with tiniᴾ x₁ x₂ θ₁≈θ₂
  ... | Ref-S ∈β = _ ∧ refl-⊆ ∧ read-≈ᶜ pc⊑A ≈ᴾ v≈
    where open _≈⟨_⟩ᴾ_
          v≈ = readᴸ-≈ⱽ ∈β ∈₁ ∈₂ (heap-≈ᴴ ≈ᴾ)

  tiniᴸ (Write-FS x₁ y₁ ∈₁ ⊑₁ refl w₁) (Write-FS x₂ y₂ ∈₂ ⊑₂ refl w₂) ⟨ Σ≈ , μ≈ ⟩ θ₁≈θ₂ pc⊑A
    with tiniᴾ x₁ x₂ θ₁≈θ₂
  ... | Ref-S ∈β = _ ∧ refl-⊆ ∧ pcᴸ ⟨ Σ≈ , μ≈′ ⟩ pc⊑A Unit
    where v≈ = readᴸ-≈ⱽ ∈β ∈₁ ∈₂ μ≈
          μ≈′ = writeᴸ-≈ᴴ μ≈ (≈ᴸ-⊔ _ (tiniᴾ y₁ y₂ θ₁≈θ₂)) w₁ w₂ ∈β

  tiniᴸ (LabelOfRef-FS x₁ ∈₁ refl) (LabelOfRef-FS x₂ ∈₂ refl) ≈ᴾ θ₁≈θ₂ pc⊑A with tiniᴾ x₁ x₂ θ₁≈θ₂
  ... | Ref-S ∈β = _ ∧ refl-⊆ ∧ label-of-≈ᶜ pc⊑A ≈ᴾ v≈
    where open _≈⟨_⟩ᴾ_
          v≈ = readᴸ-≈ⱽ ∈β ∈₁ ∈₂ (heap-≈ᴴ ≈ᴾ)

  -- TINI for high-forcing steps
  tiniᶠᴴ : ∀ {τ Γ₁ Γ₂ θ₁ θ₂ β} {c₁ : EConf Γ₁ (LIO τ)} {c₂ : EConf Γ₂ (LIO τ)} {c₁' c₂' : FConf τ} →
           let ⟨ Σ₁ , μ₁ , pc₁ , t₁ ⟩ = c₁
               ⟨ Σ₂ , μ₂ , pc₂ , t₂ ⟩ = c₂ in
             {{valid₁ : Valid-Inputs c₁ θ₁}} {{valid₂ : Valid-Inputs c₂ θ₂}} →
           c₁ ⇓ᶠ⟨ θ₁ ⟩ c₁' →
           c₂ ⇓ᶠ⟨ θ₂ ⟩ c₂' →
           ⟨ Σ₁ , μ₁ ⟩ ≈⟨ β ⟩ᴾ ⟨ Σ₂ , μ₂ ⟩ →
           pc₁ ⋤ A →
           pc₂ ⋤ A →
           ∃ (λ β' → β ⊆ β' × c₁' ≈⟨ β' ⟩ᶜ c₂')
  tiniᶠᴴ {{isV₁ᴾ ∧ isV₁ᴱ}} {{isV₂ᴾ ∧ isV₂ᴱ}} (Force x₁ y₁) (Force x₂ y₂)
    = tiniᴴ {{isV₁ᴾ ∧ isV₁ᴱ′ }} {{isV₂ᴾ ∧ isV₂ᴱ′ }} y₁ y₂
    where isV₁ᴱ′ = validⱽ-⇓ᴾ x₁ isV₁ᴱ
          isV₂ᴱ′ = validⱽ-⇓ᴾ x₂ isV₂ᴱ

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
  tiniᴴ : ∀ {τ Γ₁ Γ₂ θ₁ θ₂ β} {c₁ : TConf Γ₁ (LIO τ)} {c₂ : TConf Γ₂ (LIO τ)} {c₁' c₂' : FConf τ} →
           let ⟨ Σ₁ , μ₁ , pc₁ , t₁ ⟩ = c₁
               ⟨ Σ₂ , μ₂ , pc₂ , t₂ ⟩ = c₂ in
             {{valid₁ : Valid-Inputs c₁ θ₁}} {{valid₂ : Valid-Inputs c₂ θ₂}} →
           c₁ ⇓⟨ θ₁ ⟩ c₁' →
           c₂ ⇓⟨ θ₂ ⟩ c₂' →
           ⟨ Σ₁ , μ₁ ⟩ ≈⟨ β ⟩ᴾ ⟨ Σ₂ , μ₂ ⟩ →
           pc₁ ⋤ A →
           pc₂ ⋤ A →
           ∃ (λ β' → β ⊆ β' × c₁' ≈⟨ β' ⟩ᶜ c₂')
  tiniᴴ {{isV₁ᴾ ∧ isV₁ᴱ}} {{isV₂ᴾ ∧ isV₂ᴱ}} x₁ x₂ Σ₁≈Σ₂ pc₁⋤A pc₂⋤A
    = _ ∧ refl-⊆ ∧ pcᴴ Σ₁'≈Σ₂' (trans-⋤ (step-⊑ x₁) pc₁⋤A) (trans-⋤ (step-⊑ x₂) pc₂⋤A)
    where Σ₁≈Σ₁' = step-≈ᴾ {{ isV₁ᴾ }} {{ isV₁ᴱ }} x₁ pc₁⋤A
          Σ₂≈Σ₂' = step-≈ᴾ {{ isV₂ᴾ }} {{ isV₂ᴱ }} x₂ pc₂⋤A
          Σ₁'≈Σ₂' = square-≈ᴾ-ι Σ₁≈Σ₂ Σ₁≈Σ₁' Σ₂≈Σ₂'

  --------------------------------------------------------------------------------
  -- TINI (top-level theorems) for thunk and forcing semantics.

  tini : ∀ {τ Γ θ₁ θ₂ β} {c₁ c₂ : TConf Γ (LIO τ)} {c₁' c₂' : FConf τ} →
         {{valid₁ : Valid-Inputs c₁ θ₁}} {{valid₂ : Valid-Inputs c₂ θ₂}} →
           c₁ ⇓⟨ θ₁ ⟩ c₁' →
           c₂ ⇓⟨ θ₂ ⟩ c₂' →
           c₁ ≈⟨ β ⟩ᵀ c₂ →
           θ₁ ≈⟨ β ⟩ᴱ θ₂ →
           ∃ (λ β' → β ⊆ β' × c₁' ≈⟨ β' ⟩ᶜ c₂')
  tini {c₁ = ⟨ _ , _ , pc , _ ⟩} x₁ x₂ ⟨ Σ₁≈Σ₂ , refl , refl ⟩ θ₁≈θ₂ with pc ⊑? A
  ... | yes pc⊑A = tiniᴸ x₁ x₂ Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
  ... | no pc⋤A = tiniᴴ x₁ x₂ Σ₁≈Σ₂ pc⋤A pc⋤A

  tiniᶠ : ∀ {τ Γ θ₁ θ₂ β} {c₁ c₂ : EConf Γ (LIO τ)} {c₁' c₂' : FConf τ} →
            {{valid₁ : Valid-Inputs c₁ θ₁}} {{valid₂ : Valid-Inputs c₂ θ₂}} →
           c₁ ⇓ᶠ⟨ θ₁ ⟩ c₁' →
           c₂ ⇓ᶠ⟨ θ₂ ⟩ c₂' →
           c₁ ≈⟨ β ⟩ᴵ c₂ →
           θ₁ ≈⟨ β ⟩ᴱ θ₂ →
           ∃ (λ β' → β ⊆ β' × c₁' ≈⟨ β' ⟩ᶜ c₂')
  tiniᶠ {{isV₁ᴾ ∧ isV₁ᴱ}} {{isV₂ᴾ ∧ isV₂ᴱ}} (Force x₁ y₁) (Force x₂ y₂) ⟨ Σ≈ , refl , refl ⟩ θ₁≈θ₂ with tiniᴾ x₁ x₂ θ₁≈θ₂
  ... | Thunk′ θ₁≈θ₂' = tini {{ isV₁ᴾ ∧ isV₁ᴱ′ }} {{ isV₂ᴾ ∧ isV₂ᴱ′ }} y₁ y₂ ⟨ Σ≈ , refl , refl ⟩ θ₁≈θ₂'
    where isV₁ᴱ′ = validⱽ-⇓ᴾ x₁ isV₁ᴱ
          isV₂ᴱ′ = validⱽ-⇓ᴾ x₂ isV₂ᴱ
