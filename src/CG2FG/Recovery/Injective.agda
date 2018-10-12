open import Lattice

module CG2FG.Recovery.Injective {{𝑳 : Lattice}} where

open import CG as CG
open import FG as FG
open import Relation.Binary.PropositionalEquality

open import CG2FG.Syntax
open import CG2FG.Graph

inj-⟦·⟧ᵗ′ : ∀ {τ₁ τ₂ τ₃} → MkTy τ₁ τ₃ → MkTy τ₂ τ₃ → τ₁ ≡ τ₂
inj-⟦·⟧ᵗ′ Unit Unit = refl
inj-⟦·⟧ᵗ′ 𝓛 𝓛 = refl
inj-⟦·⟧ᵗ′ (Prod x x₁) (Prod y y₁)
  rewrite inj-⟦·⟧ᵗ′ x y | inj-⟦·⟧ᵗ′ x₁ y₁ = refl
inj-⟦·⟧ᵗ′ (Sum x x₁) (Sum y y₁)
  rewrite inj-⟦·⟧ᵗ′ x y | inj-⟦·⟧ᵗ′ x₁ y₁ = refl
inj-⟦·⟧ᵗ′ (Labeled x) (Labeled y) rewrite inj-⟦·⟧ᵗ′ x y = refl
inj-⟦·⟧ᵗ′ (Ref x) (Ref y) rewrite inj-⟦·⟧ᵗ′ x y = refl
inj-⟦·⟧ᵗ′ (LIO x) (LIO y) rewrite inj-⟦·⟧ᵗ′ x y = refl
inj-⟦·⟧ᵗ′ (LIO x) (Fun () y₁)
inj-⟦·⟧ᵗ′ (Fun () x₁) (LIO y)
inj-⟦·⟧ᵗ′ (Fun x x₁) (Fun y y₁)
  rewrite inj-⟦·⟧ᵗ′ x y | inj-⟦·⟧ᵗ′ x₁ y₁ = refl

inj-⟦_⟧ᵗ  : ∀ {τ τ'} → ⟦ τ ⟧ᵗ ≡ ⟦ τ' ⟧ᵗ → τ ≡ τ'
inj-⟦_⟧ᵗ {τ} {τ'} eq with mkTy τ | mkTy τ'
... | x | y rewrite eq = inj-⟦·⟧ᵗ′ x y

open Injective inj-⟦_⟧ᵗ renaming (inj-⟪_⟫ᶜ to inj-⟦_⟧ᶜ ; inj-S2Tᶜ to inj-MkCtx) public

mutual

  inj-⟦·⟧ᴱ : ∀ {Γ Γ' τ τ' e₁ e₂ e₃} {p₁ p₂ : MkTy τ τ'} {c₁ c₂ : MkCtx Γ Γ'} →
               Cg2Fgᴱ c₁ p₁ e₁ e₃ →
               Cg2Fgᴱ c₂ p₂ e₂ e₃ →
               e₁ ≡ e₂
  inj-⟦·⟧ᴱ Unit Unit = refl
  inj-⟦·⟧ᴱ (Lbl ℓ) (Lbl .ℓ) = refl
  inj-⟦·⟧ᴱ (Var x) (Var y) rewrite inj-Cg2Fg-∈ x y = refl
  inj-⟦·⟧ᴱ (Fun x) (Fun y) rewrite inj-⟦·⟧ᴱ x y = refl
  inj-⟦·⟧ᴱ (App {p₁ = p₁} x₁ x₂) (App {p₁ = p₂} y₁ y₂) with inj-⟦·⟧ᵗ′ p₁ p₂
  ... | refl rewrite inj-⟦·⟧ᴱ x₁ y₁ | inj-⟦·⟧ᴱ x₂ y₂ = refl
  inj-⟦·⟧ᴱ (Pair x₁ x₂) (Pair y₁ y₂)
    rewrite inj-⟦·⟧ᴱ x₁ y₁ | inj-⟦·⟧ᴱ x₂ y₂ = refl
  inj-⟦·⟧ᴱ (Fst {p₂ = p₂} x) (Fst {p₂ = p₂'} y) with inj-⟦·⟧ᵗ′ p₂ p₂'
  ... | refl rewrite inj-⟦·⟧ᴱ x y = refl
  inj-⟦·⟧ᴱ (Snd {p₁ = p₁} x) (Snd {p₁ = p₁'} y) with inj-⟦·⟧ᵗ′ p₁ p₁'
  ... | refl rewrite inj-⟦·⟧ᴱ x y = refl
  inj-⟦·⟧ᴱ (Inl {p₂ = p₂} x) (Inl {p₂ = p₂'} y)  with inj-⟦·⟧ᵗ′ p₂ p₂'
  ... | refl rewrite inj-⟦·⟧ᴱ x y = refl
  inj-⟦·⟧ᴱ (Inr {p₁ = p₁} x) (Inr {p₁ = p₁'} y) with inj-⟦·⟧ᵗ′ p₁ p₁'
  ... | refl rewrite inj-⟦·⟧ᴱ x y = refl
  inj-⟦·⟧ᴱ (Case {p₁ = p₁} {p₂} x x₁ x₂) (Case {p₁ = p₁'} {p₂'} y y₁ y₂)
    with inj-⟦·⟧ᵗ′ p₁ p₁' | inj-⟦·⟧ᵗ′ p₂ p₂'
  ... | refl | refl rewrite inj-⟦·⟧ᴱ x y | inj-⟦·⟧ᴱ x₁ y₁ | inj-⟦·⟧ᴱ x₂ y₂ = refl
  inj-⟦·⟧ᴱ (Wken {c' = c₁} x₁ x₂) (Wken {c' = c₂} y₁ y₂) with inj-MkCtx c₁ c₂
  ... | refl rewrite inj-⟦·⟧ᴱ x₁ y₁ | inj-Cg2Fg-⊆ x₂ y₂ = refl
  inj-⟦·⟧ᴱ ⌞ x ⌟ᵀ ⌞ y ⌟ᵀ rewrite inj-⟦·⟧ᵀ x y = refl

  inj-⟦·⟧ᵀ : ∀ {Γ Γ' τ τ'} {t₁ t₂ : Thunk Γ (LIO τ)} {e₃ : FG.Expr Γ' τ'}  {p₁ p₂ : MkTy τ τ'} {c₁ c₂ : MkCtx Γ Γ'} →
               Cg2Fgᵀ c₁ p₁ t₁ e₃ →
               Cg2Fgᵀ c₂ p₂ t₂ e₃ →
               t₁ ≡ t₂
  inj-⟦·⟧ᵀ (Return x) (Return y) rewrite inj-⟦·⟧ᴱ x y = refl
  inj-⟦·⟧ᵀ (Return (App x (App x₃ ()))) (Bind x₁ x₂)
  inj-⟦·⟧ᵀ (Return (App x ())) (Unlabel x₁)
  inj-⟦·⟧ᵀ (Return (App x (App x₂ ()))) (ToLabeled x₁)
  inj-⟦·⟧ᵀ (Return (Fst ())) (LabelOf x₁)
  inj-⟦·⟧ᵀ (Return ()) GetLabel
  inj-⟦·⟧ᵀ (Return ()) (Taint x₁)
  inj-⟦·⟧ᵀ (Return ()) (New x₁)
  inj-⟦·⟧ᵀ (Return ()) (Read x₁)
  inj-⟦·⟧ᵀ (Return ()) (Write x₁ x₂)
  inj-⟦·⟧ᵀ (Return ()) (LabelOfRef x₁)
  inj-⟦·⟧ᵀ (Bind x x₁) (Return (App x₂ (App x₃ ())))
  inj-⟦·⟧ᵀ (Bind {p₁ = p₁} x₁ x₂) (Bind {p₁ = q₁} y₁ y₂) with inj-⟦·⟧ᵗ′ p₁ q₁
  ... | refl rewrite inj-⟦·⟧ᴱ x₁ y₁ | inj-⟦·⟧ᴱ x₂ y₂ = refl
  inj-⟦·⟧ᵀ (Unlabel x) (Return (App x₁ ()))
  inj-⟦·⟧ᵀ (Unlabel x) (Unlabel y) rewrite inj-⟦·⟧ᴱ x y = refl
  inj-⟦·⟧ᵀ (ToLabeled x) (Return (App x₁ (App x₂ ())))
  inj-⟦·⟧ᵀ (ToLabeled x) (ToLabeled y) rewrite inj-⟦·⟧ᴱ x y = refl
  inj-⟦·⟧ᵀ (LabelOf x) (Return (Fst ()))
  inj-⟦·⟧ᵀ (LabelOf {p = p} x) (LabelOf {p = q} y) with inj-⟦·⟧ᵗ′ p q
  ... | refl rewrite inj-⟦·⟧ᴱ x y = refl
  inj-⟦·⟧ᵀ GetLabel (Return ())
  inj-⟦·⟧ᵀ GetLabel GetLabel = refl
  inj-⟦·⟧ᵀ (Taint x) (Return ())
  inj-⟦·⟧ᵀ (Taint x) (Taint y) rewrite inj-⟦·⟧ᴱ x y = refl
  inj-⟦·⟧ᵀ (New x) (Return ())
  inj-⟦·⟧ᵀ (New x) (New y) rewrite inj-⟦·⟧ᴱ x y = refl
  inj-⟦·⟧ᵀ (Read x) (Return ())
  inj-⟦·⟧ᵀ (Read x) (Read y) rewrite inj-⟦·⟧ᴱ x y = refl
  inj-⟦·⟧ᵀ (Write x x₁) (Return ())
  inj-⟦·⟧ᵀ (Write {p = p} x₁ x₂) (Write {p = q} y₁ y₂) with inj-⟦·⟧ᵗ′ p q
  ... | refl rewrite inj-⟦·⟧ᴱ x₁ y₁ | inj-⟦·⟧ᴱ x₂ y₂ = refl
  inj-⟦·⟧ᵀ (LabelOfRef x) (Return ())
  inj-⟦·⟧ᵀ (LabelOfRef {p = p} x) (LabelOfRef {p = q} y) with inj-⟦·⟧ᵗ′ p q
  ... | refl rewrite inj-⟦·⟧ᴱ x y = refl

inj-⟦_⟧ᴱ : ∀ {Γ τ} {e₁ e₂ : CG.Expr Γ τ} → ⟦ e₁ ⟧ᴱ ≡ ⟦ e₂ ⟧ᴱ → e₁ ≡ e₂
inj-⟦_⟧ᴱ {e₁ = e₁} {e₂} eq with mkCg2Fgᴱ e₁ | mkCg2Fgᴱ e₂
... | x | y rewrite eq = inj-⟦·⟧ᴱ x y
