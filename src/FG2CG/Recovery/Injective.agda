-- This module proves that the type and expression translations are
-- injective. The proof technique employes the graph of the function,
-- i.e., an inductive relation that connects inputs and outputs of the
-- translation function.

open import Lattice

module FG2CG.Recovery.Injective {{𝑳 : Lattice}} where

open import FG2CG.Graph
open import FG2CG.Syntax
open import FG as FG
open import CG as CG
open import Relation.Binary.PropositionalEquality
open import Data.Empty

--------------------------------------------------------------------------------
-- Type translation ⟪·⟫ᵗ is injective

mutual

  inj-Id : ∀ {τ₁ τ₂ τ₃} → MkTy′ (Id τ₁) τ₃ → MkTy′ τ₂ τ₃ → (Id τ₁) ≡ τ₂
  inj-Id (Id ()) 𝓛
  inj-Id (Id ()) Unit
  inj-Id (Id ()) (Refᴵ y)
  inj-Id (Id ()) (Refˢ y)
  inj-Id (Id ()) (Sum x₁ x₂)
  inj-Id (Id ()) (Prod x₁ x₂)
  inj-Id (Id ()) (Fun x₁ x₂)
  inj-Id (Id x) (Id y) = cong Id (inj-MkTy x y)

  inj-MkTy′ :  ∀ {τ τ₁ τ₂} → MkTy′ τ₁ τ → MkTy′ τ₂ τ → τ₁ ≡ τ₂
  inj-MkTy′ 𝓛 𝓛 = refl
  inj-MkTy′ Unit Unit = refl
  inj-MkTy′ (Refᴵ x) (Refᴵ x₁) = cong (Ref I) (inj-MkTy′ x x₁)
  inj-MkTy′ (Refˢ x) (Refˢ x₁) = cong (Ref S) (inj-MkTy′ x x₁)
  inj-MkTy′ (Sum x x₁) (Sum x₂ x₃) = cong₂ _+_ (inj-MkTy x x₂) (inj-MkTy x₁ x₃)
  inj-MkTy′ (Prod x x₁) (Prod x₂ x₃) = cong₂ FG._×_ (inj-MkTy x x₂) (inj-MkTy x₁ x₃)
  inj-MkTy′ (Fun x x₁) (Fun x₂ x₃) = cong₂ FG._➔_ (inj-MkTy x x₂) (inj-MkTy x₁ x₃)
  inj-MkTy′ (Id x) y = inj-Id (Id x) y
  inj-MkTy′ x (Id y) = sym (inj-Id (Id y) x)

  inj-MkTy :  ∀ {τ τ₁ τ₂} → MkTy τ₁ τ → MkTy τ₂ τ → τ₁ ≡ τ₂
  inj-MkTy (Labeled x) (Labeled y) rewrite inj-MkTy′ x y = refl

inj-⟪_⟫ᵗ : ∀ {τ₁ τ₂} → ⟪ τ₁ ⟫ᵗ ≡ ⟪ τ₂ ⟫ᵗ → τ₁ ≡ τ₂
inj-⟪_⟫ᵗ {τ₁} {τ₂} eq with mkTy τ₁ | mkTy τ₂
... | x | y rewrite eq = inj-MkTy x y

inj-⟪_⟫ᵗ′ : ∀ {τ₁ τ₂} → ⟪ τ₁ ⟫ᵗ′ ≡ ⟪ τ₂ ⟫ᵗ′ → τ₁ ≡ τ₂
inj-⟪_⟫ᵗ′ {τ₁} {τ₂} eq with mkTy′ τ₁ | mkTy′ τ₂
... | x | y rewrite eq = inj-MkTy′ x y

--------------------------------------------------------------------------------
-- Context translation ⟪·⟫ᶜ is injective

open Injective inj-⟪_⟫ᵗ using (inj-⟪_⟫ᶜ)
  renaming (inj-S2Tᶜ to ⟪·⟫ᶜ-inj′ ) public
open import Generic.Context.Graph Graph-⟪·⟫ᵗ
  renaming ( inj-S2T-∈ to ⟪·⟫∈-inj ; inj-S2T-⊆ to ⟪·⟫⊆-inj ) public

--------------------------------------------------------------------------------
-- Expression translation (⟪·⟫ᴱ and ⟪·⟫ᵀ) is injective.

mutual
  inj-⟪·⟫ᴱ  : ∀ {Γ Γ' τ τ' c₁ c₂ p₁ p₂} {e₁ : FG.Expr Γ τ} {e₂ : FG.Expr Γ τ}
                 {e₁' : CG.Expr Γ' (LIO (Labeled τ'))} →
                 Fg2Cgᴱ c₁ p₁ e₁ e₁' →
                 Fg2Cgᴱ c₂ p₂ e₂ e₁' →
                 e₁ ≡ e₂
  inj-⟪·⟫ᴱ ⌞ x ⌟ᵀ ⌞ y ⌟ᵀ rewrite inj-⟪·⟫ᵀ x y = refl

  inj-⟪·⟫ᵀ  : ∀ {Γ Γ' τ τ' c₁ p₁ c₂ p₂} {e₁ : FG.Expr Γ τ} {e₂ : FG.Expr Γ τ}
                 {e₁' : CG.Thunk Γ' (LIO (Labeled τ'))} →
                 Fg2Cgᵀ c₁ p₁ e₁ e₁' →
                 Fg2Cgᵀ c₂ p₂ e₂ e₁' →
                 e₁ ≡ e₂
  inj-⟪·⟫ᵀ Unit Unit = refl
  inj-⟪·⟫ᵀ (Var x) (Var y) rewrite ⟪·⟫∈-inj x y = refl
  inj-⟪·⟫ᵀ (Fun x) (Fun y) rewrite inj-⟪·⟫ᴱ x y = refl
  inj-⟪·⟫ᵀ (App {p₁ = p₁} x₁ x₂) (App {p₁ = p₁'} y₁ y₂) with inj-MkTy′ p₁ p₁'
  ... | refl rewrite inj-⟪·⟫ᴱ x₁ y₁ | inj-⟪·⟫ᴱ x₂ y₂ = refl
  inj-⟪·⟫ᵀ (Pair x₁ x₂) (Pair y₁ y₂)
    rewrite inj-⟪·⟫ᴱ x₁ y₁ | inj-⟪·⟫ᴱ x₂ y₂ = refl
  inj-⟪·⟫ᵀ (Fst {p₂ = p₂} x) (Fst {p₂ = q₂} y) with inj-MkTy′ p₂ q₂
  ... | refl rewrite inj-⟪·⟫ᴱ x y = refl
  inj-⟪·⟫ᵀ (Snd {p₁ = p₁} x) (Snd {p₁ = q₁} y) with inj-MkTy′ p₁ q₁
  ... | refl rewrite inj-⟪·⟫ᴱ x y = refl
  inj-⟪·⟫ᵀ (Inl {p₂ = p₂} x) (Inl {p₂ = q₂} y) with inj-MkTy′ p₂ q₂
  ... | refl rewrite inj-⟪·⟫ᴱ x y = refl
  inj-⟪·⟫ᵀ (Inr {p₁ = p₁} x) (Inr {p₁ = q₁} y) with inj-MkTy′ p₁ q₁
  ... | refl rewrite inj-⟪·⟫ᴱ x y = refl
  inj-⟪·⟫ᵀ (Case {p₁ = p₁} {p₂} {p₃} x₁ x₂ x₃) (Case {p₁ = q₁} {q₂} {q₃} y₁ y₂ y₃)
    with inj-MkTy′ p₁ q₁ |  inj-MkTy′ p₂ q₂
  ... | refl | refl rewrite inj-⟪·⟫ᴱ x₁ y₁ | inj-⟪·⟫ᴱ x₂ y₂ | inj-⟪·⟫ᴱ x₃ y₃ = refl
  inj-⟪·⟫ᵀ (Lbl ℓ) (Lbl .ℓ) = refl
  inj-⟪·⟫ᵀ (Test x₁ x₂) (Test y₁ y₂)
    rewrite inj-⟪·⟫ᴱ x₁ y₁ | inj-⟪·⟫ᴱ x₂ y₂ = refl
  inj-⟪·⟫ᵀ GetLabel GetLabel = refl
  inj-⟪·⟫ᵀ (LabelOf {p = p} x) (LabelOf {p = q} y) with inj-MkTy′ p q
  ... | refl rewrite inj-⟪·⟫ᴱ x y = refl
  inj-⟪·⟫ᵀ (Wken {c₁ = c₁} x p) (Wken {c₁ = c₂} y q) with ⟪·⟫ᶜ-inj′ c₁ c₂
  ... | eq rewrite eq | inj-⟪·⟫ᴱ x y | ⟪·⟫⊆-inj p q = refl
  inj-⟪·⟫ᵀ (Taint x₁ x₂) (Taint y₁ y₂)
    rewrite inj-⟪·⟫ᴱ x₁ y₁ | inj-⟪·⟫ᴱ x₂ y₂ = refl
  inj-⟪·⟫ᵀ (LabelOfRef {p = p} x) (LabelOfRef {p = q} y) with inj-MkTy′ p q
  ... | refl rewrite inj-⟪·⟫ᴱ x y = refl
  inj-⟪·⟫ᵀ (New x) (New y) rewrite inj-⟪·⟫ᴱ x y = refl
  inj-⟪·⟫ᵀ (Read x) (Read y) rewrite inj-⟪·⟫ᴱ x y = refl
  inj-⟪·⟫ᵀ (Write {p = p} x₁ x₂) (Write {p = q} y₁ y₂) with inj-MkTy′ p q
  ... | refl rewrite inj-⟪·⟫ᴱ x₁ y₁ |  inj-⟪·⟫ᴱ x₂ y₂ = refl
  inj-⟪·⟫ᵀ (Id x) y = injᵀ-Id (Id x) y
  inj-⟪·⟫ᵀ x (Id y) = sym (injᵀ-Id (Id y) x)
  inj-⟪·⟫ᵀ (UnId x) (UnId y) rewrite inj-⟪·⟫ᴱ x y = refl

  injᵀ-Id : ∀ {τ τ' Γ Γ' c₁ c₂ p₁ p₂} {e₁ : FG.Expr Γ τ} {e₂ : FG.Expr Γ (Id τ)}
              {e' : CG.Thunk Γ' (LIO (Labeled τ'))} →
              Fg2Cgᵀ c₁ p₁ (Id e₁) e' →
              Fg2Cgᵀ c₂ p₂ e₂ e' →
              (Id e₁) ≡ e₂
  injᵀ-Id (Id ⌞ () ⌟ᵀ) (Var x₁)
  injᵀ-Id (Id ⌞ () ⌟ᵀ) (Fst x₁)
  injᵀ-Id (Id ⌞ () ⌟ᵀ) (Snd x₁)
  injᵀ-Id (Id ⌞ () ⌟ᵀ) (Case x₁ x₂ x₃)
  injᵀ-Id (Id ⌞ () ⌟ᵀ) (Taint x₁ x₂)
  injᵀ-Id (Id ⌞ () ⌟ᵀ) (Read x₁)
  injᵀ-Id (Id x) (Id y) = cong Id (inj-⟪·⟫ᴱ x y)
  injᵀ-Id (Id ⌞ () ⌟ᵀ) (UnId x₁)

inj-⟪_⟫ᴱ : ∀ {Γ τ} {e₁ e₂ : FG.Expr Γ τ} → ⟪ e₁ ⟫ᴱ ≡ ⟪ e₂ ⟫ᴱ → e₁ ≡ e₂
inj-⟪_⟫ᴱ {e₁ = e₁} {e₂} eq with mkFg2Cgᴱ e₁ | mkFg2Cgᴱ e₂
... | x | y rewrite eq = inj-⟪·⟫ᴱ x y

inj-⟪_⟫ᵀ : ∀ {Γ τ} {e₁ e₂ : FG.Expr Γ τ} → ⟪ e₁ ⟫ᵀ ≡ ⟪ e₂ ⟫ᵀ → e₁ ≡ e₂
inj-⟪_⟫ᵀ {e₁ = e₁} {e₂} eq with mkFg2Cgᵀ e₁ | mkFg2Cgᵀ e₂
... | x | y rewrite eq = inj-⟪·⟫ᵀ x y
