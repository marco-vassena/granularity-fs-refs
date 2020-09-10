module FG2CG.Graph.Types  where

open import FG.Types as FG
open import CG.Types as CG
open import FG2CG.Types
open import Relation.Binary.PropositionalEquality

mutual

  data MkTy′ : FG.Ty → CG.Ty → Set where
    𝓛 : MkTy′ 𝓛 𝓛
    Unit : MkTy′ unit unit
    Refᴵ : ∀ {τ τ'} → MkTy′ τ τ' → MkTy′ (Ref I τ) (Ref I τ')
    Refˢ : ∀ {τ τ'} → MkTy′ τ τ' → MkTy′ (Ref S τ) (Ref S τ')
    Sum : ∀ {τ₁ τ₂ τ₁' τ₂'} → MkTy τ₁ τ₁' → MkTy τ₂ τ₂' → MkTy′ (τ₁ FG.+ τ₂) (τ₁' CG.+ τ₂')
    Prod : ∀ {τ₁ τ₂ τ₁' τ₂'} → MkTy τ₁ τ₁' → MkTy τ₂ τ₂' → MkTy′ (τ₁ FG.× τ₂) (τ₁' CG.× τ₂')
    Fun : ∀ {τ₁ τ₂ τ₁' τ₂'} → MkTy τ₁ τ₁' → MkTy τ₂ τ₂' → MkTy′ (τ₁ FG.➔ τ₂) (τ₁' CG.➔ (LIO τ₂'))
    Id : ∀ {τ τ'} → MkTy τ τ' → MkTy′ (Id τ) τ'

  data MkTy (τ : FG.Ty) : CG.Ty → Set where
    Labeled : ∀ {τ'} → MkTy′ τ τ' → MkTy τ (Labeled τ')

Bool′ : MkTy′ FG.Bool ⟪ FG.Bool ⟫ᵗ′
Bool′ = Sum (Labeled Unit) (Labeled Unit)

mutual
  mkTy′ : ∀ τ → MkTy′ τ ⟪ τ ⟫ᵗ′
  mkTy′ unit = Unit
  mkTy′ (τ × τ₁) = Prod (mkTy τ) (mkTy τ₁)
  mkTy′ (τ + τ₁) = Sum (mkTy τ) (mkTy τ₁)
  mkTy′ (τ ➔ τ₁) = Fun (mkTy τ) (mkTy τ₁)
  mkTy′ 𝓛 = 𝓛
  mkTy′ (Ref I τ) = Refᴵ (mkTy′ τ)
  mkTy′ (Ref S τ) = Refˢ (mkTy′ τ)
  mkTy′ (Id τ) = Id (mkTy τ)

  mkTy : ∀ τ → MkTy τ ⟪ τ ⟫ᵗ
  mkTy x = Labeled (mkTy′ x)

mutual
  ≡-MkTy : ∀ {τ τ'} → MkTy τ τ' → τ' ≡ ⟪ τ ⟫ᵗ
  ≡-MkTy (Labeled x) = cong Labeled (≡-MkTy′ x)

  ≡-MkTy′ : ∀ {τ τ'} → MkTy′ τ τ' → τ' ≡ ⟪ τ ⟫ᵗ′
  ≡-MkTy′ 𝓛 = refl
  ≡-MkTy′ Unit = refl
  ≡-MkTy′ (Refᴵ x) = cong (Ref I) (≡-MkTy′ x)
  ≡-MkTy′ (Refˢ x) = cong (Ref S) (≡-MkTy′ x)
  ≡-MkTy′ (Sum x x₁) = cong₂ _+_ (≡-MkTy x) (≡-MkTy x₁)
  ≡-MkTy′ (Prod x x₁) = cong₂ CG._×_ (≡-MkTy x) (≡-MkTy x₁)
  ≡-MkTy′ (Fun x x₁) = cong₂ _➔_ (≡-MkTy x) (cong LIO (≡-MkTy x₁))
  ≡-MkTy′ (Id x) rewrite ≡-MkTy x = refl

open import Function.Equivalence

-- The relation MkTy is an equivalent representation for the
-- translation function over types.
MkTy-⟪·⟫ᵗ : ∀ {τ τ'} → τ' ≡ ⟪ τ ⟫ᵗ  ⇔  MkTy τ τ'
MkTy-⟪·⟫ᵗ = equivalence (λ { refl → mkTy _ }) ≡-MkTy

MkTy′-⟪·⟫ᵗ′ : ∀ {τ τ'} → τ' ≡ ⟪ τ ⟫ᵗ′  ⇔  MkTy′ τ τ'
MkTy′-⟪·⟫ᵗ′ = equivalence (λ { refl → mkTy′ _ }) ≡-MkTy′

mutual

  -- Unique proofs
  !-MkTy : ∀ {τ τ'} (x y : MkTy τ τ') → x ≡ y
  !-MkTy (Labeled x) (Labeled y) rewrite !-MkTy′ x y = refl

  !-MkTy′ : ∀ {τ τ'} (x y : MkTy′ τ τ') → x ≡ y
  !-MkTy′ 𝓛 𝓛 = refl
  !-MkTy′ Unit Unit = refl
  !-MkTy′ (Refᴵ x) (Refᴵ y)
    rewrite !-MkTy′ x y = refl
  !-MkTy′ (Refˢ x) (Refˢ y)
    rewrite !-MkTy′ x y = refl
  !-MkTy′ (Sum x₁ x₂) (Sum y₁ y₂)
    rewrite !-MkTy x₁ y₁ | !-MkTy x₂ y₂ = refl
  !-MkTy′ (Prod x₁ x₂) (Prod y₁ y₂)
    rewrite !-MkTy x₁ y₁ | !-MkTy x₂ y₂ = refl
  !-MkTy′ (Fun x₁ x₂) (Fun y₁ y₂)
    rewrite !-MkTy x₁ y₁ | !-MkTy x₂ y₂ = refl
  !-MkTy′ (Id x) (Id y)
    rewrite !-MkTy x y = refl

--------------------------------------------------------------------------------

-- Graph instances

open import Generic.Graph

Graph-⟪·⟫ᵗ : Graph ⟪_⟫ᵗ
Graph-⟪·⟫ᵗ = record { P = MkTy ; ⌜_⌝ = mkTy ; ⌞_⌟ = ≡-MkTy }

Graph-⟪·⟫ᵗ′ : Graph ⟪_⟫ᵗ′
Graph-⟪·⟫ᵗ′ = record { P = MkTy′ ; ⌜_⌝ = mkTy′ ; ⌞_⌟ = ≡-MkTy′ }

-- Derive graph of context generically.
open import Generic.Context.Graph {FG.Ty} {CG.Ty} {⟪_⟫ᵗ} Graph-⟪·⟫ᵗ
  renaming ( S2Tᶜ to MkCtx
           ; mkS2Tᶜ to mkCtx
           ; ≡-S2Tᶜ to ≡-MkCtx
           ; S2T-∈ to Fg2Cg-∈
           ; mkS2T-∈ to mkFg2Cg-∈
           ; ≡-S2T-∈ to ≡-Fg2Cg-∈
           ; S2T-⊆ to Fg2Cg-⊆
           ; mkS2T-⊆ to mkFg2Cg-⊆
           ; ≡-S2T-⊆ to ≡-Fg2Cg-⊆ ) public

-- Derive uniqueness proof generically.
open Unique !-MkTy renaming (!-S2Tᶜ to !-MkCtx) public
