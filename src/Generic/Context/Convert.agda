module Generic.Context.Convert {Ty₁ Ty₂ : Set} (⟪_⟫ᵗ : Ty₁ → Ty₂) where

import Generic.Context.Base as B

module C₁ = B Ty₁
module C₂ = B Ty₂

-- Type-generic pointwise context transformation.
⟪_⟫ᶜ : C₁.Ctx → C₂.Ctx
⟪ C₁.[] ⟫ᶜ = C₂.[]
⟪ τ C₁.∷ Γ ⟫ᶜ = ⟪ τ ⟫ᵗ C₂.∷ ⟪ Γ ⟫ᶜ

-- If a source type is in scope in a source context, i.e., τ ∈ Γ, then
-- the transformed target type is in scope in the transformed CG
-- context, i.e., ⟪ τ ⟫ᵗ ∈ ⟪ Γ ⟫ᶜ.
⟪_⟫∈ : ∀ {τ Γ} → τ C₁.∈ Γ → ⟪ τ ⟫ᵗ C₂.∈ ⟪ Γ ⟫ᶜ
⟪ C₁.here ⟫∈ = C₂.here
⟪ C₁.there τ∈Γ ⟫∈ = C₂.there ⟪ τ∈Γ ⟫∈

-- Subset relation for is preserved by context transformation.
⟪_⟫⊆ : ∀ {Γ₁ Γ₂} → Γ₁ C₁.⊆ Γ₂ → ⟪ Γ₁ ⟫ᶜ C₂.⊆ ⟪ Γ₂ ⟫ᶜ
⟪ C₁.base ⟫⊆ = C₂.base
⟪ C₁.cons p ⟫⊆ = C₂.cons ⟪ p ⟫⊆
⟪ C₁.drop p ⟫⊆ = C₂.drop ⟪ p ⟫⊆
