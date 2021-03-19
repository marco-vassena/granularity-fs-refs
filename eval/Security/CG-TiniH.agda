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
