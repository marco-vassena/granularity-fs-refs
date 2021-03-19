  tiniᴴ : ∀ {τ Γ₁ Γ₂ θ₁ θ₂ pc₁ pc₂ β} {c₁ : IConf Γ₁ τ} {c₂ : IConf Γ₂ τ} {c₁' c₂' : FConf τ} →
             let ⟨ Σ₁ , μ₁ , _ ⟩ = c₁
                 ⟨ Σ₂ , μ₂ , _ ⟩ = c₂ in
             {{valid₁ : Valid-Inputs c₁ θ₁}} {{valid₂ : Valid-Inputs c₂ θ₂}} →
             ⟨ Σ₁ , μ₁ ⟩ ≈⟨ β ⟩ᴾ ⟨ Σ₂ , μ₂ ⟩ →
             c₁ ⇓⟨ θ₁ , pc₁ ⟩ c₁' →
             c₂ ⇓⟨ θ₂ , pc₂ ⟩ c₂' →
             pc₁ ⋤ A → pc₂ ⋤ A →
             ∃ (λ β' → β ⊆ β' × c₁' ≈⟨ β' ⟩ᶜ c₂')
  tiniᴴ {β = β} {{isV₁ᴾ ∧ isV₁ᴱ}} {{isV₂ᴾ  ∧ isV₂ᴱ}}
         ≈ᴾ x₁ x₂ pc₁⋤A pc₂⋤A =
    let ≈₁ᴾ = step-≈ᴾ {{ isV₁ᴾ }} {{ isV₁ᴱ }} x₁ pc₁⋤A
        ≈₂ᴾ = step-≈ᴾ {{ isV₂ᴾ }} {{ isV₂ᴱ }} x₂ pc₂⋤A
        ≈ᴾ′ = square-≈ᴾ-ι ≈ᴾ ≈₁ᴾ ≈₂ᴾ
        v≈ = Valueᴴ (trans-⋤ (step-⊑ x₁) pc₁⋤A) (trans-⋤ (step-⊑ x₂) pc₂⋤A) in
        β ∧ B.refl-⊆ ∧ ⟨ ≈ᴾ′ , v≈ ⟩

