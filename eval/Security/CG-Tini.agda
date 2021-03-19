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
