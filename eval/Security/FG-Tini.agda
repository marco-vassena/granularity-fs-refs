  tini : ∀ {τ Γ θ₁ θ₂ pc β} {c₁ c₂ : IConf Γ τ} {c₁' c₂' : FConf τ} →
             {{valid₁ : Valid-Inputs c₁ θ₁}} {{valid₂ : Valid-Inputs c₂ θ₂}} →
             c₁ ⇓⟨ θ₁ , pc ⟩ c₁' →
             c₂ ⇓⟨ θ₂ , pc ⟩ c₂' →
             c₁ ≈⟨ β ⟩ᴵ c₂ →
             θ₁ ≈⟨ β ⟩ᴱ θ₂ →
             ∃ (λ β' → β ⊆ β' × c₁' ≈⟨ β' ⟩ᶜ c₂')
  tini {pc = pc} x₁ x₂ ⟨ ≈ᴾ , refl ⟩  θ₁≈θ₂ with pc ⊑? A
  ... | yes pc⊑A = tiniᴸ x₁ x₂ ≈ᴾ θ₁≈θ₂ pc⊑A
  ... | no pc⋤A = tiniᴴ ≈ᴾ x₁ x₂ pc⋤A pc⋤A
