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
