  tiniᴸ : ∀ {pc β τ Γ μ₁ μ₂ Σ₁ Σ₂ e} {θ₁ θ₂ : Env Γ} {c₁' c₂' : FConf τ} →
                    let c₁ = ⟨ Σ₁ , μ₁ , e ⟩
                        c₂ = ⟨ Σ₂ , μ₂ , e ⟩ in
                    {{valid₁ : Valid-Inputs c₁ θ₁}} {{valid₂ : Valid-Inputs c₂ θ₂}} →
                    c₁ ⇓⟨ θ₁ , pc ⟩ c₁' →
                    c₂ ⇓⟨ θ₂ , pc ⟩ c₂' →
                    ⟨ Σ₁ , μ₁ ⟩ ≈⟨ β ⟩ᴾ ⟨ Σ₂ , μ₂ ⟩ →
                    θ₁ ≈⟨ β ⟩ᴱ θ₂ →
                    pc ⊑ A →
                    ∃ (λ β' → β ⊆ β' × c₁' ≈⟨ β' ⟩ᶜ c₂')

  tiniᴸ (Var τ∈Γ refl) (Var .τ∈Γ refl) ≈ᴾ θ₁≈θ₂ pc⊑A = _ ∧ refl-⊆ ∧ ⟨ ≈ᴾ , ≈ⱽ-⊑ _ v₁≈v₂ ⟩
    where v₁≈v₂ = lookup-≈ⱽ τ∈Γ θ₁≈θ₂

  tiniᴸ Unit Unit ≈ᴾ θ₁≈θ₂ pc⊑A = _ ∧ refl-⊆ ∧ ⟨ ≈ᴾ , Valueᴸ pc⊑A Unit ⟩

  tiniᴸ (Lbl ℓ) (Lbl .ℓ) ≈ᴾ θ₁≈θ₂ pc⊑A = _ ∧ refl-⊆ ∧ ⟨ ≈ᴾ , Valueᴸ pc⊑A (Lbl ℓ) ⟩

  --------------------------------------------------------------------------------
  -- Test cases

  -- Both true
  tiniᴸ {{isV₁}} {{isV₂}} (Test₁ x₁ x₂ ℓ₁⊑ℓ₂ refl) (Test₁ y₁ y₂ _ refl) ≈ᴾ θ₁≈θ₂ pc⊑A with tiniᴸ x₁ y₁ ≈ᴾ θ₁≈θ₂ pc⊑A
  ... | β' ∧ β⊆β' ∧ ⟨  ≈ᴾ′ , Valueᴸ _ (Lbl ℓ₁) ⟩
    with tiniᴸ {{ validᴾ-⇓ x₁ isV₁ }} {{ validᴾ-⇓ y₁ isV₂ }} x₂ y₂ ≈ᴾ′ (wken-≈ᴱ β⊆β' θ₁≈θ₂) pc⊑A

  tiniᴸ (Test₁ x₁ x₂ ℓ₁⊑ℓ₂ refl) (Test₁ y₁ y₂ _ refl) ≈ᴾ θ₁≈θ₂ pc⊑A
    | β' ∧ β⊆β' ∧ ⟨ ≈ᴾ′ , Valueᴸ p₁ (Lbl ℓ₁) ⟩ | β'' ∧ β'⊆β'' ∧ ⟨ ≈ᴾ′′ , Valueᴸ p₂ (Lbl ℓ₂) ⟩
      = β'' ∧ trans-⊆ β⊆β' β'⊆β'' ∧ ⟨ ≈ᴾ′′ , Valueᴸ (join-⊑' p₁ p₂) (Trueᴸ pc⊑A) ⟩

  tiniᴸ (Test₁ x₁ x₂ ℓ₁⊑ℓ₂ refl) (Test₁ y₁ y₂ _ refl) ≈ᴾ θ₁≈θ₂ pc⊑A
    | β' ∧ β⊆β' ∧ ⟨ ≈ᴾ′ , Valueᴸ p (Lbl ℓ₁) ⟩ | β'' ∧ β'⊆β'' ∧ ⟨ ≈ᴾ′′ , Valueᴴ ¬p₁ ¬p₂ ⟩
      = β'' ∧ trans-⊆ β⊆β' β'⊆β'' ∧ ⟨ ≈ᴾ′′ , Valueᴴ (join-⋤₂ ¬p₁) (join-⋤₂ ¬p₂) ⟩

  tiniᴸ {{isV₁}} {{isV₂}} (Test₁ x₁ x₂ ℓ₁⊑ℓ₂ refl) (Test₁ y₁ y₂ _ refl) ≈ᴾ θ₁≈θ₂ pc⊑A
    | β' ∧ β⊆β' ∧ ⟨ ≈ᴾ′ , Valueᴴ pc⋤ℓ₁' pc⋤ℓ₂' ⟩
    with tiniᴸ {{ validᴾ-⇓ x₁ isV₁ }} {{ validᴾ-⇓ y₁ isV₂ }} x₂ y₂ ≈ᴾ′ (wken-≈ᴱ β⊆β' θ₁≈θ₂) pc⊑A
  ... |  β'' ∧ β'⊆β'' ∧ ⟨ ≈ᴾ′′ , v≈ ⟩
    = β'' ∧ trans-⊆ β⊆β' β'⊆β'' ∧ ⟨ ≈ᴾ′′ , Valueᴴ (join-⋤₁ pc⋤ℓ₁') (join-⋤₁ pc⋤ℓ₂') ⟩

    -- True vs False
  tiniᴸ {{isV₁}} {{isV₂}} (Test₁ x₁ x₂ ℓ₁⊑ℓ₂ refl) (Test₂ y₁ y₂ ℓ₁⋤ℓ₂ refl) ≈ᴾ θ₁≈θ₂ pc⊑A with tiniᴸ x₁ y₁ ≈ᴾ θ₁≈θ₂ pc⊑A
  ... | _ ∧ β⊆β' ∧ ⟨ ≈ᴾ′ , Valueᴸ _ (Lbl ℓ₁) ⟩
    with tiniᴸ {{ validᴾ-⇓ x₁ ( isV₁) }} {{ validᴾ-⇓ y₁ (isV₂) }} x₂ y₂ ≈ᴾ′ (wken-≈ᴱ β⊆β' θ₁≈θ₂) pc⊑A

  tiniᴸ (Test₁ x₁ x₂ ℓ₁⊑ℓ₂ refl) (Test₂ y₁ y₂ ℓ₁⋤ℓ₂ refl) ≈ᴾ θ₁≈θ₂ pc⊑A
    | _ ∧ _ ∧  ⟨ ≈ᴾ′ , Valueᴸ p₁ (Lbl ℓ₁) ⟩ | _ ∧ _ ∧ ⟨ ≈ᴾ′′ , Valueᴸ p₂ (Lbl ℓ₂) ⟩
      = ⊥-elim (ℓ₁⋤ℓ₂ ℓ₁⊑ℓ₂)

  tiniᴸ (Test₁ x₁ x₂ ℓ₁⊑ℓ₂ refl) (Test₂ y₁ y₂ _ refl) ≈ᴾ θ₁≈θ₂ pc⊑A
    | β' ∧ β⊆β' ∧ ⟨ ≈ᴾ′ , Valueᴸ p (Lbl ℓ₁) ⟩ | β'' ∧ β'⊆β'' ∧ ⟨ ≈ᴾ′′ , Valueᴴ ¬p₁ ¬p₂ ⟩
      = β'' ∧ trans-⊆ β⊆β' β'⊆β'' ∧ ⟨ ≈ᴾ′′ , Valueᴴ (join-⋤₂ ¬p₁) (join-⋤₂ ¬p₂) ⟩

  tiniᴸ {{isV₁}} {{isV₂}} (Test₁ x₁ x₂ ℓ₁⊑ℓ₂ refl) (Test₂ y₁ y₂ _ refl) ≈ᴾ θ₁≈θ₂ pc⊑A
    | β' ∧ β⊆β' ∧ ⟨ ≈ᴾ′ , Valueᴴ pc⋤ℓ₁' pc⋤ℓ₂' ⟩
    with tiniᴸ {{ validᴾ-⇓ x₁ ( isV₁) }} {{ validᴾ-⇓ y₁ (isV₂) }}  x₂ y₂ ≈ᴾ′ (wken-≈ᴱ β⊆β' θ₁≈θ₂) pc⊑A
  ... | β'' ∧ β'⊆β'' ∧ ⟨ ≈ᴾ′′ , v≈ ⟩ = β'' ∧ trans-⊆ β⊆β' β'⊆β'' ∧ ⟨ ≈ᴾ′′ , Valueᴴ (join-⋤₁ pc⋤ℓ₁') (join-⋤₁ pc⋤ℓ₂') ⟩

  -- False vs True
  tiniᴸ {{isV₁}} {{isV₂}} (Test₂ x₁ x₂ ℓ₁⋤ℓ₂ refl) (Test₁ y₁ y₂ ℓ₁⊑ℓ₂ refl) ≈ᴾ θ₁≈θ₂ pc⊑A with tiniᴸ x₁ y₁ ≈ᴾ θ₁≈θ₂ pc⊑A
  ... | _ ∧ β⊆β' ∧ ⟨ ≈ᴾ′ , Valueᴸ _ (Lbl ℓ₁) ⟩
    with tiniᴸ {{ validᴾ-⇓ x₁ ( isV₁) }} {{ validᴾ-⇓ y₁ (isV₂) }} x₂ y₂ ≈ᴾ′ (wken-≈ᴱ β⊆β' θ₁≈θ₂) pc⊑A

  tiniᴸ (Test₂ x₁ x₂ ℓ₁⋤ℓ₂ refl) (Test₁ y₁ y₂ ℓ₁⊑ℓ₂ refl) ≈ᴾ θ₁≈θ₂ pc⊑A
    | _ ∧ _ ∧ ⟨ ≈ᴾ′ , Valueᴸ p₁ (Lbl ℓ₁) ⟩ | _ ∧ _ ∧ ⟨ ≈ᴾ′′ , Valueᴸ p₂ (Lbl ℓ₂) ⟩
      = ⊥-elim (ℓ₁⋤ℓ₂ ℓ₁⊑ℓ₂)

  tiniᴸ (Test₂ x₁ x₂ ℓ₁⋤ℓ₂ refl) (Test₁ y₁ y₂ _ refl) ≈ᴾ θ₁≈θ₂ pc⊑A
    | β' ∧ β⊆β' ∧ ⟨ ≈ᴾ′ , Valueᴸ p (Lbl ℓ₁) ⟩ | β'' ∧ β'⊆β'' ∧ ⟨ ≈ᴾ′′ , Valueᴴ ¬p₁ ¬p₂ ⟩
    = β'' ∧ trans-⊆ β⊆β' β'⊆β'' ∧ ⟨ ≈ᴾ′′ , Valueᴴ (join-⋤₂ ¬p₁) (join-⋤₂ ¬p₂) ⟩

  tiniᴸ {{isV₁}} {{isV₂}} (Test₂ x₁ x₂ ℓ₁⋤ℓ₂ refl) (Test₁ y₁ y₂ ℓ₁⊑ℓ₂ refl) ≈ᴾ θ₁≈θ₂ pc⊑A
    | β' ∧ β⊆β' ∧ ⟨ ≈ᴾ′ , Valueᴴ pc⋤ℓ₁' pc⋤ℓ₂' ⟩
    with tiniᴸ  {{ validᴾ-⇓ x₁ ( isV₁) }} {{ validᴾ-⇓ y₁ (isV₂) }} x₂ y₂ ≈ᴾ′ (wken-≈ᴱ β⊆β' θ₁≈θ₂) pc⊑A
  ... | β'' ∧ β'⊆β'' ∧ ⟨ ≈ᴾ′′ , v≈ ⟩ = β'' ∧ trans-⊆ β⊆β' β'⊆β'' ∧ ⟨ ≈ᴾ′′ , Valueᴴ (join-⋤₁ pc⋤ℓ₁') (join-⋤₁ pc⋤ℓ₂') ⟩

  -- False and False
  tiniᴸ {{isV₁}} {{isV₂}} (Test₂ x₁ x₂ ℓ₁⋤ℓ₂ refl) (Test₂ y₁ y₂ _ refl) ≈ᴾ θ₁≈θ₂ pc⊑A with tiniᴸ x₁ y₁ ≈ᴾ θ₁≈θ₂ pc⊑A
  ... | β' ∧ β⊆β' ∧ ⟨ ≈ᴾ′ , Valueᴸ _ (Lbl ℓ₁) ⟩
    with tiniᴸ {{ validᴾ-⇓ x₁ ( isV₁) }} {{ validᴾ-⇓ y₁ (isV₂) }}  x₂ y₂ ≈ᴾ′ (wken-≈ᴱ β⊆β' θ₁≈θ₂) pc⊑A

  tiniᴸ (Test₂ x₁ x₂ ℓ₁⋤ℓ₂ refl) (Test₂ y₁ y₂ _ refl) ≈ᴾ θ₁≈θ₂ pc⊑A
    | β' ∧ β⊆β' ∧ ⟨ ≈ᴾ′ , Valueᴸ p₁ (Lbl ℓ₁) ⟩ | β'' ∧ β'⊆β'' ∧ ⟨ ≈ᴾ′′ , Valueᴸ p₂ (Lbl ℓ₂) ⟩
      = β'' ∧ trans-⊆ β⊆β' β'⊆β'' ∧ ⟨ ≈ᴾ′′ , Valueᴸ (join-⊑' p₁ p₂) (Falseᴸ pc⊑A) ⟩

  tiniᴸ (Test₂ x₁ x₂ ℓ₁⋤ℓ₂ refl) (Test₂ y₁ y₂ _ refl) ≈ᴾ θ₁≈θ₂ pc⊑A
    | β' ∧ β⊆β' ∧ ⟨ ≈ᴾ′ , Valueᴸ p (Lbl ℓ₁) ⟩ | β'' ∧ β'⊆β'' ∧ ⟨ ≈ᴾ′′ , Valueᴴ ¬p₁ ¬p₂ ⟩
      = β'' ∧ trans-⊆ β⊆β' β'⊆β'' ∧ ⟨ ≈ᴾ′′ , Valueᴴ (join-⋤₂ ¬p₁) (join-⋤₂ ¬p₂) ⟩

  tiniᴸ {{isV₁}} {{isV₂}} (Test₂ x₁ x₂ ℓ₁⋤ℓ₂ refl) (Test₂ y₁ y₂ _ refl) ≈ᴾ θ₁≈θ₂ pc⊑A
    | β' ∧ β⊆β' ∧ ⟨ ≈ᴾ′ , Valueᴴ pc⋤ℓ₁' pc⋤ℓ₂' ⟩
    with tiniᴸ {{ validᴾ-⇓ x₁ ( isV₁) }} {{ validᴾ-⇓ y₁ (isV₂) }} x₂ y₂ ≈ᴾ′ (wken-≈ᴱ β⊆β' θ₁≈θ₂) pc⊑A
  ... | β'' ∧ β'⊆β'' ∧ ⟨ ≈ᴾ′′ , v≈ ⟩
    = β'' ∧ trans-⊆ β⊆β' β'⊆β'' ∧ ⟨ ≈ᴾ′′ , Valueᴴ (join-⋤₁ pc⋤ℓ₁') (join-⋤₁ pc⋤ℓ₂') ⟩

  -- End Test Cases
  --------------------------------------------------------------------------------

  tiniᴸ Fun Fun ≈ᴾ θ₁≈θ₂ pc⊑A = _ ∧ refl-⊆ ∧ ⟨ ≈ᴾ , Valueᴸ pc⊑A (Fun θ₁≈θ₂) ⟩

  --------------------------------------------------------------------------------
  -- App Cases

  tiniᴸ {{isV₁}} {{isV₂}} (App x₁ x₂ eq₁ x₃) (App y₁ y₂ eq₂ y₃) ≈ᴾ θ≈ pc⊑A with tiniᴸ x₁ y₁ ≈ᴾ θ≈ pc⊑A
  ... | β' ∧ β⊆β' ∧ ⟨ ≈ᴾ′ , v₁≈v₂ ⟩ with valid-invariant x₁ ( isV₁) | valid-invariant y₁ (isV₂)
  ... | isV₁ᴱ′ ∧ isV₁ᴾ′ ∧ isV₁ᴱ′′ | isV₂ᴱ′ ∧ isV₂ᴾ′ ∧ isV₂ᴱ′′
    with tiniᴸ {{ isV₁ᴾ′ ∧ isV₁ᴱ′ }} {{ isV₂ᴾ′ ∧ isV₂ᴱ′ }} x₂ y₂ ≈ᴾ′ (wken-≈ᴱ β⊆β' θ≈) pc⊑A

  -- Public closure
  tiniᴸ {{isV₁}} {{isV₂}} (App x₁ x₂ refl x₃) (App y₁ y₂ refl y₃) ≈ᴾ θ≈ pc⊑A
    | β' ∧ β⊆β' ∧ ⟨ ≈ᴾ′ , Valueᴸ pc⊑ℓ' (Fun θ≈′) ⟩ | isV₁ᴱ′ ∧ isV₁ᴾ′ ∧ isV₁ᴱ′′ | isV₂ᴱ′ ∧ isV₂ᴾ′ ∧ isV₂ᴱ′′
    | β'' ∧ β'⊆β'' ∧ ⟨ ≈ᴾ′′ , v₁'≈v₂' ⟩
       = let _ ∧ isV₁ᴾ′′ ∧ isV₁ⱽ = valid-invariant x₂ (isV₁ᴾ′ ∧ isV₁ᴱ′)
             _ ∧ isV₂ᴾ′′ ∧ isV₂ⱽ = valid-invariant y₂ (isV₂ᴾ′ ∧ isV₂ᴱ′)
             vi₁ = isV₁ᴾ′′ ∧ (isV₁ⱽ ∧ wken-valid _ (step-≤ x₂) isV₁ᴱ′′)
             vi₂ = isV₂ᴾ′′ ∧ (isV₂ⱽ ∧ wken-valid _ (step-≤ y₂) isV₂ᴱ′′)
             θ≈′′ = v₁'≈v₂' ∷ wken-≈ᴱ β'⊆β'' θ≈′
             ≈₁ = tini {{ vi₁ }} {{ vi₂ }} x₃ y₃  ⟨ ≈ᴾ′′ , refl ⟩ θ≈′′  in
             wken-∃ (trans-⊆ β⊆β' β'⊆β'') ≈₁


  -- Secret closure
  tiniᴸ {{isV₁}} {{isV₂}} (App x₁ x₂ refl x₃) (App y₁ y₂ refl y₃) ≈ᴾ θ≈ pc⊑A
    | β' ∧ β⊆β' ∧ ⟨ ≈ᴾ′ , Valueᴴ pc⋤ℓ₁ pc⋤ℓ₂ ⟩ | isV₁ᴱ′ ∧ isV₁ᴾ′ ∧ isV₁ᴱ′′ | isV₂ᴱ′ ∧ isV₂ᴾ′ ∧ isV₂ᴱ′′
    | β'' ∧ β'⊆β'' ∧ ⟨ ≈ᴾ′′ , v₁'≈v₂' ⟩
      = let _ ∧ isV₁ᴾ′′ ∧ isV₁ⱽ = valid-invariant x₂ (isV₁ᴾ′ ∧ isV₁ᴱ′)
            _ ∧ isV₂ᴾ′′ ∧ isV₂ⱽ = valid-invariant y₂ (isV₂ᴾ′ ∧ isV₂ᴱ′)
            vi₁ = (isV₁ᴾ′′ ∧ isV₁ⱽ ∧ wken-valid _ (step-≤ x₂) isV₁ᴱ′′)
            vi₂ = (isV₂ᴾ′′ ∧ isV₂ⱽ ∧ wken-valid _ (step-≤ y₂) isV₂ᴱ′′)
            ≈₁ = tiniᴴ {{ vi₁ }} {{ vi₂ }} ≈ᴾ′′ x₃ y₃ (join-⋤₂ pc⋤ℓ₁) (join-⋤₂ pc⋤ℓ₂) in
            wken-∃ (trans-⊆ β⊆β' β'⊆β'') ≈₁

  -- End App Cases
  --------------------------------------------------------------------------------

  tiniᴸ {{ isV₁ᴾ ∧ isV₁ᴱ }} {{ isV₂ᴾ ∧ isV₂ᴱ}} (Wken p x) (Wken .p y) ≈ᴾ θ≈ pc⊑A =
    let θ≈′ = slice-≈ᴱ θ≈ p
        isV₁ᴱ′ = slice-validᴱ _ p isV₁ᴱ
        isV₂ᴱ′ = slice-validᴱ _ p isV₂ᴱ in
        tiniᴸ {{ isV₁ᴾ ∧ isV₁ᴱ′ }} {{ isV₂ᴾ ∧ isV₂ᴱ′ }} x y ≈ᴾ θ≈′ pc⊑A

  tiniᴸ (Inl x) (Inl x₁) ≈ᴾ θ₁≈θ₂ pc⊑A with tiniᴸ x x₁ ≈ᴾ θ₁≈θ₂ pc⊑A
  ... | β' ∧ β⊆β' ∧ ⟨ ≈ᴾ′ , v₁≈v₂ ⟩ =  β' ∧ β⊆β' ∧ ⟨ ≈ᴾ′ , Valueᴸ pc⊑A (Inl v₁≈v₂) ⟩

  tiniᴸ (Inr x) (Inr x₁) ≈ᴾ θ₁≈θ₂ pc⊑A with tiniᴸ x x₁ ≈ᴾ θ₁≈θ₂ pc⊑A
  ... | β' ∧ β⊆β' ∧ ⟨ ≈ᴾ′ , v₁≈v₂ ⟩ = β' ∧ β⊆β' ∧ ⟨ ≈ᴾ′ , Valueᴸ pc⊑A (Inr v₁≈v₂) ⟩


  --------------------------------------------------------------------------------
  -- Case inspection

  -- Both left
  tiniᴸ {{isV₁}} {{isV₂}} (Case₁ x₁ refl x₂) (Case₁ y₁ refl y₂) ≈ᴾ θ≈ pc⊑A with tiniᴸ x₁ y₁ ≈ᴾ θ≈ pc⊑A
  ... | β' ∧ β⊆β' ∧ ⟨ ≈ᴾ′ , Valueᴸ ℓ⊑A (Inl v≈) ⟩ =
    let isV₁ᴱ′ ∧ isV₁ᴾ′ ∧ isV₁ⱽ = valid-invariant x₁ (isV₁)
        isV₂ᴱ′ ∧ isV₂ᴾ′ ∧ isV₂ⱽ = valid-invariant y₁ (isV₂)
        vi₁ = isV₁ᴾ′ ∧ isV₁ⱽ ∧ isV₁ᴱ′
        vi₂ = isV₂ᴾ′ ∧ isV₂ⱽ ∧ isV₂ᴱ′
        θ≈′ = v≈ ∷ wken-≈ᴱ β⊆β' θ≈  in
        wken-∃ β⊆β' (tini {{ vi₁ }} {{ vi₂ }} x₂ y₂ ⟨ ≈ᴾ′ , refl ⟩ θ≈′)

  ... | β' ∧ β⊆β' ∧ ⟨ ≈ᴾ′ , (Valueᴴ ℓ₁⋤A ℓ₂⋤A) ⟩ =
    let isV₁ᴱ′ ∧ isV₁ᴾ′ ∧ isV₁ⱽ = valid-invariant x₁ (isV₁)
        isV₂ᴱ′ ∧ isV₂ᴾ′ ∧ isV₂ⱽ = valid-invariant y₁ (isV₂)
        vi₁ = isV₁ᴾ′ ∧ isV₁ⱽ ∧ isV₁ᴱ′
        vi₂ = isV₂ᴾ′ ∧ isV₂ⱽ ∧ isV₂ᴱ′ in
        wken-∃ β⊆β' (tiniᴴ {{ vi₁ }} {{ vi₂ }} ≈ᴾ′ x₂ y₂ (join-⋤₂ ℓ₁⋤A) (join-⋤₂ ℓ₂⋤A))

  -- Left vs right
  tiniᴸ {{isV₁}} {{isV₂}} (Case₁ x₁ refl x₂) (Case₂ y₁ refl y₂) ≈ᴾ θ≈ pc⊑A with tiniᴸ x₁ y₁ ≈ᴾ θ≈ pc⊑A
  ... | β' ∧ β⊆β' ∧ ⟨ ≈ᴾ′ , Valueᴸ ℓ⊑A () ⟩   -- Public scrutinee with different injections (impossible)
  ... | β' ∧ β⊆β' ∧ ⟨ ≈ᴾ′ , Valueᴴ ℓ₁⋤A ℓ₂⋤A ⟩ =
    let isV₁ᴱ′ ∧ isV₁ᴾ′ ∧ isV₁ⱽ = valid-invariant x₁ (isV₁)
        isV₂ᴱ′ ∧ isV₂ᴾ′ ∧ isV₂ⱽ = valid-invariant y₁ (isV₂)
        vi₁ = isV₁ᴾ′ ∧ isV₁ⱽ ∧ isV₁ᴱ′
        vi₂ = isV₂ᴾ′ ∧ isV₂ⱽ ∧ isV₂ᴱ′ in
        wken-∃ β⊆β' (tiniᴴ {{ vi₁ }} {{ vi₂ }} ≈ᴾ′ x₂ y₂ (join-⋤₂ ℓ₁⋤A) (join-⋤₂ ℓ₂⋤A)) -- Secret scrutinee

  -- Right vs left (like above)
  tiniᴸ {{isV₁}} {{isV₂}} (Case₂ x₁ refl x₂) (Case₁ y₁ refl y₂) ≈ᴾ θ≈ pc⊑A with tiniᴸ x₁ y₁ ≈ᴾ θ≈ pc⊑A
  ... | β' ∧ β⊆β' ∧ ⟨ ≈ᴾ′ , Valueᴸ ℓ⊑A () ⟩
  ... | β' ∧ β⊆β' ∧ ⟨ ≈ᴾ′ , Valueᴴ ℓ₁⋤A ℓ₂⋤A ⟩ =
    let isV₁ᴱ′ ∧ isV₁ᴾ′ ∧ isV₁ⱽ = valid-invariant x₁ (isV₁)
        isV₂ᴱ′ ∧ isV₂ᴾ′ ∧ isV₂ⱽ = valid-invariant y₁ (isV₂)
        vi₁ = isV₁ᴾ′ ∧ isV₁ⱽ ∧ isV₁ᴱ′
        vi₂ = isV₂ᴾ′ ∧ isV₂ⱽ ∧ isV₂ᴱ′ in
        wken-∃ β⊆β' (tiniᴴ {{ vi₁ }} {{ vi₂ }} ≈ᴾ′ x₂ y₂ (join-⋤₂ ℓ₁⋤A) (join-⋤₂ ℓ₂⋤A)) -- Secret scrutinee

  -- Both right
  tiniᴸ {{isV₁}} {{isV₂}} (Case₂ x₁ refl x₂) (Case₂ y₁ refl y₂) ≈ᴾ θ≈ pc⊑A with tiniᴸ x₁ y₁ ≈ᴾ θ≈ pc⊑A
  ... | β' ∧ β⊆β' ∧ ⟨ ≈ᴾ′ , Valueᴸ ℓ⊑A (Inr v≈) ⟩ =
    let isV₁ᴱ′ ∧ isV₁ᴾ′ ∧ isV₁ⱽ = valid-invariant x₁ (isV₁)
        isV₂ᴱ′ ∧ isV₂ᴾ′ ∧ isV₂ⱽ = valid-invariant y₁ (isV₂)
        vi₁ = isV₁ᴾ′ ∧ isV₁ⱽ ∧ isV₁ᴱ′
        vi₂ = isV₂ᴾ′ ∧ isV₂ⱽ ∧ isV₂ᴱ′
        θ≈′ = v≈ ∷ wken-≈ᴱ β⊆β' θ≈  in
        wken-∃ β⊆β' (tini {{ vi₁ }} {{ vi₂ }} x₂ y₂ ⟨ ≈ᴾ′ , refl ⟩ θ≈′)


  ... | β' ∧ β⊆β' ∧ ⟨ ≈ᴾ′ , Valueᴴ ℓ₁⋤A ℓ₂⋤A ⟩ =
    let isV₁ᴱ′ ∧ isV₁ᴾ′ ∧ isV₁ⱽ = valid-invariant x₁ (isV₁)
        isV₂ᴱ′ ∧ isV₂ᴾ′ ∧ isV₂ⱽ = valid-invariant y₁ (isV₂)
        vi₁ = isV₁ᴾ′ ∧ isV₁ⱽ ∧ isV₁ᴱ′
        vi₂ = isV₂ᴾ′ ∧ isV₂ⱽ ∧ isV₂ᴱ′ in
        wken-∃ β⊆β' (tiniᴴ {{ vi₁ }} {{ vi₂ }} ≈ᴾ′ x₂ y₂ (join-⋤₂ ℓ₁⋤A) (join-⋤₂ ℓ₂⋤A))

  -- End case inspection cases
  --------------------------------------------------------------------------------

  tiniᴸ {{isV₁}} {{isV₂}} (Pair x₁ x₂) (Pair y₁ y₂) ≈ᴾ θ₁≈θ₂ pc⊑A with tiniᴸ x₁ y₁ ≈ᴾ θ₁≈θ₂ pc⊑A
  ... | β' ∧ β⊆β' ∧ ⟨ ≈ᴾ′ , v₁≈v₁' ⟩ with tiniᴸ {{ validᴾ-⇓ x₁ ( isV₁) }} {{ validᴾ-⇓ y₁ (isV₂) }} x₂ y₂ ≈ᴾ′ (wken-≈ᴱ β⊆β' θ₁≈θ₂) pc⊑A
  ... | β'' ∧ β'⊆β'' ∧ ⟨ ≈ᴾ′′ , v₂≈v₂' ⟩ = β'' ∧ trans-⊆ β⊆β' β'⊆β'' ∧ ⟨ ≈ᴾ′′ , Valueᴸ pc⊑A (Pair (wken-≈ⱽ β'⊆β'' v₁≈v₁') v₂≈v₂') ⟩

  tiniᴸ (Fst x refl) (Fst x₂ refl) ≈ᴾ θ₁≈θ₂ pc⊑A with tiniᴸ x x₂ ≈ᴾ θ₁≈θ₂ pc⊑A
  ... | β' ∧ β⊆β' ∧ ⟨ ≈ᴾ′ , Valueᴸ ℓ⊑A (Pair v₁≈v₁' v₂≈v₂') ⟩ = β' ∧ β⊆β' ∧ ⟨ ≈ᴾ′ , ≈ⱽ-⊑ _ v₁≈v₁' ⟩
  ... | β' ∧ β⊆β' ∧ ⟨ ≈ᴾ′ , Valueᴴ ℓ₁⋤A ℓ₂⋤A ⟩ = β' ∧ β⊆β' ∧ ⟨ ≈ᴾ′ , Valueᴴ (join-⋤₁ ℓ₁⋤A) (join-⋤₁ ℓ₂⋤A) ⟩

  tiniᴸ (Snd x refl) (Snd x₂ refl) ≈ᴾ θ₁≈θ₂ pc⊑A with tiniᴸ x x₂ ≈ᴾ θ₁≈θ₂ pc⊑A
  ... | β' ∧ β⊆β' ∧ ⟨ ≈ᴾ′ , Valueᴸ ℓ⊑A (Pair v₁≈v₁' v₂≈v₂') ⟩ = β' ∧ β⊆β' ∧ ⟨ ≈ᴾ′ , ≈ⱽ-⊑ _ v₂≈v₂' ⟩
  ... | β' ∧ β⊆β' ∧ ⟨ ≈ᴾ′ , Valueᴴ ℓ₁⋤A ℓ₂⋤A ⟩ = β' ∧ β⊆β' ∧ ⟨ ≈ᴾ′ , Valueᴴ (join-⋤₁ ℓ₁⋤A) (join-⋤₁ ℓ₂⋤A) ⟩

  tiniᴸ (LabelOf x) (LabelOf x₁) ≈ᴾ θ₁≈θ₂ pc⊑A with tiniᴸ x x₁ ≈ᴾ θ₁≈θ₂ pc⊑A
  ... | β' ∧ β⊆β' ∧ ⟨ ≈ᴾ′ , Valueᴸ ℓ⊑A v₁≈v₂ ⟩ = β' ∧ β⊆β' ∧ ⟨ ≈ᴾ′ , Valueᴸ ℓ⊑A (Lbl _) ⟩
  ... | β' ∧ β⊆β' ∧ ⟨ ≈ᴾ′ , Valueᴴ ℓ₁⋤A ℓ₂⋤A ⟩ = β' ∧ β⊆β' ∧ ⟨ ≈ᴾ′ , Valueᴴ ℓ₁⋤A ℓ₂⋤A ⟩

  tiniᴸ GetLabel GetLabel ≈ᴾ θ₁≈θ₂ pc⊑A = _ ∧ refl-⊆ ∧ ⟨ ≈ᴾ , Valueᴸ pc⊑A (Lbl _) ⟩

  tiniᴸ {{isV₁}} {{isV₂}} (Taint refl x₁ x₂ ⊑₁) (Taint refl y₁ y₂ ⊑₂) ≈ᴾ θ₁≈θ₂ pc⊑A with tiniᴸ x₁ y₁ ≈ᴾ θ₁≈θ₂ pc⊑A
  ... | β' ∧ β⊆β' ∧ ⟨ ≈ᴾ′ , Valueᴸ ℓ⊑A (Lbl ℓ) ⟩ =
    let isV₁ᴱ′ ∧ isV₁ᴾ′ ∧ isV₁ⱽ = valid-invariant x₁ (isV₁)
        isV₂ᴱ′ ∧ isV₂ᴾ′ ∧ isV₂ⱽ = valid-invariant y₁ (isV₂)
        vi₁ = (isV₁ᴾ′ ∧ isV₁ᴱ′)
        vi₂ = (isV₂ᴾ′ ∧ isV₂ᴱ′) in
        wken-∃ β⊆β' (tini {{ vi₁ }} {{ vi₂ }} x₂ y₂ ⟨ ≈ᴾ′ , refl ⟩ (wken-≈ᴱ β⊆β' θ₁≈θ₂))

  ... | β' ∧ β⊆β' ∧ ⟨ ≈ᴾ′ , (Valueᴴ ℓ₁⋤A ℓ₂⋤A) ⟩ =
    let isV₁ᴱ′ ∧ isV₁ᴾ′ ∧ isV₁ⱽ = valid-invariant x₁ (isV₁)
        isV₂ᴱ′ ∧ isV₂ᴾ′ ∧ isV₂ⱽ = valid-invariant y₁ (isV₂)
        vi₁ = (isV₁ᴾ′ ∧ isV₁ᴱ′)
        vi₂ = (isV₂ᴾ′ ∧ isV₂ᴱ′) in
        wken-∃ β⊆β' (tiniᴴ {{ vi₁ }} {{ vi₂ }} ≈ᴾ′ x₂ y₂ (trans-⋤ ⊑₁ ℓ₁⋤A) (trans-⋤ ⊑₂ ℓ₂⋤A))


  tiniᴸ (LabelOfRef x₁ refl) (LabelOfRef x₂ refl) ≈ᴾ θ₁≈θ₂ pc⊑A with tiniᴸ x₁ x₂ ≈ᴾ θ₁≈θ₂ pc⊑A
  ... | β' ∧ β⊆β' ∧ ⟨ ≈ᴾ′ , Valueᴸ ℓ⊑A (Ref-Iᴸ ℓ⊑A₁) ⟩ = β' ∧ β⊆β' ∧ ⟨ ≈ᴾ′ , (Valueᴸ (join-⊑' ℓ⊑A₁ ℓ⊑A) (Lbl _)) ⟩
  ... | β' ∧ β⊆β' ∧ ⟨ ≈ᴾ′ , Valueᴸ ℓ⊑A (Ref-Iᴴ ℓ₁⋤A ℓ₂⋤A) ⟩ = β' ∧ β⊆β' ∧ ⟨ ≈ᴾ′ , (Valueᴴ (join-⋤₁ ℓ₁⋤A) (join-⋤₁ ℓ₂⋤A)) ⟩
  ... | β' ∧ β⊆β' ∧ ⟨ ≈ᴾ′ , Valueᴴ ℓ₁⋤A ℓ₂⋤A ⟩ = β' ∧ β⊆β' ∧ ⟨ ≈ᴾ′ , Valueᴴ (join-⋤₂ ℓ₁⋤A) (join-⋤₂ ℓ₂⋤A) ⟩

  tiniᴸ {{isV₁}} {{isV₂}} (New x₁) (New y₁) ≈ᴾ θ₁≈θ₂ pc⊑A with tiniᴸ x₁ y₁ ≈ᴾ θ₁≈θ₂ pc⊑A
  ... | β' ∧ β⊆β' ∧ ⟨ ⟨ Σ≈ , μ≈ ⟩ , Valueᴴ ⋤₁ ⋤₂  ⟩ =
    let isV₁ᴾ′ ∧ _  = validᴾ-⇓ x₁ isV₁
        isV₂ᴾ′ ∧ _  = validᴾ-⇓ y₁ isV₂
        Σ₁≈ = updateᴴ-≈ˢ {{ validˢ isV₁ᴾ′ }} ⋤₁
        Σ₂≈ = updateᴴ-≈ˢ {{ validˢ isV₂ᴾ′ }} ⋤₂
        Σ≈′ = square-≈ˢ-ι Σ≈ Σ₁≈ Σ₂≈ ⊆ᴿ-ι ⊆ᴰ-ι
        v≈′ = Valueᴸ pc⊑A (Ref-Iᴴ ⋤₁ ⋤₂) in
        β' ∧ β⊆β' ∧ ⟨ ⟨ Σ≈′ , μ≈ ⟩ , v≈′ ⟩
    where open _≈⟨_⟩ᴴ_ μ≈

  ... | β' ∧ β⊆β' ∧ ⟨ ⟨ Σ≈ , μ≈ ⟩ , Valueᴸ ℓ⊑A r≈ ⟩ = β' ∧ β⊆β' ∧ ⟨ ⟨ Σ≈′ , μ≈ ⟩ , v≈′ ⟩
      where M≈ = getᴸ Σ≈ ℓ⊑A
            Σ≈′ = updateᴸ-≈ˢ Σ≈ (new-≈ᴹ M≈  r≈)
            v≈′ = Valueᴸ pc⊑A (Ref-Iᴸ′ ℓ⊑A ∥ M≈ ∥-≡)

  -- Read public reference
  tiniᴸ (Read x₁ n∈M₁ refl) (Read x₂ n∈M₂ refl) ≈ᴾ θ₁≈θ₂ pc⊑A with tiniᴸ x₁ x₂ ≈ᴾ θ₁≈θ₂ pc⊑A
  ... | β' ∧ β⊆β' ∧ ⟨ ⟨ Σ≈ , μ≈ ⟩ , Valueᴸ ℓ⊑A (Ref-Iᴸ ℓ'⊑A) ⟩ = β' ∧ β⊆β' ∧ ⟨ ⟨ Σ≈ , μ≈ ⟩ , v≈ ⟩
       where M≈ = getᴸ Σ≈ ℓ'⊑A
             v≈ = Valueᴸ (join-⊑' ℓ'⊑A ℓ⊑A) (read-≈ᴹ M≈ n∈M₁ n∈M₂)

  -- Read secret reference.
  ... | β' ∧ β⊆β' ∧ ⟨ ≈ᴾ′ , Valueᴸ ℓ⊑A (Ref-Iᴴ ℓ₁⋤A ℓ₂⋤A) ⟩ = β' ∧ β⊆β' ∧ ⟨ ≈ᴾ′ , v≈ ⟩
    where v≈ = Valueᴴ (join-⋤₁ ℓ₁⋤A) (join-⋤₁ ℓ₂⋤A)

  -- Read secret-dependent reference
  ... | β' ∧ β⊆β' ∧ ⟨ ≈ᴾ′ , Valueᴴ ℓ₁⋤A ℓ₂⋤A ⟩ = β' ∧ β⊆β' ∧ ⟨ ≈ᴾ′ , v≈ ⟩
    where v≈ = Valueᴴ (join-⋤₂ ℓ₁⋤A) (join-⋤₂ ℓ₂⋤A)

  tiniᴸ {{isV₁}} {{isV₂}} (Write x₁ ⊑₁ x₂ ℓ₂⊑ℓ w₁) (Write y₁ ⊑₂ y₂ ℓ₂⊑ℓ' w₂) ≈ᴾ θ₁≈θ₂ pc⊑A
    with  validᴾ-⇓ x₁ isV₁ | validᴾ-⇓ y₁ isV₂ | tiniᴸ x₁ y₁ ≈ᴾ θ₁≈θ₂ pc⊑A

  -- Write low-data to a secret-dependent reference
  ... | isV₁′ | isV₂′ | β' ∧ β⊆β' ∧ ⟨ ≈ᴾ′ , Valueᴴ ℓ₁⋤A ℓ₂⋤A ⟩
    with tiniᴸ {{ isV₁′ }} {{ isV₂′ }} x₂ y₂ ≈ᴾ′ (wken-≈ᴱ β⊆β' θ₁≈θ₂) pc⊑A
  ... | β'' ∧ β'⊆β'' ∧ ⟨ ⟨ Σ≈ , μ≈ ⟩  , v≈ ⟩ =
    let isV₁ᴾ′′ ∧ _  = validᴾ-⇓ x₂ isV₁′
        isV₂ᴾ′′ ∧ _  = validᴾ-⇓ y₂ isV₂′
        Σ₁≈ = updateᴴ-≈ˢ {{ validˢ isV₁ᴾ′′ }} (trans-⋤ ⊑₁ ℓ₁⋤A)
        Σ₂≈ = updateᴴ-≈ˢ {{ validˢ isV₂ᴾ′′ }} (trans-⋤ ⊑₂ ℓ₂⋤A)
        Σ≈′ = square-≈ˢ-ι Σ≈ Σ₁≈ Σ₂≈ ⊆ᴿ-ι ⊆ᴰ-ι in
        β'' ∧ trans-⊆ β⊆β' β'⊆β'' ∧ ⟨ ⟨ Σ≈′ , μ≈ ⟩ , Valueᴸ pc⊑A Unit ⟩
    where open _≈⟨_⟩ᴴ_ μ≈

  -- Write low data to low reference
  tiniᴸ {{isV₁}} {{isV₂}} (Write x₁ ℓ'⊑ℓ x₂ ℓ₂⊑ℓ w₁) (Write y₁ ℓ'⊑ℓ' y₂ ℓ₂⊑ℓ' w₂) ≈ᴾ θ₁≈θ₂ pc⊑A
    | isV₁′ | isV₂′ | β' ∧ β⊆β'  ∧ ⟨ ≈ᴾ′ , Valueᴸ ℓ⊑A (Ref-Iᴸ ⊑₁) ⟩
    with tiniᴸ {{ isV₁′ }} {{ isV₂′ }} x₂ y₂ ≈ᴾ′ (wken-≈ᴱ β⊆β' θ₁≈θ₂) pc⊑A
  ... | β'' ∧ β'⊆β'' ∧ ⟨ ⟨ Σ≈ , μ≈ ⟩ , v≈ ⟩ = β'' ∧ trans-⊆ β⊆β' β'⊆β'' ∧ ⟨ ⟨ Σ≈′ , μ≈ ⟩ , Valueᴸ pc⊑A Unit ⟩
      where M≈ = getᴸ Σ≈ ⊑₁
            Σ≈′ = updateᴸ-≈ˢ Σ≈ (update-≈ᴹ M≈ (extract-≈ᴿ v≈ (trans-⊑ ℓ₂⊑ℓ ⊑₁)) w₁ w₂)

  -- Write low data to high reference
  tiniᴸ  {{isV₁}} {{isV₂}} (Write x₁ ⊑₁ x₂ ⊑₁′ w₁) (Write y₁ ⊑₂ y₂ ⊑₂′ w₂) ≈ᴾ θ₁≈θ₂ pc⊑A
    | isV₁′ | isV₂′ | β' ∧ β⊆β'  ∧ ⟨ ≈ᴾ′ , Valueᴸ ℓ⊑A (Ref-Iᴴ ⋤₁ ⋤₂) ⟩
    with tiniᴸ {{ isV₁′ }} {{ isV₂′ }} x₂ y₂ ≈ᴾ′ (wken-≈ᴱ β⊆β' θ₁≈θ₂) pc⊑A
  ... | β'' ∧ β'⊆β'' ∧ ⟨ ⟨ Σ≈ , μ≈ ⟩ , v≈ ⟩ =
    let isV₁ᴾ′′ ∧ _  = validᴾ-⇓ x₂ isV₁′
        isV₂ᴾ′′ ∧ _  = validᴾ-⇓ y₂ isV₂′
        Σ₁≈ = updateᴴ-≈ˢ {{ validˢ isV₁ᴾ′′ }} ⋤₁
        Σ₂≈ = updateᴴ-≈ˢ {{ validˢ isV₂ᴾ′′ }} ⋤₂
        Σ≈′ = square-≈ˢ-ι Σ≈ Σ₁≈ Σ₂≈ ⊆ᴿ-ι ⊆ᴰ-ι in
        β'' ∧ trans-⊆ β⊆β' β'⊆β'' ∧ ⟨ ⟨ Σ≈′ , μ≈ ⟩ , Valueᴸ pc⊑A Unit ⟩
    where open _≈⟨_⟩ᴴ_ μ≈

  tiniᴸ (Id x₁) (Id x₂) ≈ᴾ θ₁≈θ₂ pc⊑A with  tiniᴸ x₁ x₂ ≈ᴾ θ₁≈θ₂ pc⊑A
  ... | β' ∧ β⊆β' ∧ ⟨ ≈ᴾ′ , v≈ ⟩ = β' ∧ β⊆β' ∧ ⟨ ≈ᴾ′ , Valueᴸ pc⊑A (Id v≈) ⟩

  tiniᴸ (UnId x₁ refl) (UnId x₂ refl) ≈ᴾ θ₁≈θ₂ pc⊑A with tiniᴸ x₁ x₂ ≈ᴾ θ₁≈θ₂ pc⊑A
  ... | β' ∧ β⊆β' ∧ ⟨ ≈ᴾ′ , Valueᴸ ℓ⊑A (Id v≈) ⟩ = β' ∧ β⊆β' ∧ ⟨ ≈ᴾ′ , ≈ⱽ-⊑ _ v≈ ⟩
  ... | β' ∧ β⊆β' ∧ ⟨ ≈ᴾ′ , Valueᴴ ℓ₁⋤A ℓ₂⋤A ⟩ = β' ∧ β⊆β' ∧ ⟨ ≈ᴾ′ , Valueᴴ (join-⋤₁ ℓ₁⋤A) (join-⋤₁ ℓ₂⋤A) ⟩

  tiniᴸ (LabelOfRef-FS x₁ ∈₁ refl) (LabelOfRef-FS x₂ ∈₂ refl) ≈ᴾ θ₁≈θ₂ pc⊑A with tiniᴸ x₁ x₂ ≈ᴾ θ₁≈θ₂ pc⊑A
  ... | β' ∧ β⊆β' ∧ ⟨ ⟨ Σ≈ , μ≈ ⟩ , Valueᴸ ℓ⊑A (Ref-S ∈β') ⟩ = β' ∧ β⊆β' ∧ ⟨ ⟨ Σ≈ , μ≈ ⟩ , v≈ ⟩
    where v≈ = ≈ⱽ-⊑ _ (label-of-≈ⱽ (readᴸ-≈ⱽ ∈β' ∈₁ ∈₂ μ≈))
  ... | β' ∧ β⊆β' ∧ ⟨ ≈ᴾ′ , Valueᴴ ℓ₁⋤A ℓ₂⋤A ⟩ = β' ∧ β⊆β' ∧ ⟨ ≈ᴾ′ , Valueᴴ (join-⋤₁ ℓ₁⋤A) (join-⋤₁ ℓ₂⋤A) ⟩

  tiniᴸ (New-FS {μ' = μ₁'} x₁) (New-FS {μ' = μ₂'} x₂) ≈ᴾ θ₁≈θ₂ pc⊑A with tiniᴸ x₁ x₂ ≈ᴾ θ₁≈θ₂ pc⊑A
  ... | β' ∧ β⊆β' ∧ ⟨ ⟨ Σ≈ , μ≈ ⟩ , v≈  ⟩ = β'' ∧ β⊆β'' ∧ ⟨ ⟨ wken-≈ˢ ⊆₁ Σ≈ , μ≈′ ⟩ , wken-≈ⱽ ⊆₂ v≈′ ⟩
      where
        instance _ = _≟_
                 _ = ≈-# μ≈
        β₁ =  ∥ μ₁' ∥ᴴ ↔ ∥ μ₂' ∥ᴴ
        β'' = β' ∣ᴮ β₁
        ⊆₁ = ∣ᴮ-⊆₁ β' β₁
        ⊆₂ = ∣ᴮ-⊆₂ β' β₁
        β⊆β'' = trans-⊆ β⊆β' ⊆₁
        μ≈′ = newᴸ-≈ᴴ v≈ μ≈
        v≈′ = Valueᴸ pc⊑A (Ref-S (↔-∈ᵗ ∥ μ₁' ∥ᴴ ∥ μ₂' ∥ᴴ))

  tiniᴸ (Read-FS x₁ ∈₁ refl) (Read-FS x₂ ∈₂ refl) ≈ᴾ θ₁≈θ₂ pc⊑A with tiniᴸ x₁ x₂ ≈ᴾ θ₁≈θ₂ pc⊑A

  ... | β' ∧ β⊆β' ∧ ⟨ ≈ᴾ′ , Valueᴴ ℓ₁⋤A ℓ₂⋤A ⟩ = β' ∧ β⊆β' ∧ ⟨ ≈ᴾ′ , v≈ ⟩
    where v≈ = Valueᴴ (join-⋤₁ ℓ₁⋤A) (join-⋤₁ ℓ₂⋤A)

  ... | β' ∧ β⊆β' ∧ ⟨  ⟨ Σ≈ , μ≈ ⟩ , Valueᴸ ℓ⊑A (Ref-S ∈β) ⟩ = β' ∧ β⊆β' ∧ ⟨ ⟨ Σ≈ , μ≈ ⟩ , ≈ⱽ-⊑ _ v≈ ⟩
       where v≈ = readᴸ-≈ⱽ ∈β ∈₁ ∈₂ μ≈

  tiniᴸ  {{isV₁}} {{isV₂}} (Write-FS x₁ x₂ ∈₁ ⊑₁ refl w₁) (Write-FS y₁ y₂ ∈₂ ⊑₂ refl w₂) ≈ᴾ θ₁≈θ₂ pc⊑A
    with  validᴾ-⇓ x₁ (isV₁) | validᴾ-⇓ y₁ (isV₂) | tiniᴸ x₁ y₁ ≈ᴾ θ₁≈θ₂ pc⊑A
  ... | isV₁′ | isV₂′ | β' ∧ β⊆β' ∧ ⟨ ≈ᴾ′ , (Valueᴸ ℓ⊑A (Ref-S ∈β')) ⟩
    with tiniᴸ {{ isV₁′ }} {{ isV₂′ }} x₂ y₂ ≈ᴾ′ (wken-≈ᴱ β⊆β' θ₁≈θ₂) pc⊑A
  ... | β'' ∧ β'⊆β'' ∧ ⟨ ⟨ Σ≈ , μ≈ ⟩ , v≈′ ⟩ =
            let ∈β'' = bij-⊆ β'⊆β'' ∈β'
                v≈ = readᴸ-≈ⱽ ∈β'' ∈₁ ∈₂ μ≈
                μ≈′ = writeᴸ-≈ᴴ μ≈ (≈ⱽ-⊑ _ v≈′) w₁ w₂ ∈β'' in
                β'' ∧ trans-⊆ β⊆β' β'⊆β'' ∧ ⟨ ⟨ Σ≈ , μ≈′ ⟩ , Valueᴸ pc⊑A Unit ⟩

  tiniᴸ  {{isV₁}} {{isV₂}} (Write-FS x₁ x₂ ∈₁ ⊑₁ refl w₁) (Write-FS y₁ y₂ ∈₂ ⊑₂ refl w₂) ≈ᴾ θ₁≈θ₂ pc⊑A
    | isV₁′ | isV₂′ | β' ∧ β⊆β' ∧ ⟨ ≈ᴾ′ , (Valueᴴ ℓ₁⋤A ℓ₂⋤A) ⟩
    with tiniᴸ {{ isV₁′ }} {{ isV₂′ }} x₂ y₂ ≈ᴾ′ (wken-≈ᴱ β⊆β' θ₁≈θ₂) pc⊑A
  ... | β'' ∧ β'⊆β'' ∧ ⟨ ⟨ Σ≈ , μ≈ ⟩ , v≈ ⟩ =
    let v≈₁ = Valueᴴ (trans-⋤ ⊑₁ ℓ₁⋤A) (join-⋤₁ ℓ₁⋤A)
        v≈₂ = Valueᴴ (trans-⋤ ⊑₂ ℓ₂⋤A) (join-⋤₁ ℓ₂⋤A)
        isV₁ᴾ′′ ∧ _ = validᴾ-⇓ x₂ isV₁′
        isV₂ᴾ′′ ∧ _ = validᴾ-⇓ y₂ isV₂′
        μ≈₁ = writeᴴ-≈ᴴ {{ validᴴ isV₁ᴾ′′ }} ∈₁ w₁ v≈₁
        μ≈₂ = writeᴴ-≈ᴴ {{ validᴴ isV₂ᴾ′′ }} ∈₂ w₂ v≈₂
        μ≈′ = square-≈ᴴ-ι μ≈  μ≈₁ μ≈₂ in
        β'' ∧ trans-⊆ β⊆β' β'⊆β'' ∧ ⟨ ⟨ Σ≈ , μ≈′ ⟩ , Valueᴸ pc⊑A Unit ⟩
