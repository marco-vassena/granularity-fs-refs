step-≈ᴾ : ∀ {τ Γ θ pc} {c : IConf Γ τ} {c' : FConf τ} →
             let ⟨ Σ , μ , _ ⟩ = c
                 ⟨ Σ' , μ' , _ ⟩ = c' in
                 {{validᴾ : Validᴾ ⟨ Σ , μ ⟩ }} {{validᴱ : Validᴱ ∥ μ ∥ᴴ θ}} →
               c ⇓⟨ θ , pc ⟩ c' →
               pc ⋤ A →
               ⟨ Σ , μ ⟩ ≈⟨ ι ∥ μ ∥ᴴ ⟩ᴾ ⟨ Σ' , μ' ⟩

step-≈ᴾ (Var τ∈Γ x) pc⋤A = refl-≈ᴾ

step-≈ᴾ Unit pc⋤A = refl-≈ᴾ

step-≈ᴾ (Lbl ℓ) pc⋤A = refl-≈ᴾ

step-≈ᴾ {{isVᴾ}} {{isVᴱ}} (Test₁ x x₁ ℓ⊑ refl) pc⋤A =
  let isVᴱ′ ∧ isVᴾ′ ∧ _ = valid-invariant x (isVᴾ ∧ isVᴱ)
      ≈ᴾ′ = step-≈ᴾ x pc⋤A
      ≈ᴾ′′ = step-≈ᴾ {{ isVᴾ′}} {{isVᴱ′}} x₁ pc⋤A
  in trans-≈ᴾ-ι ≈ᴾ′ ≈ᴾ′′

step-≈ᴾ {{isVᴾ}} {{isVᴱ}} (Test₂ x x₁ ℓ⊑ refl) pc⋤A =
  let isVᴱ′′ ∧ isVᴾ′ ∧ isVᴱ′ = valid-invariant x (isVᴾ ∧ isVᴱ)
      ≈ᴾ′ = step-≈ᴾ x pc⋤A
      ≈ᴾ′′ = step-≈ᴾ {{ isVᴾ′ }} {{ isVᴱ′′ }} x₁ pc⋤A
  in trans-≈ᴾ-ι ≈ᴾ′ ≈ᴾ′′

step-≈ᴾ Fun pc⋤A = refl-≈ᴾ

step-≈ᴾ {{isVᴾ}} {{isVᴱ}} (App x₁ x₂ refl x₃) pc⋤A =
  let isV₁ᴱ ∧ isVᴾ′ ∧ isVᴱ′ = valid-invariant x₁ (isVᴾ ∧ isVᴱ)
      _ ∧ isVᴾ′′ ∧ isVⱽ = valid-invariant x₂ (isVᴾ′ ∧ isV₁ᴱ)
      ≈ᴾ′ = step-≈ᴾ x₁ pc⋤A
      ≈ᴾ′′ = step-≈ᴾ {{ isVᴾ′ }} {{ isV₁ᴱ }} x₂ pc⋤A
      isVᴱ′′ = wken-valid _ (step-≤ x₂) isVᴱ′
      ≈ᴾ′′′ = step-≈ᴾ {{ isVᴾ′′ }} {{  isVⱽ ∧ isVᴱ′′  }} x₃ (join-⋤₁ pc⋤A)
  in trans-≈ᴾ-ι ≈ᴾ′ (trans-≈ᴾ-ι ≈ᴾ′′ ≈ᴾ′′′)

step-≈ᴾ {{isVᴾ}} {{isVᴱ}} (Wken p x) pc⋤A = step-≈ᴾ {{ isVᴾ }} {{ slice-validᴱ _ p isVᴱ }} x pc⋤A

step-≈ᴾ (Inl x) pc⋤A = step-≈ᴾ x pc⋤A

step-≈ᴾ (Inr x) pc⋤A = step-≈ᴾ x pc⋤A

step-≈ᴾ {{isVᴾ}} {{isVᴱ}} (Case₁ x₁ refl x₂) pc⋤A =
  let isVᴱ′ ∧ isVᴾ′ ∧ isVⱽ = valid-invariant x₁ (isVᴾ ∧ isVᴱ)
      ≈ᴾ′ = step-≈ᴾ x₁ pc⋤A
      ≈ᴾ′′ = step-≈ᴾ {{ isVᴾ′ }} {{ isVⱽ ∧ isVᴱ′ }} x₂ (join-⋤₁ pc⋤A)
  in trans-≈ᴾ-ι ≈ᴾ′ ≈ᴾ′′

step-≈ᴾ {{isVᴾ}} {{isVᴱ}} (Case₂ x refl x₁) pc⋤A =
  let isVᴱ′ ∧ isVᴾ′ ∧ isVⱽ = valid-invariant x (isVᴾ ∧ isVᴱ)
      ≈ᴾ′ = step-≈ᴾ x pc⋤A
      ≈ᴾ′′ = step-≈ᴾ {{ isVᴾ′ }} {{ isVⱽ ∧ isVᴱ′ }} x₁ (join-⋤₁ pc⋤A)
  in trans-≈ᴾ-ι ≈ᴾ′ ≈ᴾ′′

step-≈ᴾ {{isVᴾ}} {{isVᴱ}} (Pair x x₁) pc⋤A =
  let isVᴱ′ ∧ isVᴾ′ ∧ _ = valid-invariant x (isVᴾ ∧ isVᴱ)
      ≈ᴾ′ = step-≈ᴾ x pc⋤A
      ≈ᴾ′′ = step-≈ᴾ {{ isVᴾ′ }} {{ isVᴱ′ }} x₁ pc⋤A
  in trans-≈ᴾ-ι ≈ᴾ′ ≈ᴾ′′

step-≈ᴾ (Fst x refl) pc⋤A = step-≈ᴾ x pc⋤A

step-≈ᴾ (Snd x x₁) pc⋤A = step-≈ᴾ x pc⋤A

step-≈ᴾ (LabelOf x) pc⋤A = step-≈ᴾ x pc⋤A

step-≈ᴾ GetLabel pc⋤A = refl-≈ᴾ

step-≈ᴾ {{ isVᴾ }} {{isVᴱ}} (Taint refl x x₁ pc'⊑pc'') pc⋤A =
  let isVᴱ′ ∧ isVᴾ′ ∧ _ = valid-invariant x (isVᴾ ∧ isVᴱ)
      ≈ᴾ′ = step-≈ᴾ x pc⋤A
      ≈ᴾ′′ = step-≈ᴾ {{ isVᴾ′ }} {{ isVᴱ′ }} x₁ (join-⋤₁ pc⋤A)
  in trans-≈ᴾ-ι ≈ᴾ′ ≈ᴾ′′

step-≈ᴾ (LabelOfRef x eq) pc⋤A = step-≈ᴾ x pc⋤A

step-≈ᴾ {{isVᴾ}} {{isVᴱ}} (New x) pc⋤A =
  let ⟨ ≈ˢ , ≈ᴴ ⟩ = step-≈ᴾ x pc⋤A
      _ ∧ ⟨ isVˢ′ , isVᴴ′ ⟩ ∧ _ = valid-invariant x (isVᴾ ∧ isVᴱ)
      ≈ˢ′ = updateᴴ-≈ˢ {{ isVˢ′ }} (trans-⋤ (step-⊑ x) pc⋤A) in
      ⟨ trans-≈ˢ-ι (step-≤ x) ≈ˢ ≈ˢ′ , ≈ᴴ ⟩

step-≈ᴾ (Read x x₁ eq) pc⋤A = step-≈ᴾ x pc⋤A

step-≈ᴾ {{isVᴾ}} {{isVᴱ}} (Write x ⊑₁ x₁ ⊑₂ w) pc⋤A =
  let isVᴱ′ ∧ isVᴾ′ ∧ _ = valid-invariant x (isVᴾ ∧ isVᴱ)
      isVᴱ′′ ∧ ⟨ isVˢ′ , isVᴴ′ ⟩ ∧ _ = valid-invariant x₁ (isVᴾ′ ∧ isVᴱ′)
      ≈ᴾ′ = step-≈ᴾ x pc⋤A
      ≈ᴾ′′ = step-≈ᴾ {{ isVᴾ′ }} {{ isVᴱ′ }} x₁ pc⋤A
      ℓ⋤A = trans-⋤ (trans-⊑ (step-⊑ x) ⊑₁) pc⋤A
      ≈ᴾ′′′ = ⟨ updateᴴ-≈ˢ {{ isVˢ′ }} ℓ⋤A , refl-≈ᴴ {{ isVᴴ′ }} ⟩
  in trans-≈ᴾ-ι ≈ᴾ′ (trans-≈ᴾ-ι ≈ᴾ′′ ≈ᴾ′′′)

step-≈ᴾ (LabelOfRef-FS x x₁ eq) pc⋤A = step-≈ᴾ x pc⋤A

-- TODO: Do we need all of them implicits?
step-≈ᴾ {{isVᴾ}} {{isVᴱ}} (New-FS x) pc⋤A =
  let ⟨ ≈ˢ , ≈ᴴ ⟩ = step-≈ᴾ {{ isVᴾ }} {{isVᴱ}} x pc⋤A
      isVᴾ′ ∧ _ = validᴾ-⇓ x (isVᴾ ∧ isVᴱ)
      ≈ˢ′ = trans-≈ˢ-ι (step-≤ x) ≈ˢ (refl-≈ˢ {{ validˢ isVᴾ′ }}) in
      ⟨ ≈ˢ′ , snoc-≈ᴴ _ ≈ᴴ ⟩

step-≈ᴾ (Read-FS x x₁ eq) pc⋤A = step-≈ᴾ x pc⋤A

step-≈ᴾ {{isVᴾ}} {{isVᴱ}} (Write-FS x x₁ ∈₁ ⊑₁ refl w) pc⋤A =
  let isVᴱ′ ∧ isVᴾ′ ∧ _ = valid-invariant x (isVᴾ ∧ isVᴱ)
      isVᴱ′′ ∧ isVᴾ′′ ∧ _ = valid-invariant x₁ (isVᴾ′ ∧ isVᴱ′)
      ≈ᴾ′ = step-≈ᴾ x pc⋤A
      ≈ᴾ′′ = step-≈ᴾ {{ isVᴾ′ }} {{ isVᴱ′ }} x₁ pc⋤A
      v≈ = Valueᴴ (trans-⋤ (trans-⊑ (step-⊑ x) ⊑₁) pc⋤A) (join-⋤₁ (trans-⋤ (step-⊑ x) pc⋤A))
      ≈ᴾ′′′ = writeᴴ-≈ᴴ {{ validᴴ isVᴾ′′ }} ∈₁ w v≈
  in trans-≈ᴾ-ι ≈ᴾ′ (trans-≈ᴾ-ι ≈ᴾ′′ ⟨ refl-≈ˢ {{ validˢ isVᴾ′′ }} , ≈ᴾ′′′ ⟩)
  where open Validᴾ

step-≈ᴾ (Id x) pc⋤A = step-≈ᴾ x pc⋤A

step-≈ᴾ (UnId x eq) pc⋤A = step-≈ᴾ x pc⋤A
