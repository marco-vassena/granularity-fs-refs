  stepᶠ-≈ᴾ : ∀ {τ Γ θ} {c : EConf Γ (LIO τ)} {c' : FConf τ} →
               let ⟨ Σ , μ , pc , e ⟩ = c
                   ⟨ Σ' , μ' , _ , _ ⟩ = c' in
               {{validᴾ : Validᴾ ⟨ Σ , μ ⟩ }} {{validᴱ : Validᴱ ∥ μ ∥ᴴ θ}} →
               c ⇓ᶠ⟨ θ ⟩ c' →
               pc ⋤ A →
               ⟨ Σ , μ ⟩ ≈⟨ ι ∥ μ ∥ᴴ ⟩ᴾ ⟨ Σ' , μ' ⟩
  stepᶠ-≈ᴾ {{isVᴾ}} {{isVᴱ}} (Force x y) pc⋤A = step-≈ᴾ {{isVᴾ}} {{ isVᴱ′ }} y pc⋤A
    where isVᴱ′ = validⱽ-⇓ᴾ x isVᴱ

  -- High steps preserve low-equivalence of stores
  step-≈ᴾ : ∀ {τ Γ θ} {c : TConf Γ (LIO τ)} {c' : FConf τ} →
               let ⟨ Σ , μ , pc , t ⟩ = c
                   ⟨ Σ' , μ' ,  _ , _ ⟩ = c' in
               {{validᴾ : Validᴾ ⟨ Σ , μ ⟩ }} {{validᴱ : Validᴱ ∥ μ ∥ᴴ θ}} →
               c ⇓⟨ θ ⟩ c' →
               pc ⋤ A →
               ⟨ Σ , μ ⟩ ≈⟨ ι ∥ μ ∥ᴴ ⟩ᴾ ⟨ Σ' , μ' ⟩
  step-≈ᴾ (Return x) pc⋤A = refl-≈ᴾ

  step-≈ᴾ {{isVᴾ}} {{isVᴱ}} (Bind x x₁) pc⋤A =
    let isVᴾ′ ∧ isVᴱ′′ = valid-⇓ᶠ x (isVᴾ ∧ isVᴱ)
        ≈ᴾ′ = stepᶠ-≈ᴾ x pc⋤A
        ≈ᴾ′′ = stepᶠ-≈ᴾ {{ isVᴾ′ }} {{ isVᴱ′′ }} x₁ (trans-⋤ (stepᶠ-⊑ x) pc⋤A)
    in trans-≈ᴾ-ι ≈ᴾ′ ≈ᴾ′′

  step-≈ᴾ (Unlabel x eq) pc⋤A = refl-≈ᴾ
  step-≈ᴾ (ToLabeled x) pc⋤A = stepᶠ-≈ᴾ x pc⋤A
  step-≈ᴾ (LabelOf x x₁) pc⋤A = refl-≈ᴾ
  step-≈ᴾ GetLabel pc⋤A = refl-≈ᴾ
  step-≈ᴾ (Taint x x₁) pc⋤A = refl-≈ᴾ

  step-≈ᴾ {{isVᴾ}} (New x pc⊑ℓ) pc⋤A = ⟨ ≈ˢ , ≈ᴴ ⟩
    where ≈ˢ = updateᴴ-≈ˢ {{ validˢ isVᴾ }} (trans-⋤ pc⊑ℓ pc⋤A)
          ≈ᴴ = refl-≈ᴴ {{ validᴴ isVᴾ }}

  step-≈ᴾ (Read x n∈M eq) pc⋤A = refl-≈ᴾ

  step-≈ᴾ {{isVᴾ}} (Write x x₁ pc⊑ℓ x₃ up) pc⋤A = ⟨ ≈ˢ , ≈ᴴ ⟩
    where ≈ˢ = updateᴴ-≈ˢ {{ validˢ isVᴾ }} (trans-⋤ pc⊑ℓ pc⋤A)
          ≈ᴴ = refl-≈ᴴ {{ validᴴ isVᴾ }}

  step-≈ᴾ (LabelOfRef x eq) pc⋤A = refl-≈ᴾ

  step-≈ᴾ {{isVᴾ}} (New-FS x x₁) pc⋤A = ⟨ ≈ˢ , ≈ᴴ ⟩
    where ≈ˢ = refl-≈ˢ {{ validˢ isVᴾ }}
          ≈ᴴ = snoc-≈ᴴ _ (refl-≈ᴴ {{validᴴ isVᴾ}} )

  step-≈ᴾ (Read-FS x n∈μ eq) pc⋤A = refl-≈ᴾ

  step-≈ᴾ {{isVᴾ}} (Write-FS x x₁ n∈μ ⊑₁ refl w) pc⋤A = ⟨ ≈ˢ , ≈ᴴ ⟩
    where ≈ˢ = refl-≈ˢ {{ validˢ isVᴾ }}
          v≈ = Labeledᴴ (trans-⋤ ⊑₁ pc⋤A) (join-⋤₁ pc⋤A)
          ≈ᴴ = writeᴴ-≈ᴴ {{ validᴴ isVᴾ }} n∈μ w v≈

  step-≈ᴾ (LabelOfRef-FS x n∈μ eq) pc⋤A = refl-≈ᴾ
