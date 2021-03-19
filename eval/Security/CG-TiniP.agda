tiniᴾ : ∀ {τ Γ θ₁ θ₂ v₁ v₂ β} {e : Expr Γ τ} →
         e ⇓ᴾ⟨ θ₁ ⟩ v₁ →
         e ⇓ᴾ⟨ θ₂ ⟩ v₂ →
         θ₁ ≈⟨ β ⟩ᴱ θ₂ →
         v₁ ≈⟨ β ⟩ⱽ v₂
tiniᴾ Unit Unit θ₁≈θ₂ = Unit
tiniᴾ (Lbl ℓ) (Lbl .ℓ) θ₁≈θ₂ = Lbl ℓ
tiniᴾ (Test₁ _ _ ℓ₁⊑ℓ₂) (Test₁ _ _ _) _ = Inl Unit
tiniᴾ (Test₂ x₁ x₂ ℓ₁⋤ℓ₂) (Test₁ x₃ x₄  ℓ₁⊑ℓ₂) θ₁≈θ₂ with tiniᴾ x₁ x₃ θ₁≈θ₂ | tiniᴾ x₂ x₄ θ₁≈θ₂
... | Lbl ℓ₁ | Lbl ℓ₂ = ⊥-elim (ℓ₁⋤ℓ₂ ℓ₁⊑ℓ₂)
tiniᴾ (Test₁ x₁ x₂ ℓ₁⊑ℓ₂) (Test₂ x₃ x₄ ℓ₁⋤ℓ₂) θ₁≈θ₂ with tiniᴾ x₁ x₃ θ₁≈θ₂ | tiniᴾ x₂ x₄ θ₁≈θ₂
... | Lbl ℓ₁ | Lbl ℓ₂ = ⊥-elim (ℓ₁⋤ℓ₂ ℓ₁⊑ℓ₂)
tiniᴾ (Test₂ _ _ _) (Test₂ _ _ _) _ = Inr Unit
tiniᴾ (Wken p x) (Wken .p x₁) θ₁≈θ₂ = tiniᴾ x x₁ (slice-≈ᴱ θ₁≈θ₂ p)
tiniᴾ (Var τ∈Γ) (Var .τ∈Γ) θ₁≈θ₂ = lookup-≈ⱽ τ∈Γ θ₁≈θ₂
tiniᴾ SThunk SThunk θ₁≈θ₂ = Thunk′ θ₁≈θ₂
tiniᴾ Fun Fun θ₁≈θ₂ = Fun θ₁≈θ₂
tiniᴾ (App x x₁ x₂) (App x₃ x₄ x₅) θ₁≈θ₂ with tiniᴾ x x₃ θ₁≈θ₂
... | Fun θ₁'≈θ₂'  with tiniᴾ x₁ x₄ θ₁≈θ₂
... | v₁≈v₂ = tiniᴾ x₂ x₅ (v₁≈v₂ ∷ θ₁'≈θ₂')
tiniᴾ (Inl x) (Inl x₁) θ₁≈θ₂ = Inl (tiniᴾ x x₁ θ₁≈θ₂)
tiniᴾ (Inr x) (Inr x₁) θ₁≈θ₂ = Inr (tiniᴾ x x₁ θ₁≈θ₂)
tiniᴾ (Case₁ x x₁) (Case₁ x₂ x₃) θ₁≈θ₂ with tiniᴾ x x₂ θ₁≈θ₂
tiniᴾ (Case₁ x x₁) (Case₁ x₂ x₃) θ₁≈θ₂ | Inl v₁≈v₂ = tiniᴾ x₁ x₃ (v₁≈v₂ ∷ θ₁≈θ₂)
tiniᴾ (Case₁ x x₁) (Case₂ x₂ x₃) θ₁≈θ₂ with tiniᴾ x x₂ θ₁≈θ₂
tiniᴾ (Case₁ x x₁) (Case₂ x₂ x₃) θ₁≈θ₂ | ()
tiniᴾ (Case₂ x x₁) (Case₁ x₂ x₃) θ₁≈θ₂ with tiniᴾ x x₂ θ₁≈θ₂
tiniᴾ (Case₂ x x₁) (Case₁ x₂ x₃) θ₁≈θ₂ | ()
tiniᴾ (Case₂ x x₁) (Case₂ x₂ x₃) θ₁≈θ₂ with tiniᴾ x x₂ θ₁≈θ₂
tiniᴾ (Case₂ x x₁) (Case₂ x₂ x₃) θ₁≈θ₂ | Inr v₁≈v₂ = tiniᴾ x₁ x₃ (v₁≈v₂ ∷ θ₁≈θ₂)
tiniᴾ (Pair x x₁) (Pair x₂ x₃) θ₁≈θ₂ = Pair (tiniᴾ x x₂ θ₁≈θ₂) (tiniᴾ x₁ x₃ θ₁≈θ₂)
tiniᴾ (Fst x) (Fst x₁) θ₁≈θ₂ with tiniᴾ x x₁ θ₁≈θ₂
tiniᴾ (Fst x) (Fst x₁) θ₁≈θ₂ | Pair v₁≈v₁' v₂≈v₂' = v₁≈v₁'
tiniᴾ (Snd x) (Snd x₁) θ₁≈θ₂ with tiniᴾ x x₁ θ₁≈θ₂
tiniᴾ (Snd x) (Snd x₁) θ₁≈θ₂ | Pair v₁≈v₂ v₁≈v₃ = v₁≈v₃
