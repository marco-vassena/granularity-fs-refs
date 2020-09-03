open import Lattice

module CG2FG.Graph.Expr {{𝑳 : Lattice}} where

open import FG as FG
open import CG as CG
open import CG2FG.Syntax
open import Relation.Binary.PropositionalEquality
open import CG2FG.Graph.Types

-- Not that the following relations are indexed over the corresponding
-- relations over types and contexts because the functions that they
-- model transform the type and contexts indices of the input
-- expression as well.

mutual

  data Cg2Fgᴱ {Γ Γ'} (c : MkCtx Γ Γ') : ∀ {τ τ'} → MkTy τ τ' → CG.Expr Γ τ → FG.Expr Γ' τ' → Set where

    instance
      Unit : Cg2Fgᴱ c Unit （） （）

      Lbl : ∀ ℓ → Cg2Fgᴱ c 𝓛 ⌞ ℓ ⌟ ⌞ ℓ ⌟

      Test : ∀ {e₁ e₂ : CG.Expr Γ 𝓛} {e₁' e₂'} →
               Cg2Fgᴱ c 𝓛 e₁ e₁' →
               Cg2Fgᴱ c 𝓛 e₂ e₂' →
               Cg2Fgᴱ c Bool′ (e₁ ⊑-? e₂) (e₁' ⊑-? e₂')

      Var : ∀ {τ τ' p} {τ∈Γ : τ CG.∈ Γ} {τ∈Γ' : τ' FG.∈ Γ'} →
              Cg2Fg-∈ p c τ∈Γ τ∈Γ' →
              Cg2Fgᴱ  c p (var τ∈Γ) (var τ∈Γ')

      Fun : ∀ {τ₁ τ₂ τ₁' τ₂' p₁ p₂} {e : CG.Expr (τ₁ CG.∷ Γ) τ₂} {e' : FG.Expr (τ₁' FG.∷ Γ') τ₂'} →
              Cg2Fgᴱ (p₁ ∷ c) p₂ e e' →
              Cg2Fgᴱ c (Fun p₁ p₂) (Λ e) (Λ e')

      App : ∀ {τ₁ τ₂ τ₁' τ₂' p₁ p₂} {e₁ : CG.Expr Γ (τ₁ ➔ τ₂)} {e₁' : FG.Expr Γ' (τ₁' ➔ τ₂')} →
              {e₂ : CG.Expr Γ τ₁} {e₂' : FG.Expr Γ' τ₁'} →
              Cg2Fgᴱ c (Fun p₁ p₂) e₁ e₁' →
              Cg2Fgᴱ c p₁ e₂ e₂' →
              Cg2Fgᴱ c p₂ (e₁ ∘ e₂) (e₁' ∘ e₂')

      Pair : ∀ {τ₁ τ₂ τ₁' τ₂' e₁ e₁' e₂ e₂'} {p₁ : MkTy τ₁ τ₁'} {p₂ : MkTy τ₂ τ₂'} →
               Cg2Fgᴱ c p₁ e₁ e₁' →
               Cg2Fgᴱ c p₂ e₂ e₂' →
               Cg2Fgᴱ c (Prod p₁ p₂) ⟨ e₁ , e₂ ⟩ ⟨ e₁' , e₂' ⟩

      Fst : ∀ {τ₁ τ₂ τ₁' τ₂' e e'} {p₁ : MkTy τ₁ τ₁'} {p₂ : MkTy τ₂ τ₂'} →
               Cg2Fgᴱ c (Prod p₁ p₂) e e' →
               Cg2Fgᴱ c p₁ (fst e) (fst e')

      Snd : ∀ {τ₁ τ₂ τ₁' τ₂' e e'} {p₁ : MkTy τ₁ τ₁'} {p₂ : MkTy τ₂ τ₂'} →
               Cg2Fgᴱ c (Prod p₁ p₂) e e' →
               Cg2Fgᴱ c p₂ (snd e) (snd e')

      Inl : ∀ {τ₁ τ₂ τ₁' τ₂' e e'} {p₁ : MkTy τ₁ τ₁'} {p₂ : MkTy τ₂ τ₂'} →
               Cg2Fgᴱ c p₁ e e' →
               Cg2Fgᴱ c (Sum p₁ p₂) (inl e) (inl e')

      Inr : ∀ {τ₁ τ₂ τ₁' τ₂' e e'} {p₁ : MkTy τ₁ τ₁'} {p₂ : MkTy τ₂ τ₂'} →
               Cg2Fgᴱ c p₂ e e' →
               Cg2Fgᴱ c (Sum p₁ p₂) (inr e) (inr e')

      Case : ∀ {τ₁ τ₂ τ₃ τ₁' τ₂' τ₃' e e₁ e₂ e' e₁' e₂'} {p₁ : MkTy τ₁ τ₁'} {p₂ : MkTy τ₂ τ₂'} {p₃ : MkTy τ₃ τ₃'} →
                 Cg2Fgᴱ c (Sum p₁ p₂) e e' →
                 Cg2Fgᴱ (p₁ ∷ c) p₃ e₁ e₁' →
                 Cg2Fgᴱ (p₂ ∷ c) p₃ e₂ e₂' →
                 Cg2Fgᴱ c p₃ (case e e₁ e₂) (case e' e₁' e₂')

      Wken : ∀ {τ τ' Γ₁ Γ₁' e e' c'} {p : MkTy τ τ'} {x : Γ₁ CG.⊆ Γ} {y : Γ₁' FG.⊆ Γ'} →
               Cg2Fgᴱ c' p e e' →
               Cg2Fg-⊆ c' c x y →
               Cg2Fgᴱ c p (wken e x) (wken e' y)

      ⌞_⌟ᵀ : ∀ {τ τ' e t} {p : MkTy τ τ'} →
               Cg2Fgᵀ c p t e →
               Cg2Fgᴱ c (LIO p) ⌞ t ⌟ᵀ (Λ (e FG.↑¹))


  data Cg2Fgᵀ {Γ Γ'} (c : MkCtx Γ Γ') : ∀ {τ τ'} →  MkTy τ τ' → Thunk Γ (LIO τ) → FG.Expr Γ' τ' → Set where
    instance
      Return : ∀ {τ τ' e e'} {p : MkTy τ τ'} →
                 Cg2Fgᴱ c p e e' →
                 Cg2Fgᵀ c p (return e) e'

      Bind : ∀ {τ₁ τ₂ τ₁' τ₂' e₁ e₂ e₁' e₂'} {p₁ : MkTy τ₁ τ₁'} {p₂ : MkTy τ₂ τ₂'} →
               Cg2Fgᴱ c (LIO p₁) e₁ e₁' →
               Cg2Fgᴱ (p₁ ∷ c) (LIO p₂) e₂ e₂' →
               Cg2Fgᵀ c p₂
                 (bind e₁ e₂)
                 ((Λ (taint (labelOf (var FG.here)) (e₂' FG.∘  Id （） )) ∘ (e₁' FG.∘ Id （）)))

      Unlabel : ∀ {τ τ' e e'} {p : MkTy τ τ'} →
                  Cg2Fgᴱ c (Labeled p) e e' →
                  Cg2Fgᵀ c p
                    (unlabel e)
                    ((Λ (taint (fst (var FG.here)) (snd (var FG.here)))) ∘ (unId e'))

      ToLabeled : ∀ {τ τ' e e'} {p : MkTy τ τ'} →
                     Cg2Fgᴱ c (LIO p) e e' →
                     Cg2Fgᵀ c (Labeled p)
                       (toLabeled e)
                       ((Λ (Id ⟨ (labelOf (var FG.here)) , var FG.here ⟩) ) ∘ (e' FG.∘ (Id （）)))

      LabelOf : ∀ {τ τ' e e'} {p : MkTy τ τ'} →
                  Cg2Fgᴱ c (Labeled p) e e' →
                  Cg2Fgᵀ c 𝓛 (labelOf e) (fst (unId e'))

      GetLabel : Cg2Fgᵀ c 𝓛 getLabel getLabel

      Taint : ∀ {e e'} → Cg2Fgᴱ c 𝓛 e e' → Cg2Fgᵀ c Unit (taint e) (taint e' （）)

      New : ∀ {τ τ' s e e'} {p : MkTy τ τ'} →
              Cg2Fgᴱ c (Labeled p) e e' →
              Cg2Fgᵀ c (Ref {s = s} p)
                (new e)
                (new (Λ (taint ( (fst (var FG.here))) (snd (var FG.here))) ∘  (unId e')))

      Read : ∀ {τ τ' s e e'} {p : MkTy τ τ'} →
               Cg2Fgᴱ c (Ref {s = s} p) e e' →
               Cg2Fgᵀ c p (! e) (! e')

      Writeᴵ : ∀ {τ τ' e₁ e₂ e₁' e₂'} {p : MkTy τ τ'} →
               Cg2Fgᴱ c (Ref {s = I} p) e₁ e₁' →
               Cg2Fgᴱ c (Labeled p) e₂ e₂' →
               Cg2Fgᵀ c Unit (e₁ ≔ e₂) (e₁' ≔ snd (unId e₂') )

      Writeˢ : ∀ {τ τ' e₁ e₂ e₁' e₂'} {p : MkTy τ τ'} →
               Cg2Fgᴱ c (Ref {s = S} p) e₁ e₁' →
               Cg2Fgᴱ c (Labeled p) e₂ e₂' →
               Cg2Fgᵀ c Unit (e₁ ≔ e₂)
                             (e₁' ≔ ((Λ (taint (fst (var here)) (snd (var here)))) ∘ unId e₂' ))

      LabelOfRef : ∀ {τ τ' s e e'} {p : MkTy τ τ'} →
                   Cg2Fgᴱ c (Ref {s = s} p) e e' →
                   Cg2Fgᵀ c 𝓛 (labelOfRef e) (labelOfRef e')

mutual

  instance
    mkCg2Fgᴱ : ∀ {Γ τ} (e : CG.Expr Γ τ) → Cg2Fgᴱ (mkCtx _) (mkTy _) e ⟦ e ⟧ᴱ
    mkCg2Fgᴱ (var τ∈Γ) = Var (mkCg2Fg-∈ τ∈Γ)
    mkCg2Fgᴱ (Λ e) = Fun (mkCg2Fgᴱ e)
    mkCg2Fgᴱ (e ∘ e₁) = App (mkCg2Fgᴱ e) (mkCg2Fgᴱ e₁)
    mkCg2Fgᴱ ⟨ e , e₁ ⟩ = Pair (mkCg2Fgᴱ e) (mkCg2Fgᴱ e₁)
    mkCg2Fgᴱ (fst e) = Fst (mkCg2Fgᴱ e)
    mkCg2Fgᴱ (snd e) = Snd (mkCg2Fgᴱ e)
    mkCg2Fgᴱ (inl e) = Inl (mkCg2Fgᴱ e)
    mkCg2Fgᴱ (inr e) = Inr (mkCg2Fgᴱ e)
    mkCg2Fgᴱ (case e e₁ e₂) = Case (mkCg2Fgᴱ e) (mkCg2Fgᴱ e₁) (mkCg2Fgᴱ e₂)
    mkCg2Fgᴱ ⌞ t ⌟ᵀ = ⌞ (mkCg2Fgᵀ t) ⌟ᵀ
    mkCg2Fgᴱ (wken e x) = Wken (mkCg2Fgᴱ e) (mkCg2Fg-⊆ x)
    mkCg2Fgᴱ （） = Unit
    mkCg2Fgᴱ ⌞ ℓ ⌟ = Lbl ℓ
    mkCg2Fgᴱ (e₁ ⊑-? e₂) = Test (mkCg2Fgᴱ e₁) (mkCg2Fgᴱ e₂)

    mkCg2Fgᵀ : ∀ {Γ τ} (t : CG.Thunk Γ (LIO τ)) → Cg2Fgᵀ (mkCtx _) (mkTy _) t ⟦ t ⟧ᵀ
    mkCg2Fgᵀ (return e) = Return (mkCg2Fgᴱ e )
    mkCg2Fgᵀ (bind e e₁) = Bind (mkCg2Fgᴱ e) (mkCg2Fgᴱ e₁)
    mkCg2Fgᵀ (unlabel e) = Unlabel (mkCg2Fgᴱ e)
    mkCg2Fgᵀ (toLabeled e) = ToLabeled (mkCg2Fgᴱ e)
    mkCg2Fgᵀ (labelOf e) = LabelOf (mkCg2Fgᴱ e)
    mkCg2Fgᵀ getLabel = GetLabel
    mkCg2Fgᵀ (taint e) = Taint (mkCg2Fgᴱ e)
    mkCg2Fgᵀ (new e) = New (mkCg2Fgᴱ e)
    mkCg2Fgᵀ (! e) = Read (mkCg2Fgᴱ e)
    mkCg2Fgᵀ (_≔_ {s = I} e e₁) = Writeᴵ (mkCg2Fgᴱ e) (mkCg2Fgᴱ e₁)
    mkCg2Fgᵀ (_≔_ {s = S} e e₁) = Writeˢ (mkCg2Fgᴱ e) (mkCg2Fgᴱ e₁)
    mkCg2Fgᵀ (labelOfRef e) = LabelOfRef (mkCg2Fgᴱ e)

mutual

  ≡-Cg2Fgᴱ : ∀ {Γ τ c p e'} {e : CG.Expr Γ τ} → Cg2Fgᴱ c p e e' → e' ≡ ⟦ e ⟧ᴱ
  ≡-Cg2Fgᴱ Unit = refl
  ≡-Cg2Fgᴱ (Lbl ℓ) = refl
  ≡-Cg2Fgᴱ (Test x₁ x₂)
    rewrite ≡-Cg2Fgᴱ x₁ | ≡-Cg2Fgᴱ x₂ = refl
  ≡-Cg2Fgᴱ (Var x) rewrite ≡-Cg2Fg-∈ x = refl
  ≡-Cg2Fgᴱ (Fun x) rewrite ≡-Cg2Fgᴱ x = refl
  ≡-Cg2Fgᴱ (App {p₁ = p₁} x x₁) with ≡-MkTy p₁
  ... | refl rewrite ≡-Cg2Fgᴱ x | ≡-Cg2Fgᴱ x₁ = refl
  ≡-Cg2Fgᴱ (Pair x x₁)
    rewrite ≡-Cg2Fgᴱ x | ≡-Cg2Fgᴱ x₁ = refl
  ≡-Cg2Fgᴱ (Fst {p₂ = p₂} x) with ≡-MkTy p₂
  ... | refl rewrite ≡-Cg2Fgᴱ x = refl
  ≡-Cg2Fgᴱ (Snd {p₁ = p₁} x) with ≡-MkTy p₁
  ... | refl rewrite ≡-Cg2Fgᴱ x = refl
  ≡-Cg2Fgᴱ (Inl {p₂ = p₂} x) with ≡-MkTy p₂
  ... | refl rewrite ≡-Cg2Fgᴱ x = refl
  ≡-Cg2Fgᴱ (Inr {p₁ = p₁} x) with ≡-MkTy p₁
  ... | refl rewrite ≡-Cg2Fgᴱ x = refl
  ≡-Cg2Fgᴱ (Case {p₁ = p₁} {p₂ = p₂} x x₁ x₂) with ≡-MkTy p₁ | ≡-MkTy p₂
  ... | refl | refl rewrite ≡-Cg2Fgᴱ x | ≡-Cg2Fgᴱ x₁ | ≡-Cg2Fgᴱ x₂ = refl
  ≡-Cg2Fgᴱ (Wken {c' = c'} x₁ x₂) with ≡-MkCtx c'
  ... | refl rewrite ≡-Cg2Fg-⊆ x₂ | ≡-Cg2Fgᴱ x₁ = refl
  ≡-Cg2Fgᴱ ⌞ x ⌟ᵀ rewrite ≡-Cg2Fgᵀ x = refl


  ≡-Cg2Fgᵀ : ∀ {Γ τ c p e} {t : CG.Thunk Γ (LIO τ)} → Cg2Fgᵀ c p t e → e ≡ ⟦ t ⟧ᵀ
  ≡-Cg2Fgᵀ (Return x) = ≡-Cg2Fgᴱ x
  ≡-Cg2Fgᵀ (Bind {p₁ = p₁} x x₁) with ≡-MkTy p₁
  ... | refl rewrite ≡-Cg2Fgᴱ x | ≡-Cg2Fgᴱ x₁ = refl
  ≡-Cg2Fgᵀ (Unlabel x) rewrite ≡-Cg2Fgᴱ x = refl
  ≡-Cg2Fgᵀ (ToLabeled x) rewrite ≡-Cg2Fgᴱ x = refl
  ≡-Cg2Fgᵀ (LabelOf {p = p} x) with ≡-MkTy p
  ... | refl rewrite ≡-Cg2Fgᴱ x = refl
  ≡-Cg2Fgᵀ GetLabel = refl
  ≡-Cg2Fgᵀ (Taint x) rewrite ≡-Cg2Fgᴱ x = refl
  ≡-Cg2Fgᵀ (New x) rewrite ≡-Cg2Fgᴱ x = refl
  ≡-Cg2Fgᵀ (Read x) rewrite ≡-Cg2Fgᴱ x = refl
  ≡-Cg2Fgᵀ (Writeᴵ {p = p} x x₁) with ≡-MkTy p
  ... | refl rewrite ≡-Cg2Fgᴱ x | ≡-Cg2Fgᴱ x₁ = refl
  ≡-Cg2Fgᵀ (Writeˢ {p = p} x x₁) with ≡-MkTy p
  ... | refl rewrite ≡-Cg2Fgᴱ x | ≡-Cg2Fgᴱ x₁ = refl
  ≡-Cg2Fgᵀ (LabelOfRef {p = p} x) with ≡-MkTy p
  ... | refl rewrite ≡-Cg2Fgᴱ x = refl

open import Function.Equivalence

-- The relation Cg2Fgᴱ is an equivalent representation for the
-- translation function over Thunks, i.e., ⟦ t ⟧ᵀ.
Cg2Fgᵀ-⟦·⟧ᵀ : ∀ {Γ τ} {t : CG.Thunk Γ (LIO τ)} {e : FG.Expr ⟦ Γ ⟧ᶜ ⟦ τ ⟧ᵗ}→
              e ≡ ⟦ t ⟧ᵀ  ⇔  Cg2Fgᵀ (mkCtx _) (mkTy _) t e
Cg2Fgᵀ-⟦·⟧ᵀ = equivalence (λ { refl → mkCg2Fgᵀ _ }) ≡-Cg2Fgᵀ

-- The relation Cg2Fgᴱ is an equivalent representation for the
-- translation function over Expr, i.e., ⟦ t ⟧ᵀ.
Cg2Fgᴱ-⟦·⟧ᴱ : ∀ {Γ τ} {e₁ : CG.Expr Γ τ} {e₂ : FG.Expr ⟦ Γ ⟧ᶜ ⟦ τ ⟧ᵗ}→
              e₂ ≡ ⟦ e₁ ⟧ᴱ  ⇔  Cg2Fgᴱ (mkCtx _) (mkTy _) e₁ e₂
Cg2Fgᴱ-⟦·⟧ᴱ = equivalence (λ { refl → mkCg2Fgᴱ _ }) ≡-Cg2Fgᴱ
