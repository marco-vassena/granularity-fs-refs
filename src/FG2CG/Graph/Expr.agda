open import Lattice

module FG2CG.Graph.Expr {{𝑳 : Lattice}} where

open import FG as FG
open import CG as CG
open import FG2CG.Syntax
open import Relation.Binary.PropositionalEquality
open import FG2CG.Graph.Types

-- Not that the following relations are indexed over the corresponding
-- relations over types and contexts because the functions that they
-- model transform the type and contexts indices of the input
-- expression as well.

mutual

  data Fg2Cgᴱ {Γ Γ' τ τ'} (c : MkCtx Γ Γ') (p : MkTy′ τ τ') : FG.Expr Γ τ → CG.Expr Γ' (LIO (Labeled τ')) → Set where
    ⌞_⌟ᵀ : ∀ {e : FG.Expr Γ τ} {t : CG.Thunk Γ' (LIO (Labeled τ'))} →
             Fg2Cgᵀ c p e t →
             Fg2Cgᴱ c p e ⌞ t ⌟ᵀ

  data Fg2Cgᵀ {Γ Γ'} (c : MkCtx Γ Γ') : ∀ {τ τ'} → MkTy′ τ τ' → FG.Expr Γ τ → CG.Thunk Γ' (LIO (Labeled τ')) → Set where

    Unit : Fg2Cgᵀ c Unit （） (toLabeled ⌞ return （） ⌟ᵀ)

    Var : ∀ {τ τ'} {τ∈Γ : τ FG.∈ Γ} {τ∈Γ' : (Labeled τ') CG.∈ Γ'} {p : MkTy′ τ τ'} →
            Fg2Cg-∈ (Labeled p) c τ∈Γ τ∈Γ' →
            Fg2Cgᵀ c p (var τ∈Γ) (toLabeled ⌞ unlabel (CG.var τ∈Γ') ⌟ᵀ)

    Fun : ∀ {τ₁ τ₂ τ₁' τ₂'} {e : FG.Expr (τ₁ FG.∷ Γ) τ₂} {e' : CG.Expr (τ₁' CG.∷ Γ') (LIO (Labeled τ₂'))}  →
             {p₁ : MkTy τ₁ τ₁'} {p₂ : MkTy′ τ₂ τ₂'} →
             Fg2Cgᴱ (p₁ ∷ c) p₂ e e' →
             Fg2Cgᵀ c (Fun p₁ (Labeled p₂)) (Λ e) (toLabeled ⌞ return (Λ e') ⌟ᵀ)

    App : ∀ {τ₁ τ₂ τ₁' τ₂'} {e₁ : FG.Expr Γ (τ₁ ➔ τ₂)} {e₂ : FG.Expr Γ τ₁}
            {e₁' : CG.Expr Γ' (LIO (Labeled ((Labeled τ₁') ➔ LIO (Labeled τ₂'))))} {e₂' : CG.Expr Γ' (LIO (Labeled τ₁'))} →
            {p₁ : MkTy′ τ₁ τ₁'} {p₂ : MkTy′ τ₂ τ₂'} →
            Fg2Cgᴱ c (Fun (Labeled p₁) (Labeled p₂)) e₁ e₁' →
            Fg2Cgᴱ c p₁ e₂ e₂' →
            Fg2Cgᵀ c p₂ (e₁ ∘ e₂)
              (bind e₁'
              ⌞ bind (e₂' CG.↑¹)
              ⌞ toLabeled
                ⌞ bind ⌞ unlabel (var (CG.there CG.here)) ⌟ᵀ
                ⌞ bind (var CG.here ∘ var (CG.there CG.here))
                ⌞ unlabel (var CG.here) ⌟ᵀ ⌟ᵀ ⌟ᵀ ⌟ᵀ ⌟ᵀ)

    Pair : ∀ {τ₁ τ₂ τ₁' τ₂'} {e₁ : FG.Expr Γ τ₁} {e₂ : FG.Expr Γ τ₂}
             {e₁' : CG.Expr Γ' (LIO (Labeled τ₁'))} {e₂' : CG.Expr Γ' (LIO (Labeled τ₂'))}
             {p₁ : MkTy′ τ₁ τ₁'} {p₂ : MkTy′ τ₂ τ₂'} →
             Fg2Cgᴱ c p₁ e₁ e₁' →
             Fg2Cgᴱ c p₂ e₂ e₂' →
             Fg2Cgᵀ c (Prod (Labeled p₁) (Labeled p₂)) ⟨ e₁ , e₂ ⟩
               (toLabeled
                 ⌞ bind e₁'
                 ⌞ bind (e₂' CG.↑¹)
                 ⌞ return ⟨ var (CG.there CG.here) , var CG.here ⟩ ⌟ᵀ ⌟ᵀ ⌟ᵀ)

    Fst :  ∀ {τ₁ τ₂ τ₁' τ₂'} {e : FG.Expr Γ (τ₁ × τ₂)}
             {e' : CG.Expr Γ' (LIO (Labeled ((Labeled τ₁') × (Labeled τ₂'))))}
             {p₁ : MkTy′ τ₁ τ₁'} {p₂ : MkTy′ τ₂ τ₂'} →
             Fg2Cgᴱ c (Prod (Labeled p₁) (Labeled p₂)) e e' →
             Fg2Cgᵀ c p₁ (fst e) (
               (toLabeled
                 ⌞ bind e'
                 ⌞ bind ⌞ unlabel (var CG.here) ⌟ᵀ
                 ⌞ unlabel (fst (var CG.here)) ⌟ᵀ ⌟ᵀ ⌟ᵀ))

    Snd :  ∀ {τ₁ τ₂ τ₁' τ₂'} {e : FG.Expr Γ (τ₁ × τ₂)}
             {e' : CG.Expr Γ' (LIO (Labeled ((Labeled τ₁') × (Labeled τ₂'))))}
             {p₁ : MkTy′ τ₁ τ₁'} {p₂ : MkTy′ τ₂ τ₂'} →
             Fg2Cgᴱ c (Prod (Labeled p₁) (Labeled p₂)) e e' →
             Fg2Cgᵀ c p₂ (snd e) (
               (toLabeled
                 ⌞ bind e'
                 ⌞ bind ⌞ unlabel (var CG.here) ⌟ᵀ
                 ⌞ unlabel (snd (var CG.here)) ⌟ᵀ ⌟ᵀ ⌟ᵀ))

    Inl :  ∀ {τ₁ τ₂ τ₁' τ₂'} {e : FG.Expr Γ τ₁}
             {e' : CG.Expr Γ' (LIO (Labeled τ₁'))}
             {p₁ : MkTy′ τ₁ τ₁'} {p₂ : MkTy′ τ₂ τ₂'} →
             Fg2Cgᴱ c p₁ e e' →
             Fg2Cgᵀ c (Sum (Labeled p₁) (Labeled p₂))
               (inl e)
               (toLabeled
                 ⌞ bind e' ⌞ return (inl (var CG.here)) ⌟ᵀ ⌟ᵀ)

    Inr :  ∀ {τ₁ τ₂ τ₁' τ₂'} {e : FG.Expr Γ τ₂}
             {e' : CG.Expr Γ' (LIO (Labeled τ₂'))}
             {p₁ : MkTy′ τ₁ τ₁'} {p₂ : MkTy′ τ₂ τ₂'} →
             Fg2Cgᴱ c p₂ e e' →
             Fg2Cgᵀ c (Sum (Labeled p₁) (Labeled p₂))
               (inr e)
               (toLabeled
                 ⌞ bind e' ⌞ return (inr (var CG.here)) ⌟ᵀ ⌟ᵀ)

    Case : ∀ {τ₁ τ₂ τ₃ τ₁' τ₂' τ₃' e₁ e₂ e₁' e₂'} {e : FG.Expr Γ (τ₁ FG.+ τ₂)}
             {e' : CG.Expr Γ' (LIO (Labeled ((Labeled τ₁') CG.+ (Labeled τ₂'))))}
             {p₁ : MkTy′ τ₁ τ₁'} {p₂ : MkTy′ τ₂ τ₂'} {p₃ : MkTy′ τ₃ τ₃'} →
             Fg2Cgᴱ c (Sum (Labeled p₁) (Labeled p₂)) e e' →
             Fg2Cgᴱ (Labeled p₁ ∷ c) p₃ e₁ e₁' →
             Fg2Cgᴱ (Labeled p₂ ∷ c) p₃ e₂ e₂' →
             Fg2Cgᵀ c p₃ (case e e₁ e₂) (
               toLabeled
                 ⌞ bind e'
                 ⌞ bind ⌞ unlabel (var CG.here) ⌟ᵀ
                 ⌞ bind (case (var CG.here) (
                        wken e₁' (CG.cons (CG.drop (CG.drop CG.refl-⊆))))
                        (wken e₂' (CG.cons (CG.drop (CG.drop CG.refl-⊆)))))
                 ⌞ unlabel (var CG.here) ⌟ᵀ ⌟ᵀ ⌟ᵀ ⌟ᵀ)

    Lbl : ∀ ℓ → Fg2Cgᵀ c 𝓛 ⌞ ℓ ⌟  (toLabeled ⌞ return ⌞ ℓ ⌟ ⌟ᵀ)

    Test : ∀ {e₁ e₂ : FG.Expr Γ 𝓛} {e₁' e₂' : CG.Expr Γ' _} →
             Fg2Cgᴱ c 𝓛 e₁ e₁' →
             Fg2Cgᴱ c 𝓛 e₂ e₂' →
             Fg2Cgᵀ c Bool′ (e₁ ⊑-? e₂)
               (toLabeled
                 ⌞ bind e₁'
                 ⌞ bind (wken e₂' (CG.drop CG.refl-⊆ ))
                 ⌞ bind ⌞ toLabeled ⌞ return （） ⌟ᵀ ⌟ᵀ
                 ⌞ bind ⌞ unlabel (var (there (there here))) ⌟ᵀ
                 ⌞ bind ⌞ unlabel (var (there (there here))) ⌟ᵀ
                 ⌞ return (CG.if (var (there here) ⊑-? var here)
                            then inl (var (there (there here)))
                            else inr (var (there (there here)))) ⌟ᵀ ⌟ᵀ ⌟ᵀ ⌟ᵀ ⌟ᵀ ⌟ᵀ)

    GetLabel : Fg2Cgᵀ c 𝓛 getLabel (toLabeled ⌞ getLabel ⌟ᵀ)

    LabelOf : ∀ {τ τ'} {e : FG.Expr Γ τ} {e' : CG.Expr Γ' (LIO (Labeled τ'))} {p : MkTy′ τ τ'} →
                Fg2Cgᴱ c p e e' →
                Fg2Cgᵀ c 𝓛 (labelOf e) (
                  toLabeled
                    ⌞ bind e'
                    ⌞ labelOf (var CG.here) ⌟ᵀ ⌟ᵀ)

    Wken : ∀ {τ τ' Γ₁ Γ₁'} {e : FG.Expr Γ₁ τ} {e' : CG.Expr Γ₁' (LIO (Labeled τ'))}
             {p : MkTy′ τ τ'} {c₁ : MkCtx Γ₁ Γ₁'} →
             {x : Γ₁ FG.⊆ Γ} {y : Γ₁' CG.⊆ Γ'} →
             Fg2Cgᴱ c₁ p e e' →
             Fg2Cg-⊆ c₁ c x y →
             Fg2Cgᵀ c p (wken e x) (bind ⌞ return (wken e' y) ⌟ᵀ (var CG.here))

    Taint : ∀ {τ τ'} {e₁ : FG.Expr Γ 𝓛} {e₁' : CG.Expr Γ' (LIO (Labeled 𝓛))}
              {e₂ : FG.Expr Γ τ} {e₂' : CG.Expr Γ' (LIO (Labeled τ'))} →
              {p : MkTy′ τ τ'} →
              Fg2Cgᴱ c 𝓛 e₁ e₁' →
              Fg2Cgᴱ c p e₂ e₂' →
              Fg2Cgᵀ c p (taint e₁ e₂) (
                toLabeled
                  ⌞ bind e₁'
                  ⌞ bind ⌞ unlabel (var CG.here) ⌟ᵀ
                  ⌞ bind ⌞ taint (var CG.here) ⌟ᵀ
                  ⌞ bind (wken e₂' (CG.drop (CG.drop (CG.drop CG.refl-⊆))))
                  ⌞ unlabel (var CG.here ) ⌟ᵀ ⌟ᵀ ⌟ᵀ ⌟ᵀ ⌟ᵀ)

    LabelOfRef : ∀ {τ τ' s} {e : FG.Expr Γ (Ref s τ)} {e' : CG.Expr Γ' (LIO (Labeled (Ref s τ')))}
                   {p : MkTy′ τ τ'} →
                   Fg2Cgᴱ c (Ref p) e e' →
                   Fg2Cgᵀ c 𝓛 (labelOfRef e) (
                     toLabeled
                       ⌞ bind e'
                       ⌞ bind ⌞ unlabel (var CG.here) ⌟ᵀ
                       ⌞ labelOfRef (var CG.here) ⌟ᵀ ⌟ᵀ ⌟ᵀ )

    New : ∀ {τ τ' s} {e : FG.Expr Γ τ} {e' : CG.Expr Γ' (LIO (Labeled τ'))}
            {p : MkTy′ τ τ'} →
            Fg2Cgᴱ c p e e' →
            Fg2Cgᵀ c (Ref {s = s} p) (new e) (
              toLabeled
                ⌞ bind e'
                ⌞ new (var CG.here) ⌟ᵀ ⌟ᵀ)

    Read : ∀ {τ τ' s} {e : FG.Expr Γ (Ref s τ)} {e' : CG.Expr Γ' (LIO (Labeled (Ref s τ')))}
             {p : MkTy′ τ τ'} →
             Fg2Cgᴱ c (Ref p) e e' →
             Fg2Cgᵀ c p (! e) (
               toLabeled
                 ⌞ bind e'
                 ⌞ bind ⌞ unlabel (var CG.here) ⌟ᵀ
                 ⌞ ! (var CG.here) ⌟ᵀ ⌟ᵀ ⌟ᵀ)

    Write : ∀ {τ τ' s} {e₁ : FG.Expr Γ (Ref s τ)} {e₁' : CG.Expr Γ' (LIO (Labeled (Ref s τ')))}
              {e₂ : FG.Expr Γ τ} {e₂' : CG.Expr Γ' (LIO (Labeled τ'))}
              {p : MkTy′ τ τ'} →
              Fg2Cgᴱ c (Ref p) e₁ e₁' →
              Fg2Cgᴱ c p e₂ e₂' →
              Fg2Cgᵀ c Unit (e₁ ≔ e₂) (
                bind ⌞ toLabeled
                     ⌞ bind e₁'
                     ⌞ bind (e₂' CG.↑¹)
                     ⌞ bind ⌞ unlabel (var (CG.there CG.here)) ⌟ᵀ
                     ⌞ var CG.here ≔ var (CG.there CG.here) ⌟ᵀ ⌟ᵀ ⌟ᵀ ⌟ᵀ ⌟ᵀ
                ⌞ toLabeled ⌞ return （） ⌟ᵀ ⌟ᵀ)

    Id : ∀ {τ τ'} {e : FG.Expr Γ τ} {e' : CG.Expr Γ' (LIO (Labeled τ'))} {p : MkTy′ τ τ'} →
           Fg2Cgᴱ c p e e' →
           Fg2Cgᵀ c (Id (Labeled p)) (Id e) (toLabeled e')

    UnId : ∀ {τ τ'} {e : FG.Expr Γ (Id τ)} {e' : CG.Expr Γ' (LIO (Labeled (Labeled τ')))} {p : MkTy′ τ τ'} →
             Fg2Cgᴱ c (Id (Labeled p)) e e' →
             Fg2Cgᵀ c p (unId e) (
               toLabeled ⌞
                 bind e'
               ⌞ bind ⌞ unlabel (var CG.here) ⌟ᵀ ⌞ unlabel (var CG.here) ⌟ᵀ ⌟ᵀ ⌟ᵀ )


mutual

  mkFg2Cgᴱ : ∀ {Γ τ} (e : FG.Expr Γ τ) → Fg2Cgᴱ (mkCtx _) (mkTy′ _) e ⟪ e ⟫ᴱ
  mkFg2Cgᴱ e = ⌞ mkFg2Cgᵀ e ⌟ᵀ

  -- Missing translation for ref-s.
  mkFg2Cgᵀ : ∀ {Γ τ} (e : FG.Expr Γ τ) → Fg2Cgᵀ (mkCtx _) (mkTy′ _) e ⟪ e ⟫ᵀ
  mkFg2Cgᵀ （） = Unit
  mkFg2Cgᵀ (var τ∈Γ) = Var (mkFg2Cg-∈ τ∈Γ)
  mkFg2Cgᵀ (Λ e) = Fun (mkFg2Cgᴱ e)
  mkFg2Cgᵀ (e ∘ e₁) = App (mkFg2Cgᴱ e) (mkFg2Cgᴱ e₁)
  mkFg2Cgᵀ (wken e x) = Wken (mkFg2Cgᴱ e) (mkFg2Cg-⊆ x)
  mkFg2Cgᵀ ⟨ e , e₁ ⟩ = Pair (mkFg2Cgᴱ e) (mkFg2Cgᴱ e₁)
  mkFg2Cgᵀ (fst e) = Fst (mkFg2Cgᴱ e)
  mkFg2Cgᵀ (snd e) = Snd (mkFg2Cgᴱ e)
  mkFg2Cgᵀ (inl e) = Inl (mkFg2Cgᴱ e)
  mkFg2Cgᵀ (inr e) = Inr (mkFg2Cgᴱ e)
  mkFg2Cgᵀ (case e e₁ e₂) = Case (mkFg2Cgᴱ e) (mkFg2Cgᴱ e₁) (mkFg2Cgᴱ e₂)
  mkFg2Cgᵀ ⌞ ℓ ⌟ = Lbl ℓ
  mkFg2Cgᵀ (e₁ ⊑-? e₂) = Test (mkFg2Cgᴱ e₁) (mkFg2Cgᴱ e₂)
  mkFg2Cgᵀ getLabel = GetLabel
  mkFg2Cgᵀ (labelOf e) = LabelOf (mkFg2Cgᴱ e)
  mkFg2Cgᵀ (taint e e₁) = Taint (mkFg2Cgᴱ e) (mkFg2Cgᴱ e₁)
  mkFg2Cgᵀ (labelOfRef {s = I} e) = LabelOfRef (mkFg2Cgᴱ e)
  mkFg2Cgᵀ (new e) = New (mkFg2Cgᴱ e)
  mkFg2Cgᵀ (! e) = Read (mkFg2Cgᴱ e)
  mkFg2Cgᵀ (e ≔ e₁) = Write (mkFg2Cgᴱ e) (mkFg2Cgᴱ e₁)
  mkFg2Cgᵀ (labelOfRef e) = LabelOfRef (mkFg2Cgᴱ e)
  mkFg2Cgᵀ (Id e) = Id (mkFg2Cgᴱ e)
  mkFg2Cgᵀ (unId e) = UnId (mkFg2Cgᴱ e)

  ≡-Fg2Cgᴱ : ∀ {Γ τ e₂ c p} {e₁ : FG.Expr Γ τ} → Fg2Cgᴱ c p e₁ e₂ → e₂ ≡ ⟪ e₁ ⟫ᴱ
  ≡-Fg2Cgᴱ ⌞ x ⌟ᵀ rewrite ≡-Fg2Cgᵀ x = refl

  ≡-Fg2Cgᵀ : ∀ {Γ τ t c p} {e : FG.Expr Γ τ} → Fg2Cgᵀ c p e t → t ≡ ⟪ e ⟫ᵀ
  ≡-Fg2Cgᵀ Unit = refl
  ≡-Fg2Cgᵀ (Var x) rewrite ≡-Fg2Cg-∈ x = refl
  ≡-Fg2Cgᵀ (Fun x) rewrite ≡-Fg2Cgᴱ x = refl
  ≡-Fg2Cgᵀ (App {p₁ = p₁} x x₁) with ≡-MkTy′ p₁
  ... | refl rewrite ≡-Fg2Cgᴱ x | ≡-Fg2Cgᴱ x₁ = refl
  ≡-Fg2Cgᵀ (Pair x x₁)
    rewrite ≡-Fg2Cgᴱ x | ≡-Fg2Cgᴱ x₁ = refl
  ≡-Fg2Cgᵀ (Fst {p₂ = p₂} x) with ≡-MkTy′ p₂
  ... | refl rewrite ≡-Fg2Cgᴱ x = refl
  ≡-Fg2Cgᵀ (Snd {p₁ = p₁} x) with ≡-MkTy′ p₁
  ... | refl rewrite ≡-Fg2Cgᴱ x = refl
  ≡-Fg2Cgᵀ (Inl x) rewrite ≡-Fg2Cgᴱ x = refl
  ≡-Fg2Cgᵀ (Inr x) rewrite ≡-Fg2Cgᴱ x = refl
  ≡-Fg2Cgᵀ (Case {p₁ = p₁} {p₂ = p₂} x x₁ x₂) with ≡-MkTy′ p₁ | ≡-MkTy′ p₂
  ... | refl | refl rewrite ≡-Fg2Cgᴱ x | ≡-Fg2Cgᴱ x₁ | ≡-Fg2Cgᴱ x₂ = refl
  ≡-Fg2Cgᵀ (Lbl ℓ) = refl
  ≡-Fg2Cgᵀ (Test x₁ x₂) rewrite ≡-Fg2Cgᴱ x₁ | ≡-Fg2Cgᴱ x₂ = refl
  ≡-Fg2Cgᵀ GetLabel = refl
  ≡-Fg2Cgᵀ (LabelOf {p = p} x) with ≡-MkTy′ p
  ... | refl rewrite ≡-Fg2Cgᴱ x = refl
  ≡-Fg2Cgᵀ (Wken {c₁ = c₁} x₁ x₂) with ≡-MkCtx c₁
  ... | refl rewrite ≡-Fg2Cg-⊆ x₂ | ≡-Fg2Cgᴱ x₁ = refl
  ≡-Fg2Cgᵀ (Taint x x₁)
    rewrite ≡-Fg2Cgᴱ x | ≡-Fg2Cgᴱ x₁ = refl
  ≡-Fg2Cgᵀ (LabelOfRef {p = p} x) with ≡-MkTy′ p
  ... | refl rewrite ≡-Fg2Cgᴱ x = refl
  ≡-Fg2Cgᵀ (New x) rewrite ≡-Fg2Cgᴱ x = refl
  ≡-Fg2Cgᵀ (Read x) rewrite ≡-Fg2Cgᴱ x = refl
  ≡-Fg2Cgᵀ (Write {p = p} x x₁) with ≡-MkTy′ p
  ... | refl rewrite ≡-Fg2Cgᴱ x | ≡-Fg2Cgᴱ x₁ = refl
  ≡-Fg2Cgᵀ (Id x) rewrite ≡-Fg2Cgᴱ x = refl
  ≡-Fg2Cgᵀ (UnId x) rewrite ≡-Fg2Cgᴱ x = refl

open import Function.Equivalence

-- The relation Fg2Cgᵀ is an equivalent representation for the
-- translation function over Thunks ⟪ τ ⟫ᵀ.
Fg2Cgᵀ-⟪·⟫ᵀ : ∀ {Γ τ} {e : FG.Expr Γ τ} {t : CG.Thunk ⟪ Γ ⟫ᶜ (LIO ⟪ τ ⟫ᵗ)} →
              t ≡ ⟪ e ⟫ᵀ  ⇔  Fg2Cgᵀ (mkCtx _) (mkTy′ _) e t
Fg2Cgᵀ-⟪·⟫ᵀ = equivalence (λ { refl → mkFg2Cgᵀ _ }) ≡-Fg2Cgᵀ

-- The relation Fg2Cgᴱ is an equivalent representation for the
-- translation function over Thunks ⟪ τ ⟫ᴱ.
Fg2Cgᴱ-⟪·⟫ᴱ : ∀ {Γ τ} {e₁ : FG.Expr Γ τ} {e₂ : CG.Expr ⟪ Γ ⟫ᶜ (LIO ⟪ τ ⟫ᵗ)} →
              e₂ ≡ ⟪ e₁ ⟫ᴱ  ⇔  Fg2Cgᴱ (mkCtx _) (mkTy′ _) e₁ e₂
Fg2Cgᴱ-⟪·⟫ᴱ = equivalence (λ { refl → mkFg2Cgᴱ _ }) ≡-Fg2Cgᴱ
