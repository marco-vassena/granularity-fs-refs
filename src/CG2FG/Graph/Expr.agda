open import Lattice

module CG2FG.Graph.Expr {{ð³ : Lattice}} where

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

  data Cg2Fgá´± {Î Î'} (c : MkCtx Î Î') : â {Ï Ï'} â MkTy Ï Ï' â CG.Expr Î Ï â FG.Expr Î' Ï' â Set where

    instance
      Unit : Cg2Fgá´± c Unit ï¼ï¼ ï¼ï¼

      Lbl : â â â Cg2Fgá´± c ð â â â â â â

      Test : â {eâ eâ : CG.Expr Î ð} {eâ' eâ'} â
               Cg2Fgá´± c ð eâ eâ' â
               Cg2Fgá´± c ð eâ eâ' â
               Cg2Fgá´± c Boolâ² (eâ â-? eâ) (eâ' â-? eâ')

      Var : â {Ï Ï' p} {ÏâÎ : Ï CG.â Î} {ÏâÎ' : Ï' FG.â Î'} â
              Cg2Fg-â p c ÏâÎ ÏâÎ' â
              Cg2Fgá´±  c p (var ÏâÎ) (var ÏâÎ')

      Fun : â {Ïâ Ïâ Ïâ' Ïâ' pâ pâ} {e : CG.Expr (Ïâ CG.â· Î) Ïâ} {e' : FG.Expr (Ïâ' FG.â· Î') Ïâ'} â
              Cg2Fgá´± (pâ â· c) pâ e e' â
              Cg2Fgá´± c (Fun pâ pâ) (Î e) (Î e')

      App : â {Ïâ Ïâ Ïâ' Ïâ' pâ pâ} {eâ : CG.Expr Î (Ïâ â Ïâ)} {eâ' : FG.Expr Î' (Ïâ' â Ïâ')} â
              {eâ : CG.Expr Î Ïâ} {eâ' : FG.Expr Î' Ïâ'} â
              Cg2Fgá´± c (Fun pâ pâ) eâ eâ' â
              Cg2Fgá´± c pâ eâ eâ' â
              Cg2Fgá´± c pâ (eâ â eâ) (eâ' â eâ')

      Pair : â {Ïâ Ïâ Ïâ' Ïâ' eâ eâ' eâ eâ'} {pâ : MkTy Ïâ Ïâ'} {pâ : MkTy Ïâ Ïâ'} â
               Cg2Fgá´± c pâ eâ eâ' â
               Cg2Fgá´± c pâ eâ eâ' â
               Cg2Fgá´± c (Prod pâ pâ) â¨ eâ , eâ â© â¨ eâ' , eâ' â©

      Fst : â {Ïâ Ïâ Ïâ' Ïâ' e e'} {pâ : MkTy Ïâ Ïâ'} {pâ : MkTy Ïâ Ïâ'} â
               Cg2Fgá´± c (Prod pâ pâ) e e' â
               Cg2Fgá´± c pâ (fst e) (fst e')

      Snd : â {Ïâ Ïâ Ïâ' Ïâ' e e'} {pâ : MkTy Ïâ Ïâ'} {pâ : MkTy Ïâ Ïâ'} â
               Cg2Fgá´± c (Prod pâ pâ) e e' â
               Cg2Fgá´± c pâ (snd e) (snd e')

      Inl : â {Ïâ Ïâ Ïâ' Ïâ' e e'} {pâ : MkTy Ïâ Ïâ'} {pâ : MkTy Ïâ Ïâ'} â
               Cg2Fgá´± c pâ e e' â
               Cg2Fgá´± c (Sum pâ pâ) (inl e) (inl e')

      Inr : â {Ïâ Ïâ Ïâ' Ïâ' e e'} {pâ : MkTy Ïâ Ïâ'} {pâ : MkTy Ïâ Ïâ'} â
               Cg2Fgá´± c pâ e e' â
               Cg2Fgá´± c (Sum pâ pâ) (inr e) (inr e')

      Case : â {Ïâ Ïâ Ïâ Ïâ' Ïâ' Ïâ' e eâ eâ e' eâ' eâ'} {pâ : MkTy Ïâ Ïâ'} {pâ : MkTy Ïâ Ïâ'} {pâ : MkTy Ïâ Ïâ'} â
                 Cg2Fgá´± c (Sum pâ pâ) e e' â
                 Cg2Fgá´± (pâ â· c) pâ eâ eâ' â
                 Cg2Fgá´± (pâ â· c) pâ eâ eâ' â
                 Cg2Fgá´± c pâ (case e eâ eâ) (case e' eâ' eâ')

      Wken : â {Ï Ï' Îâ Îâ' e e' c'} {p : MkTy Ï Ï'} {x : Îâ CG.â Î} {y : Îâ' FG.â Î'} â
               Cg2Fgá´± c' p e e' â
               Cg2Fg-â c' c x y â
               Cg2Fgá´± c p (wken e x) (wken e' y)

      â_âáµ : â {Ï Ï' e t} {p : MkTy Ï Ï'} â
               Cg2Fgáµ c p t e â
               Cg2Fgá´± c (LIO p) â t âáµ (Î (e FG.âÂ¹))


  data Cg2Fgáµ {Î Î'} (c : MkCtx Î Î') : â {Ï Ï'} â  MkTy Ï Ï' â Thunk Î (LIO Ï) â FG.Expr Î' Ï' â Set where
    instance
      Return : â {Ï Ï' e e'} {p : MkTy Ï Ï'} â
                 Cg2Fgá´± c p e e' â
                 Cg2Fgáµ c p (return e) e'

      Bind : â {Ïâ Ïâ Ïâ' Ïâ' eâ eâ eâ' eâ'} {pâ : MkTy Ïâ Ïâ'} {pâ : MkTy Ïâ Ïâ'} â
               Cg2Fgá´± c (LIO pâ) eâ eâ' â
               Cg2Fgá´± (pâ â· c) (LIO pâ) eâ eâ' â
               Cg2Fgáµ c pâ
                 (bind eâ eâ)
                 ((Î (taint (labelOf (var FG.here)) (eâ' FG.â  Id ï¼ï¼ )) â (eâ' FG.â Id ï¼ï¼)))

      Unlabel : â {Ï Ï' e e'} {p : MkTy Ï Ï'} â
                  Cg2Fgá´± c (Labeled p) e e' â
                  Cg2Fgáµ c p
                    (unlabel e)
                    ((Î (taint (fst (var FG.here)) (snd (var FG.here)))) â (unId e'))

      ToLabeled : â {Ï Ï' e e'} {p : MkTy Ï Ï'} â
                     Cg2Fgá´± c (LIO p) e e' â
                     Cg2Fgáµ c (Labeled p)
                       (toLabeled e)
                       ((Î (Id â¨ (labelOf (var FG.here)) , var FG.here â©) ) â (e' FG.â (Id ï¼ï¼)))

      LabelOf : â {Ï Ï' e e'} {p : MkTy Ï Ï'} â
                  Cg2Fgá´± c (Labeled p) e e' â
                  Cg2Fgáµ c ð (labelOf e) (fst (unId e'))

      GetLabel : Cg2Fgáµ c ð getLabel getLabel

      Taint : â {e e'} â Cg2Fgá´± c ð e e' â Cg2Fgáµ c Unit (taint e) (taint e' ï¼ï¼)

      New : â {Ï Ï' s e e'} {p : MkTy Ï Ï'} â
              Cg2Fgá´± c (Labeled p) e e' â
              Cg2Fgáµ c (Ref {s = s} p)
                (new e)
                (new (Î (taint ( (fst (var FG.here))) (snd (var FG.here))) â  (unId e')))

      Read : â {Ï Ï' s e e'} {p : MkTy Ï Ï'} â
               Cg2Fgá´± c (Ref {s = s} p) e e' â
               Cg2Fgáµ c p (! e) (! e')

      Write : â {Ï Ï' s eâ eâ eâ' eâ'} {p : MkTy Ï Ï'} â
               Cg2Fgá´± c (Ref {s = s} p) eâ eâ' â
               Cg2Fgá´± c (Labeled p) eâ eâ' â
               Cg2Fgáµ c Unit (eâ â eâ)
                             (eâ' â ((Î (taint (fst (var here)) (snd (var here)))) â unId eâ' ))


      LabelOfRef : â {Ï Ï' s e e'} {p : MkTy Ï Ï'} â
                   Cg2Fgá´± c (Ref {s = s} p) e e' â
                   Cg2Fgáµ c ð (labelOfRef e) (labelOfRef e')

mutual

  instance
    mkCg2Fgá´± : â {Î Ï} (e : CG.Expr Î Ï) â Cg2Fgá´± (mkCtx _) (mkTy _) e â¦ e â§á´±
    mkCg2Fgá´± (var ÏâÎ) = Var (mkCg2Fg-â ÏâÎ)
    mkCg2Fgá´± (Î e) = Fun (mkCg2Fgá´± e)
    mkCg2Fgá´± (e â eâ) = App (mkCg2Fgá´± e) (mkCg2Fgá´± eâ)
    mkCg2Fgá´± â¨ e , eâ â© = Pair (mkCg2Fgá´± e) (mkCg2Fgá´± eâ)
    mkCg2Fgá´± (fst e) = Fst (mkCg2Fgá´± e)
    mkCg2Fgá´± (snd e) = Snd (mkCg2Fgá´± e)
    mkCg2Fgá´± (inl e) = Inl (mkCg2Fgá´± e)
    mkCg2Fgá´± (inr e) = Inr (mkCg2Fgá´± e)
    mkCg2Fgá´± (case e eâ eâ) = Case (mkCg2Fgá´± e) (mkCg2Fgá´± eâ) (mkCg2Fgá´± eâ)
    mkCg2Fgá´± â t âáµ = â (mkCg2Fgáµ t) âáµ
    mkCg2Fgá´± (wken e x) = Wken (mkCg2Fgá´± e) (mkCg2Fg-â x)
    mkCg2Fgá´± ï¼ï¼ = Unit
    mkCg2Fgá´± â â â = Lbl â
    mkCg2Fgá´± (eâ â-? eâ) = Test (mkCg2Fgá´± eâ) (mkCg2Fgá´± eâ)

    mkCg2Fgáµ : â {Î Ï} (t : CG.Thunk Î (LIO Ï)) â Cg2Fgáµ (mkCtx _) (mkTy _) t â¦ t â§áµ
    mkCg2Fgáµ (return e) = Return (mkCg2Fgá´± e )
    mkCg2Fgáµ (bind e eâ) = Bind (mkCg2Fgá´± e) (mkCg2Fgá´± eâ)
    mkCg2Fgáµ (unlabel e) = Unlabel (mkCg2Fgá´± e)
    mkCg2Fgáµ (toLabeled e) = ToLabeled (mkCg2Fgá´± e)
    mkCg2Fgáµ (labelOf e) = LabelOf (mkCg2Fgá´± e)
    mkCg2Fgáµ getLabel = GetLabel
    mkCg2Fgáµ (taint e) = Taint (mkCg2Fgá´± e)
    mkCg2Fgáµ (new e) = New (mkCg2Fgá´± e)
    mkCg2Fgáµ (! e) = Read (mkCg2Fgá´± e)
    mkCg2Fgáµ (e â eâ) = Write (mkCg2Fgá´± e) (mkCg2Fgá´± eâ)
    mkCg2Fgáµ (labelOfRef e) = LabelOfRef (mkCg2Fgá´± e)

mutual

  â¡-Cg2Fgá´± : â {Î Ï c p e'} {e : CG.Expr Î Ï} â Cg2Fgá´± c p e e' â e' â¡ â¦ e â§á´±
  â¡-Cg2Fgá´± Unit = refl
  â¡-Cg2Fgá´± (Lbl â) = refl
  â¡-Cg2Fgá´± (Test xâ xâ)
    rewrite â¡-Cg2Fgá´± xâ | â¡-Cg2Fgá´± xâ = refl
  â¡-Cg2Fgá´± (Var x) rewrite â¡-Cg2Fg-â x = refl
  â¡-Cg2Fgá´± (Fun x) rewrite â¡-Cg2Fgá´± x = refl
  â¡-Cg2Fgá´± (App {pâ = pâ} x xâ) with â¡-MkTy pâ
  ... | refl rewrite â¡-Cg2Fgá´± x | â¡-Cg2Fgá´± xâ = refl
  â¡-Cg2Fgá´± (Pair x xâ)
    rewrite â¡-Cg2Fgá´± x | â¡-Cg2Fgá´± xâ = refl
  â¡-Cg2Fgá´± (Fst {pâ = pâ} x) with â¡-MkTy pâ
  ... | refl rewrite â¡-Cg2Fgá´± x = refl
  â¡-Cg2Fgá´± (Snd {pâ = pâ} x) with â¡-MkTy pâ
  ... | refl rewrite â¡-Cg2Fgá´± x = refl
  â¡-Cg2Fgá´± (Inl {pâ = pâ} x) with â¡-MkTy pâ
  ... | refl rewrite â¡-Cg2Fgá´± x = refl
  â¡-Cg2Fgá´± (Inr {pâ = pâ} x) with â¡-MkTy pâ
  ... | refl rewrite â¡-Cg2Fgá´± x = refl
  â¡-Cg2Fgá´± (Case {pâ = pâ} {pâ = pâ} x xâ xâ) with â¡-MkTy pâ | â¡-MkTy pâ
  ... | refl | refl rewrite â¡-Cg2Fgá´± x | â¡-Cg2Fgá´± xâ | â¡-Cg2Fgá´± xâ = refl
  â¡-Cg2Fgá´± (Wken {c' = c'} xâ xâ) with â¡-MkCtx c'
  ... | refl rewrite â¡-Cg2Fg-â xâ | â¡-Cg2Fgá´± xâ = refl
  â¡-Cg2Fgá´± â x âáµ rewrite â¡-Cg2Fgáµ x = refl


  â¡-Cg2Fgáµ : â {Î Ï c p e} {t : CG.Thunk Î (LIO Ï)} â Cg2Fgáµ c p t e â e â¡ â¦ t â§áµ
  â¡-Cg2Fgáµ (Return x) = â¡-Cg2Fgá´± x
  â¡-Cg2Fgáµ (Bind {pâ = pâ} x xâ) with â¡-MkTy pâ
  ... | refl rewrite â¡-Cg2Fgá´± x | â¡-Cg2Fgá´± xâ = refl
  â¡-Cg2Fgáµ (Unlabel x) rewrite â¡-Cg2Fgá´± x = refl
  â¡-Cg2Fgáµ (ToLabeled x) rewrite â¡-Cg2Fgá´± x = refl
  â¡-Cg2Fgáµ (LabelOf {p = p} x) with â¡-MkTy p
  ... | refl rewrite â¡-Cg2Fgá´± x = refl
  â¡-Cg2Fgáµ GetLabel = refl
  â¡-Cg2Fgáµ (Taint x) rewrite â¡-Cg2Fgá´± x = refl
  â¡-Cg2Fgáµ (New x) rewrite â¡-Cg2Fgá´± x = refl
  â¡-Cg2Fgáµ (Read x) rewrite â¡-Cg2Fgá´± x = refl
  -- â¡-Cg2Fgáµ (Writeá´µ {p = p} x xâ) with â¡-MkTy p
  -- ... | refl rewrite â¡-Cg2Fgá´± x | â¡-Cg2Fgá´± xâ = refl
  â¡-Cg2Fgáµ (Write {p = p} x xâ) with â¡-MkTy p
  ... | refl rewrite â¡-Cg2Fgá´± x | â¡-Cg2Fgá´± xâ = refl
  â¡-Cg2Fgáµ (LabelOfRef {p = p} x) with â¡-MkTy p
  ... | refl rewrite â¡-Cg2Fgá´± x = refl

open import Function.Equivalence

-- The relation Cg2Fgá´± is an equivalent representation for the
-- translation function over Thunks, i.e., â¦ t â§áµ.
Cg2Fgáµ-â¦Â·â§áµ : â {Î Ï} {t : CG.Thunk Î (LIO Ï)} {e : FG.Expr â¦ Î â§á¶ â¦ Ï â§áµ}â
              e â¡ â¦ t â§áµ  â  Cg2Fgáµ (mkCtx _) (mkTy _) t e
Cg2Fgáµ-â¦Â·â§áµ = equivalence (Î» { refl â mkCg2Fgáµ _ }) â¡-Cg2Fgáµ

-- The relation Cg2Fgá´± is an equivalent representation for the
-- translation function over Expr, i.e., â¦ t â§áµ.
Cg2Fgá´±-â¦Â·â§á´± : â {Î Ï} {eâ : CG.Expr Î Ï} {eâ : FG.Expr â¦ Î â§á¶ â¦ Ï â§áµ}â
              eâ â¡ â¦ eâ â§á´±  â  Cg2Fgá´± (mkCtx _) (mkTy _) eâ eâ
Cg2Fgá´±-â¦Â·â§á´± = equivalence (Î» { refl â mkCg2Fgá´± _ }) â¡-Cg2Fgá´±
