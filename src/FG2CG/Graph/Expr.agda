open import Lattice

module FG2CG.Graph.Expr {{ð³ : Lattice}} where

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

  data Fg2Cgá´± {Î Î' Ï Ï'} (c : MkCtx Î Î') (p : MkTyâ² Ï Ï') : FG.Expr Î Ï â CG.Expr Î' (LIO (Labeled Ï')) â Set where
    â_âáµ : â {e : FG.Expr Î Ï} {t : CG.Thunk Î' (LIO (Labeled Ï'))} â
             Fg2Cgáµ c p e t â
             Fg2Cgá´± c p e â t âáµ

  data Fg2Cgáµ {Î Î'} (c : MkCtx Î Î') : â {Ï Ï'} â MkTyâ² Ï Ï' â FG.Expr Î Ï â CG.Thunk Î' (LIO (Labeled Ï')) â Set where

    Unit : Fg2Cgáµ c Unit ï¼ï¼ (toLabeled â return ï¼ï¼ âáµ)

    Var : â {Ï Ï'} {ÏâÎ : Ï FG.â Î} {ÏâÎ' : (Labeled Ï') CG.â Î'} {p : MkTyâ² Ï Ï'} â
            Fg2Cg-â (Labeled p) c ÏâÎ ÏâÎ' â
            Fg2Cgáµ c p (var ÏâÎ) (toLabeled â unlabel (CG.var ÏâÎ') âáµ)

    Fun : â {Ïâ Ïâ Ïâ' Ïâ'} {e : FG.Expr (Ïâ FG.â· Î) Ïâ} {e' : CG.Expr (Ïâ' CG.â· Î') (LIO (Labeled Ïâ'))}  â
             {pâ : MkTy Ïâ Ïâ'} {pâ : MkTyâ² Ïâ Ïâ'} â
             Fg2Cgá´± (pâ â· c) pâ e e' â
             Fg2Cgáµ c (Fun pâ (Labeled pâ)) (Î e) (toLabeled â return (Î e') âáµ)

    App : â {Ïâ Ïâ Ïâ' Ïâ'} {eâ : FG.Expr Î (Ïâ â Ïâ)} {eâ : FG.Expr Î Ïâ}
            {eâ' : CG.Expr Î' (LIO (Labeled ((Labeled Ïâ') â LIO (Labeled Ïâ'))))} {eâ' : CG.Expr Î' (LIO (Labeled Ïâ'))} â
            {pâ : MkTyâ² Ïâ Ïâ'} {pâ : MkTyâ² Ïâ Ïâ'} â
            Fg2Cgá´± c (Fun (Labeled pâ) (Labeled pâ)) eâ eâ' â
            Fg2Cgá´± c pâ eâ eâ' â
            Fg2Cgáµ c pâ (eâ â eâ)
              (bind eâ'
              â bind (eâ' CG.âÂ¹)
              â toLabeled
                â bind â unlabel (var (CG.there CG.here)) âáµ
                â bind (var CG.here â var (CG.there CG.here))
                â unlabel (var CG.here) âáµ âáµ âáµ âáµ âáµ)

    Pair : â {Ïâ Ïâ Ïâ' Ïâ'} {eâ : FG.Expr Î Ïâ} {eâ : FG.Expr Î Ïâ}
             {eâ' : CG.Expr Î' (LIO (Labeled Ïâ'))} {eâ' : CG.Expr Î' (LIO (Labeled Ïâ'))}
             {pâ : MkTyâ² Ïâ Ïâ'} {pâ : MkTyâ² Ïâ Ïâ'} â
             Fg2Cgá´± c pâ eâ eâ' â
             Fg2Cgá´± c pâ eâ eâ' â
             Fg2Cgáµ c (Prod (Labeled pâ) (Labeled pâ)) â¨ eâ , eâ â©
               (toLabeled
                 â bind eâ'
                 â bind (eâ' CG.âÂ¹)
                 â return â¨ var (CG.there CG.here) , var CG.here â© âáµ âáµ âáµ)

    Fst :  â {Ïâ Ïâ Ïâ' Ïâ'} {e : FG.Expr Î (Ïâ Ã Ïâ)}
             {e' : CG.Expr Î' (LIO (Labeled ((Labeled Ïâ') Ã (Labeled Ïâ'))))}
             {pâ : MkTyâ² Ïâ Ïâ'} {pâ : MkTyâ² Ïâ Ïâ'} â
             Fg2Cgá´± c (Prod (Labeled pâ) (Labeled pâ)) e e' â
             Fg2Cgáµ c pâ (fst e) (
               (toLabeled
                 â bind e'
                 â bind â unlabel (var CG.here) âáµ
                 â unlabel (fst (var CG.here)) âáµ âáµ âáµ))

    Snd :  â {Ïâ Ïâ Ïâ' Ïâ'} {e : FG.Expr Î (Ïâ Ã Ïâ)}
             {e' : CG.Expr Î' (LIO (Labeled ((Labeled Ïâ') Ã (Labeled Ïâ'))))}
             {pâ : MkTyâ² Ïâ Ïâ'} {pâ : MkTyâ² Ïâ Ïâ'} â
             Fg2Cgá´± c (Prod (Labeled pâ) (Labeled pâ)) e e' â
             Fg2Cgáµ c pâ (snd e) (
               (toLabeled
                 â bind e'
                 â bind â unlabel (var CG.here) âáµ
                 â unlabel (snd (var CG.here)) âáµ âáµ âáµ))

    Inl :  â {Ïâ Ïâ Ïâ' Ïâ'} {e : FG.Expr Î Ïâ}
             {e' : CG.Expr Î' (LIO (Labeled Ïâ'))}
             {pâ : MkTyâ² Ïâ Ïâ'} {pâ : MkTyâ² Ïâ Ïâ'} â
             Fg2Cgá´± c pâ e e' â
             Fg2Cgáµ c (Sum (Labeled pâ) (Labeled pâ))
               (inl e)
               (toLabeled
                 â bind e' â return (inl (var CG.here)) âáµ âáµ)

    Inr :  â {Ïâ Ïâ Ïâ' Ïâ'} {e : FG.Expr Î Ïâ}
             {e' : CG.Expr Î' (LIO (Labeled Ïâ'))}
             {pâ : MkTyâ² Ïâ Ïâ'} {pâ : MkTyâ² Ïâ Ïâ'} â
             Fg2Cgá´± c pâ e e' â
             Fg2Cgáµ c (Sum (Labeled pâ) (Labeled pâ))
               (inr e)
               (toLabeled
                 â bind e' â return (inr (var CG.here)) âáµ âáµ)

    Case : â {Ïâ Ïâ Ïâ Ïâ' Ïâ' Ïâ' eâ eâ eâ' eâ'} {e : FG.Expr Î (Ïâ FG.+ Ïâ)}
             {e' : CG.Expr Î' (LIO (Labeled ((Labeled Ïâ') CG.+ (Labeled Ïâ'))))}
             {pâ : MkTyâ² Ïâ Ïâ'} {pâ : MkTyâ² Ïâ Ïâ'} {pâ : MkTyâ² Ïâ Ïâ'} â
             Fg2Cgá´± c (Sum (Labeled pâ) (Labeled pâ)) e e' â
             Fg2Cgá´± (Labeled pâ â· c) pâ eâ eâ' â
             Fg2Cgá´± (Labeled pâ â· c) pâ eâ eâ' â
             Fg2Cgáµ c pâ (case e eâ eâ) (
               toLabeled
                 â bind e'
                 â bind â unlabel (var CG.here) âáµ
                 â bind (case (var CG.here) (
                        wken eâ' (CG.cons (CG.drop (CG.drop CG.refl-â))))
                        (wken eâ' (CG.cons (CG.drop (CG.drop CG.refl-â)))))
                 â unlabel (var CG.here) âáµ âáµ âáµ âáµ)

    Lbl : â â â Fg2Cgáµ c ð â â â  (toLabeled â return â â â âáµ)

    Test : â {eâ eâ : FG.Expr Î ð} {eâ' eâ' : CG.Expr Î' _} â
             Fg2Cgá´± c ð eâ eâ' â
             Fg2Cgá´± c ð eâ eâ' â
             Fg2Cgáµ c Boolâ² (eâ â-? eâ)
               (toLabeled
                 â bind eâ'
                 â bind (wken eâ' (CG.drop CG.refl-â ))
                 â bind â toLabeled â return ï¼ï¼ âáµ âáµ
                 â bind â unlabel (var (there (there here))) âáµ
                 â bind â unlabel (var (there (there here))) âáµ
                 â return (CG.if (var (there here) â-? var here)
                            then inl (var (there (there here)))
                            else inr (var (there (there here)))) âáµ âáµ âáµ âáµ âáµ âáµ)

    GetLabel : Fg2Cgáµ c ð getLabel (toLabeled â getLabel âáµ)

    LabelOf : â {Ï Ï'} {e : FG.Expr Î Ï} {e' : CG.Expr Î' (LIO (Labeled Ï'))} {p : MkTyâ² Ï Ï'} â
                Fg2Cgá´± c p e e' â
                Fg2Cgáµ c ð (labelOf e) (
                  toLabeled
                    â bind e'
                    â labelOf (var CG.here) âáµ âáµ)

    Wken : â {Ï Ï' Îâ Îâ'} {e : FG.Expr Îâ Ï} {e' : CG.Expr Îâ' (LIO (Labeled Ï'))}
             {p : MkTyâ² Ï Ï'} {câ : MkCtx Îâ Îâ'} â
             {x : Îâ FG.â Î} {y : Îâ' CG.â Î'} â
             Fg2Cgá´± câ p e e' â
             Fg2Cg-â câ c x y â
             Fg2Cgáµ c p (wken e x) (bind â return (wken e' y) âáµ (var CG.here))

    Taint : â {Ï Ï'} {eâ : FG.Expr Î ð} {eâ' : CG.Expr Î' (LIO (Labeled ð))}
              {eâ : FG.Expr Î Ï} {eâ' : CG.Expr Î' (LIO (Labeled Ï'))} â
              {p : MkTyâ² Ï Ï'} â
              Fg2Cgá´± c ð eâ eâ' â
              Fg2Cgá´± c p eâ eâ' â
              Fg2Cgáµ c p (taint eâ eâ) (
                toLabeled
                  â bind eâ'
                  â bind â unlabel (var CG.here) âáµ
                  â bind â taint (var CG.here) âáµ
                  â bind (wken eâ' (CG.drop (CG.drop (CG.drop CG.refl-â))))
                  â unlabel (var CG.here ) âáµ âáµ âáµ âáµ âáµ)

    LabelOfRef : â {Ï Ï' s} {e : FG.Expr Î (Ref s Ï)} {e' : CG.Expr Î' (LIO (Labeled (Ref s Ï')))}
                   {p : MkTyâ² Ï Ï'} â
                   Fg2Cgá´± c (Ref p) e e' â
                   Fg2Cgáµ c ð (labelOfRef e) (
                     toLabeled
                       â bind e'
                       â bind â unlabel (var CG.here) âáµ
                       â labelOfRef (var CG.here) âáµ âáµ âáµ )

    New : â {Ï Ï' s} {e : FG.Expr Î Ï} {e' : CG.Expr Î' (LIO (Labeled Ï'))}
            {p : MkTyâ² Ï Ï'} â
            Fg2Cgá´± c p e e' â
            Fg2Cgáµ c (Ref {s = s} p) (new e) (
              toLabeled
                â bind e'
                â new (var CG.here) âáµ âáµ)

    Read : â {Ï Ï' s} {e : FG.Expr Î (Ref s Ï)} {e' : CG.Expr Î' (LIO (Labeled (Ref s Ï')))}
             {p : MkTyâ² Ï Ï'} â
             Fg2Cgá´± c (Ref p) e e' â
             Fg2Cgáµ c p (! e) (
               toLabeled
                 â bind e'
                 â bind â unlabel (var CG.here) âáµ
                 â ! (var CG.here) âáµ âáµ âáµ)

    Write : â {Ï Ï' s} {eâ : FG.Expr Î (Ref s Ï)} {eâ' : CG.Expr Î' (LIO (Labeled (Ref s Ï')))}
              {eâ : FG.Expr Î Ï} {eâ' : CG.Expr Î' (LIO (Labeled Ï'))}
              {p : MkTyâ² Ï Ï'} â
              Fg2Cgá´± c (Ref p) eâ eâ' â
              Fg2Cgá´± c p eâ eâ' â
              Fg2Cgáµ c Unit (eâ â eâ) (
                bind â toLabeled
                     â bind eâ'
                     â bind (eâ' CG.âÂ¹)
                     â bind â unlabel (var (CG.there CG.here)) âáµ
                     â var CG.here â var (CG.there CG.here) âáµ âáµ âáµ âáµ âáµ
                â toLabeled â return ï¼ï¼ âáµ âáµ)

    Id : â {Ï Ï'} {e : FG.Expr Î Ï} {e' : CG.Expr Î' (LIO (Labeled Ï'))} {p : MkTyâ² Ï Ï'} â
           Fg2Cgá´± c p e e' â
           Fg2Cgáµ c (Id (Labeled p)) (Id e) (toLabeled e')

    UnId : â {Ï Ï'} {e : FG.Expr Î (Id Ï)} {e' : CG.Expr Î' (LIO (Labeled (Labeled Ï')))} {p : MkTyâ² Ï Ï'} â
             Fg2Cgá´± c (Id (Labeled p)) e e' â
             Fg2Cgáµ c p (unId e) (
               toLabeled â
                 bind e'
               â bind â unlabel (var CG.here) âáµ â unlabel (var CG.here) âáµ âáµ âáµ )


mutual

  mkFg2Cgá´± : â {Î Ï} (e : FG.Expr Î Ï) â Fg2Cgá´± (mkCtx _) (mkTyâ² _) e âª e â«á´±
  mkFg2Cgá´± e = â mkFg2Cgáµ e âáµ

  -- Missing translation for ref-s.
  mkFg2Cgáµ : â {Î Ï} (e : FG.Expr Î Ï) â Fg2Cgáµ (mkCtx _) (mkTyâ² _) e âª e â«áµ
  mkFg2Cgáµ ï¼ï¼ = Unit
  mkFg2Cgáµ (var ÏâÎ) = Var (mkFg2Cg-â ÏâÎ)
  mkFg2Cgáµ (Î e) = Fun (mkFg2Cgá´± e)
  mkFg2Cgáµ (e â eâ) = App (mkFg2Cgá´± e) (mkFg2Cgá´± eâ)
  mkFg2Cgáµ (wken e x) = Wken (mkFg2Cgá´± e) (mkFg2Cg-â x)
  mkFg2Cgáµ â¨ e , eâ â© = Pair (mkFg2Cgá´± e) (mkFg2Cgá´± eâ)
  mkFg2Cgáµ (fst e) = Fst (mkFg2Cgá´± e)
  mkFg2Cgáµ (snd e) = Snd (mkFg2Cgá´± e)
  mkFg2Cgáµ (inl e) = Inl (mkFg2Cgá´± e)
  mkFg2Cgáµ (inr e) = Inr (mkFg2Cgá´± e)
  mkFg2Cgáµ (case e eâ eâ) = Case (mkFg2Cgá´± e) (mkFg2Cgá´± eâ) (mkFg2Cgá´± eâ)
  mkFg2Cgáµ â â â = Lbl â
  mkFg2Cgáµ (eâ â-? eâ) = Test (mkFg2Cgá´± eâ) (mkFg2Cgá´± eâ)
  mkFg2Cgáµ getLabel = GetLabel
  mkFg2Cgáµ (labelOf e) = LabelOf (mkFg2Cgá´± e)
  mkFg2Cgáµ (taint e eâ) = Taint (mkFg2Cgá´± e) (mkFg2Cgá´± eâ)
  mkFg2Cgáµ (labelOfRef {s = I} e) = LabelOfRef (mkFg2Cgá´± e)
  mkFg2Cgáµ (new e) = New (mkFg2Cgá´± e)
  mkFg2Cgáµ (! e) = Read (mkFg2Cgá´± e)
  mkFg2Cgáµ (e â eâ) = Write (mkFg2Cgá´± e) (mkFg2Cgá´± eâ)
  mkFg2Cgáµ (labelOfRef e) = LabelOfRef (mkFg2Cgá´± e)
  mkFg2Cgáµ (Id e) = Id (mkFg2Cgá´± e)
  mkFg2Cgáµ (unId e) = UnId (mkFg2Cgá´± e)

  â¡-Fg2Cgá´± : â {Î Ï eâ c p} {eâ : FG.Expr Î Ï} â Fg2Cgá´± c p eâ eâ â eâ â¡ âª eâ â«á´±
  â¡-Fg2Cgá´± â x âáµ rewrite â¡-Fg2Cgáµ x = refl

  â¡-Fg2Cgáµ : â {Î Ï t c p} {e : FG.Expr Î Ï} â Fg2Cgáµ c p e t â t â¡ âª e â«áµ
  â¡-Fg2Cgáµ Unit = refl
  â¡-Fg2Cgáµ (Var x) rewrite â¡-Fg2Cg-â x = refl
  â¡-Fg2Cgáµ (Fun x) rewrite â¡-Fg2Cgá´± x = refl
  â¡-Fg2Cgáµ (App {pâ = pâ} x xâ) with â¡-MkTyâ² pâ
  ... | refl rewrite â¡-Fg2Cgá´± x | â¡-Fg2Cgá´± xâ = refl
  â¡-Fg2Cgáµ (Pair x xâ)
    rewrite â¡-Fg2Cgá´± x | â¡-Fg2Cgá´± xâ = refl
  â¡-Fg2Cgáµ (Fst {pâ = pâ} x) with â¡-MkTyâ² pâ
  ... | refl rewrite â¡-Fg2Cgá´± x = refl
  â¡-Fg2Cgáµ (Snd {pâ = pâ} x) with â¡-MkTyâ² pâ
  ... | refl rewrite â¡-Fg2Cgá´± x = refl
  â¡-Fg2Cgáµ (Inl x) rewrite â¡-Fg2Cgá´± x = refl
  â¡-Fg2Cgáµ (Inr x) rewrite â¡-Fg2Cgá´± x = refl
  â¡-Fg2Cgáµ (Case {pâ = pâ} {pâ = pâ} x xâ xâ) with â¡-MkTyâ² pâ | â¡-MkTyâ² pâ
  ... | refl | refl rewrite â¡-Fg2Cgá´± x | â¡-Fg2Cgá´± xâ | â¡-Fg2Cgá´± xâ = refl
  â¡-Fg2Cgáµ (Lbl â) = refl
  â¡-Fg2Cgáµ (Test xâ xâ) rewrite â¡-Fg2Cgá´± xâ | â¡-Fg2Cgá´± xâ = refl
  â¡-Fg2Cgáµ GetLabel = refl
  â¡-Fg2Cgáµ (LabelOf {p = p} x) with â¡-MkTyâ² p
  ... | refl rewrite â¡-Fg2Cgá´± x = refl
  â¡-Fg2Cgáµ (Wken {câ = câ} xâ xâ) with â¡-MkCtx câ
  ... | refl rewrite â¡-Fg2Cg-â xâ | â¡-Fg2Cgá´± xâ = refl
  â¡-Fg2Cgáµ (Taint x xâ)
    rewrite â¡-Fg2Cgá´± x | â¡-Fg2Cgá´± xâ = refl
  â¡-Fg2Cgáµ (LabelOfRef {p = p} x) with â¡-MkTyâ² p
  ... | refl rewrite â¡-Fg2Cgá´± x = refl
  â¡-Fg2Cgáµ (New x) rewrite â¡-Fg2Cgá´± x = refl
  â¡-Fg2Cgáµ (Read x) rewrite â¡-Fg2Cgá´± x = refl
  â¡-Fg2Cgáµ (Write {p = p} x xâ) with â¡-MkTyâ² p
  ... | refl rewrite â¡-Fg2Cgá´± x | â¡-Fg2Cgá´± xâ = refl
  â¡-Fg2Cgáµ (Id x) rewrite â¡-Fg2Cgá´± x = refl
  â¡-Fg2Cgáµ (UnId x) rewrite â¡-Fg2Cgá´± x = refl

open import Function.Equivalence

-- The relation Fg2Cgáµ is an equivalent representation for the
-- translation function over Thunks âª Ï â«áµ.
Fg2Cgáµ-âªÂ·â«áµ : â {Î Ï} {e : FG.Expr Î Ï} {t : CG.Thunk âª Î â«á¶ (LIO âª Ï â«áµ)} â
              t â¡ âª e â«áµ  â  Fg2Cgáµ (mkCtx _) (mkTyâ² _) e t
Fg2Cgáµ-âªÂ·â«áµ = equivalence (Î» { refl â mkFg2Cgáµ _ }) â¡-Fg2Cgáµ

-- The relation Fg2Cgá´± is an equivalent representation for the
-- translation function over Thunks âª Ï â«á´±.
Fg2Cgá´±-âªÂ·â«á´± : â {Î Ï} {eâ : FG.Expr Î Ï} {eâ : CG.Expr âª Î â«á¶ (LIO âª Ï â«áµ)} â
              eâ â¡ âª eâ â«á´±  â  Fg2Cgá´± (mkCtx _) (mkTyâ² _) eâ eâ
Fg2Cgá´±-âªÂ·â«á´± = equivalence (Î» { refl â mkFg2Cgá´± _ }) â¡-Fg2Cgá´±
