-- CG L-equivalence of target (translated) terms implies
-- L-equivalence of the original source FG terms.

open import Lattice

module FG2CG.Recovery.Unlift {{ð³ : Lattice}} (A : Label) where

open import FG as FG
open import CG as CG
open import FG.LowEq A as F
open import CG.LowEq A as C
open import FG2CG.Syntax
open import FG2CG.Graph as G
open import FG2CG.Recovery.Injective
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Unit

-- Why is this private?
private

  -- This module performs unlifting using the graph of the translation function.
  module Aux where

    mutual

      unlift-âá´± : â {Î Î' câ câ Î²} {Î¸â Î¸â : FG.Env Î} {Î¸â' Î¸â' : CG.Env Î'} â
                    Î¸â' C.ââ¨ Î² â©á´± Î¸â' â
                    Fg2Cgáµ câ Î¸â Î¸â' â
                    Fg2Cgáµ câ Î¸â Î¸â' â
                    Î¸â F.ââ¨ Î² â©á´± Î¸â
      unlift-âá´± C.[] G.[] G.[] = []
      unlift-âá´± (vââvâ C.â· Î¸ââÎ¸â) (xâ G.â· xâ) (yâ G.â· yâ) = unlift-ââ±½ vââvâ xâ yâ â· unlift-âá´± Î¸ââÎ¸â xâ yâ

      unlift-âá´¿ : â {Ï Ï' pâ pâ Î²} {râ râ : FG.Raw Ï} {râ' râ' : CG.Value Ï'} â
                    râ' C.ââ¨ Î² â©â±½ râ' â
                    Fg2Cgá´¿ pâ râ râ' â
                    Fg2Cgá´¿ pâ râ râ' â
                    râ F.ââ¨ Î² â©á´¿ râ
      unlift-âá´¿ C.Unit G.Unit G.Unit = Unit
      unlift-âá´¿ (C.Lbl .ââ) (G.Lbl .ââ) (G.Lbl ââ) = Lbl ââ
      unlift-âá´¿ (C.Inl a) (G.Inl b) (G.Inl c) = Inl (unlift-ââ±½ a b c)
      unlift-âá´¿ (C.Inr a) (G.Inr b) (G.Inr c) = Inr (unlift-ââ±½ a b c)
      unlift-âá´¿ (C.Pair lââlâ râârâ) (G.Pair lâ râ) (G.Pair lâ râ) = Pair (unlift-ââ±½ lââlâ lâ lâ ) (unlift-ââ±½ râârâ râ râ)
      unlift-âá´¿ (C.Fun Î¸ââÎ¸ââ²) (G.Fun {c = a} xâ xâ) (G.Fun {c = b} yâ yâ) with â¡-MkCtx a | â¡-MkCtx b
      ... | eqâ | eqâ  rewrite eqâ | inj-âª eqâ â«á¶ | inj-âªÂ·â«á´± xâ yâ = Fun (unlift-âá´± Î¸ââÎ¸ââ² xâ yâ)
      unlift-âá´¿ (C.Ref-Iá´¸ ââA n) G.Refá´µ G.Refá´µ = Ref-Iá´¸ ââA
      unlift-âá´¿ (C.Ref-Iá´´ âââ¤A âââ¤A) G.Refá´µ G.Refá´µ = Ref-Iá´´ âââ¤A âââ¤A
      unlift-âá´¿ (C.Ref-S x) G.RefË¢ G.RefË¢ = Ref-S x
      unlift-âá´¿ a (Id b) (Id c) = Id (unlift-ââ±½ a b c)

      unlift-ââ±½ : â {Ï Ï' pâ pâ Î²} {vâ vâ : FG.Value Ï} {vâ' vâ' : CG.Value (Labeled Ï')} â
                    vâ' C.ââ¨ Î² â©â±½ vâ' â
                    Fg2Cgâ±½ pâ vâ vâ' â
                    Fg2Cgâ±½ pâ vâ vâ' â
                    vâ F.ââ¨ Î² â©â±½ vâ
      unlift-ââ±½ (C.Labeledá´¸ ââA a) (G.Labeled .â b) (G.Labeled â c) = Valueá´¸ ââA (unlift-âá´¿ a b c)
      unlift-ââ±½ (C.Labeledá´´ ââ¤A a) (G.Labeled â b) (G.Labeled ââ c) = Valueá´´ ââ¤A a

    import Generic.Memory.LowEq {FG.Ty} {FG.Raw} F._ââ¨_â©á´¿_ A as FM
    import Generic.Memory.LowEq {CG.Ty} {CG.Value} C._ââ¨_â©â±½_ A as CM
    open import FG2CG.Graph.Memory as FGM

    unlift-âá´¹ : â {â Î²} {Mâ Mâ : FG.Memory â} {Mâ' Mâ' : CG.Memory â} â
                   Mâ' C.ââ¨ Î² â©á´¹ Mâ' â
                   Fg2Cgá´¹ Mâ Mâ' â
                   Fg2Cgá´¹ Mâ Mâ' â
                   Mâ F.ââ¨ Î² â©á´¹ Mâ
    unlift-âá´¹ CM.[] G.nil G.nil  = FM.[]
    unlift-âá´¹ (vââvâ CM.â· MââMâ) (G.cons p xâ xâ) (G.cons q yâ yâ) with â¡-MkTyâ² p | â¡-MkTyâ² q | inj-MkTyâ² p q
    ... | eqâ | eqâ | eqâ rewrite eqâ | eqâ | eqâ
      = (unlift-âá´¿ vââvâ xâ yâ) FM.â· (unlift-âá´¹  MââMâ xâ yâ)

-- Public memories.
unlift-âá´¹ : â {â Î²} {Mâ Mâ : FG.Memory â} â âª Mâ â«á´¹ C.ââ¨ Î² â©á´¹ âª Mâ â«á´¹ â Mâ F.ââ¨ Î² â©á´¹ Mâ
unlift-âá´¹ âªMââMââ« = Aux.unlift-âá´¹ âªMââMââ« (mkFg2Cgá´¹ _) (mkFg2Cgá´¹ _)

-- Memories.
unlift-ââ¨_â©á´¹ : â {â Î²} {Mâ Mâ : FG.Memory â} (x : Dec (â â A)) â âª Mâ â«á´¹ C.ââ¨ Î² , x â©á´¹ âª Mâ â«á´¹ â Mâ F.ââ¨ Î² , x â©á´¹ Mâ
unlift-ââ¨ yes p â©á´¹ âªMââMââ« = unlift-âá´¹ âªMââMââ«
unlift-ââ¨ no Â¬p â©á´¹ _ = tt

-- Stores.
unlift-âË¢ : â {Î£â Î£â Î²} â âª Î£â â«Ë¢ C.ââ¨ Î² â©Ë¢ âª Î£â â«Ë¢ â Î£â F.ââ¨ Î² â©Ë¢ Î£â
unlift-âË¢ âªÎ£ââÎ£ââ« â = unlift-ââ¨ â â? A â©á´¹ (âªÎ£ââÎ£ââ« â)

-- Raw values.
unlift-âá´¿ : â {Ï Î²} {râ râ : FG.Raw Ï} â
              âª râ â«á´¿ C.ââ¨ Î² â©â±½ âª râ â«á´¿ â
              râ F.ââ¨ Î² â©á´¿ râ
unlift-âá´¿ âªrâârââ« = Aux.unlift-âá´¿ âªrâârââ« (mkFg2Cgá´¿ _) (mkFg2Cgá´¿ _)

-- Values.
unlift-ââ±½ : â {Ï Î²} {vâ vâ : FG.Value Ï} â
              âª vâ â«â±½ C.ââ¨ Î² â©â±½ âª vâ â«â±½ â
              vâ F.ââ¨ Î² â©â±½ vâ
unlift-ââ±½ âªvââvââ« = Aux.unlift-ââ±½ âªvââvââ« (mkFg2Cgâ±½ _) (mkFg2Cgâ±½ _)

-- Environments.
unlift-âá´± :  â {Î Î²} {Î¸â Î¸â : FG.Env Î} â
               âª Î¸â â«áµ C.ââ¨ Î² â©á´± âª Î¸â â«áµ â
               Î¸â F.ââ¨ Î² â©á´± Î¸â
unlift-âá´± âªÎ¸ââÎ¸ââ« = Aux.unlift-âá´± âªÎ¸ââÎ¸ââ« (mkFg2Cgáµ _) (mkFg2Cgáµ _)

unlift-âá´´ : â {Î¼â Î¼â Î²} â âª Î¼â â«á´´ C.ââ¨ Î² â©á´´ âª Î¼â â«á´´ â Î¼â F.ââ¨ Î² â©á´´ Î¼â
unlift-âá´´ {Î¼â} {Î¼â} {Î²} âá´´ = record { dom-â = unlift-dom-â ; rng-â = unlift-rng-â ; lift-â = unlift-lift-â }
  where open C._ââ¨_â©á´´_ âá´´
        open import Generic.Heap.Lemmas CG.Ty CG.LValue as HC
        open import Generic.Heap.Lemmas FG.Ty FG.Value as HF
        open import FG2CG.Graph.Types
        open import FG2CG.Graph.Value
        open import Generic.Heap.Graph Graph-âªÂ·â«áµâ² Graph-âªÂ·â«á´¸
        open import Generic.Value.HLowEq {CG.Ty} {CG.LValue} C._ââ¨_â©á´¸_ as CH
        open import Generic.Value.HLowEq {FG.Ty} {FG.Value} F._ââ¨_â©â±½_ as FH

        unlift-dom-â : Î² F.âá´° Î¼â
        unlift-dom-â âá´® with HC.â-< (dom-â âá´®)
        ... | â¤â rewrite â¥ Î¼â â¥-â¡á´´ = HF.<-â â¤â

        unlift-rng-â : Î² F.âá´¿ Î¼â
        unlift-rng-â âá´® with HC.â-< (rng-â âá´®)
        ... | â¤â rewrite â¥ Î¼â â¥-â¡á´´ = HF.<-â â¤â

        unlift-lift-â : F.Lift-â Î¼â Î¼â Î²
        unlift-lift-â {vâ = vâ} {vâ = vâ} âá´® ââ ââ with lift-â âá´® âª ââ â«âá´´ âª ââ â«âá´´
        ... | âv with CH.ââ±½-type-â¡ âv
        ... | eq with inj-âª eq â«áµâ²
        unlift-lift-â {vâ = vâ} {vâ} âá´® ââ ââ | CH.â âv â | refl | refl = FH.â unlift-ââ±½ âv â

unlift-âá´¾ : â {pâ pâ Î²} â âª pâ â«á´¾ C.ââ¨ Î² â©á´¾ âª pâ â«á´¾ â pâ F.ââ¨ Î² â©á´¾ pâ
unlift-âá´¾ C.â¨ Î£â , Î¼â â© = F.â¨ unlift-âË¢ Î£â , unlift-âá´´ Î¼â â©

-- Initial configurations (not needed).
unlift-âá´µ : â {Ï Î Î²} {câ câ : IConf Î Ï} â (pc : Label) â âª câ â«á´µ pc C.ââ¨ Î² â©á´µ âª câ â«á´µ pc â câ F.ââ¨ Î² â©á´µ câ
unlift-âá´µ pc â¨ âá´¾ , refl , term-â¡ â© = â¨ unlift-âá´¾ âá´¾ , inj-âª term-â¡ â«á´± â©

-- Final configurations.
unlift-âá¶ : â {pc Ï Î²} {câ câ : FG.FConf Ï} â
            let â¨ _ , _ , _ ^ ââ â© = câ
                â¨ _ , _ , _ ^ ââ â© = câ in
                pc â ââ â
                pc â ââ â
                âª câ â«á¶   pc C.ââ¨ Î² â©á¶ âª câ â«á¶  pc â
                câ F.ââ¨ Î² â©á¶ câ
unlift-âá¶ pcâââ pcâââ (pcá´¸ âá´¾ pcâA vâ) = â¨ unlift-âá´¾ âá´¾ , unlift-ââ±½ vâ â©
unlift-âá¶ pcâââ pcâââ (pcá´´ âá´¾ pcâ¤A _) = â¨ unlift-âá´¾ âá´¾ , Valueá´´ (trans-â¤ pcâââ pcâ¤A) (trans-â¤ pcâââ pcâ¤A)  â©
