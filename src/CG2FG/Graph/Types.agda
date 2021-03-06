module CG2FG.Graph.Types where

open import FG.Types as FG
open import CG.Types as CG
open import CG2FG.Syntax
open import Relation.Binary.PropositionalEquality

data MkTy : CG.Ty โ FG.Ty โ Set where
  instance
    Unit : MkTy unit unit
    ๐ : MkTy ๐ ๐
    Prod : โ {ฯโ ฯโ ฯโ' ฯโ'} โ MkTy ฯโ ฯโ' โ MkTy ฯโ ฯโ' โ MkTy (ฯโ CG.ร ฯโ) (ฯโ' FG.ร ฯโ')
    Sum : โ {ฯโ ฯโ ฯโ' ฯโ'} โ MkTy ฯโ ฯโ' โ MkTy ฯโ ฯโ' โ MkTy (ฯโ CG.+ ฯโ) (ฯโ' FG.+ ฯโ')
    Labeled : โ {ฯ ฯ'} โ MkTy ฯ ฯ' โ MkTy (Labeled ฯ) (Id (๐ ร ฯ'))
    Ref : โ {ฯ ฯ' s} โ MkTy ฯ ฯ' โ MkTy (CG.Ref s ฯ) (FG.Ref s ฯ')
    LIO : โ {ฯ ฯ'} โ MkTy ฯ ฯ' โ MkTy (CG.LIO ฯ) ((Id unit) FG.โ ฯ')
    Fun : โ {ฯโ ฯโ ฯโ' ฯโ'} โ MkTy ฯโ ฯโ' โ MkTy ฯโ ฯโ' โ MkTy (ฯโ CG.โ ฯโ) (ฯโ' FG.โ ฯโ')

Boolโฒ : MkTy CG.Bool FG.Bool
Boolโฒ = Sum Unit Unit

instance
  mkTy : โ ฯ โ MkTy ฯ โฆ ฯ โงแต
  mkTy unit = Unit
  mkTy (ฯ ร ฯโ) = Prod (mkTy ฯ) (mkTy ฯโ)
  mkTy (ฯ + ฯโ) = Sum (mkTy ฯ) (mkTy ฯโ)
  mkTy (ฯ โ ฯโ) = MkTy.Fun (mkTy ฯ) (mkTy ฯโ)
  mkTy ๐ = ๐
  mkTy (LIO ฯ) = LIO (mkTy ฯ)
  mkTy (Labeled ฯ) = Labeled (mkTy ฯ)
  mkTy (Ref s ฯ) = Ref (mkTy ฯ)

โก-MkTy : โ {ฯ ฯ'} โ MkTy ฯ ฯ' โ ฯ' โก โฆ ฯ โงแต
โก-MkTy Unit = refl
โก-MkTy ๐ = refl
โก-MkTy (Prod x xโ) rewrite โก-MkTy x | โก-MkTy xโ = refl
โก-MkTy (Sum x xโ) rewrite โก-MkTy x | โก-MkTy xโ = refl
โก-MkTy (Labeled x) rewrite โก-MkTy x = refl
โก-MkTy (Ref x) rewrite โก-MkTy x = refl
โก-MkTy (LIO x) rewrite โก-MkTy x = refl
โก-MkTy (Fun x xโ) rewrite โก-MkTy x | โก-MkTy xโ = refl

open import Function.Equivalence

-- The relation MkTy is an equivalent representation for the
-- translation function over types.
MkTy-โฆยทโงแต : โ {ฯ ฯ'} โ ฯ' โก โฆ ฯ โงแต  โ  MkTy ฯ ฯ'
MkTy-โฆยทโงแต = equivalence (ฮป { refl โ mkTy _ }) โก-MkTy

instance
  -- Unique proofs
  !-MkTy : โ {ฯ ฯ'} (p q : MkTy ฯ ฯ') โ p โก q
  !-MkTy Unit Unit = refl
  !-MkTy ๐ ๐ = refl
  !-MkTy (Prod pโ pโ) (Prod qโ qโ)
    rewrite !-MkTy pโ qโ | !-MkTy pโ qโ = refl
  !-MkTy (Sum pโ pโ) (Sum qโ qโ)
    rewrite !-MkTy pโ qโ | !-MkTy pโ qโ = refl
  !-MkTy (Labeled p) (Labeled q) rewrite !-MkTy p q = refl
  !-MkTy (Ref p) (Ref q) rewrite !-MkTy p q = refl
  !-MkTy (LIO p) (LIO q) rewrite !-MkTy p q = refl
  !-MkTy (Fun pโ pโ) (Fun qโ qโ)
    rewrite !-MkTy pโ qโ | !-MkTy pโ qโ = refl

--------------------------------------------------------------------------------
-- TODO: is this ever used?
-- Yes, it is used in the translation of expressions
-- Graph instances

open import Generic.Graph

-- TODO: if we make ctx an instance of our generic container we can reuse the exisiting proofs

Graph-โฆยทโงแต : Graph โฆ_โงแต
Graph-โฆยทโงแต = record { P = MkTy ; โ_โ = mkTy ; โ_โ = โก-MkTy }

-- Is this eveer used?
-- Derive graph of context generically.
open import Generic.Context.Graph {CG.Ty} {FG.Ty} {โฆ_โงแต} Graph-โฆยทโงแต
  renaming ( S2Tแถ to MkCtx
           ; mkS2Tแถ to mkCtx
           ; โก-S2Tแถ to โก-MkCtx
           ; S2T-โ to Cg2Fg-โ
           ; mkS2T-โ to mkCg2Fg-โ
           ; โก-S2T-โ to โก-Cg2Fg-โ
           ; S2T-โ to Cg2Fg-โ
           ; mkS2T-โ to mkCg2Fg-โ
           ; โก-S2T-โ to โก-Cg2Fg-โ
           ; inj-S2T-โ to inj-Cg2Fg-โ
           ; inj-โช_โซโ to inj-โฆ_โงโ
           ; inj-S2T-โ to inj-Cg2Fg-โ
           ; inj-โช_โซโ to inj-โฆ_โงโ ) public

-- Derive uniqueness proof generically.
open Unique !-MkTy renaming (!-S2Tแถ to !-MkCtx) public

--------------------------------------------------------------------------------
open import Generic.CrossEq

-- TODO: rename MkTy to โโแต ?
_โโแต_ : FG.Ty โ CG.Ty โ Set
ฯโ โโแต ฯโ = MkTy ฯโ ฯโ

๐ป : CEq CG.Ty FG.Ty
๐ป = record { โฆ_โง = โฆ_โงแต ; _โโ_ = _โโแต_ ; โ_โ = โก-MkTy ; refl-โโ = mkTy ; !-โโ = !-MkTy }

-- For labeled values
๐ปแดธ : CEq CG.Ty FG.Ty
๐ปแดธ = record
     { โฆ_โง = ฮป ฯ โ โฆ Labeled ฯ โงแต
     ; _โโ_ = ฮป ฯโ ฯโ โ MkTy (Labeled ฯโ) ฯโ
     ; โ_โ = โก-MkTy
     ; refl-โโ = ฮป ฯ โ mkTy (Labeled ฯ)
     ; !-โโ = !-MkTy }
