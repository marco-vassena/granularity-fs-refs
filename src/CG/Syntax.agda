-- Well-typed syntax

open import Lattice

module CG.Syntax {{๐ณ : Lattice}} where

open import CG.Types
open import Data.Nat using (โ)

mutual

  -- (e : Expr ฮ ฯ) represents a term t of type ฯ in the context ฮ,
  -- i.e., ฮ โข t โท ฯ. Note that this definition merges syntax and tpying
  -- judgment: only well-typed terms can be constructed with it.
  data Expr (ฮ : Ctx) : Ty โ Set where

    -- Unit
    ๏ผ๏ผ : Expr ฮ unit

    -- First class labels.
    โ_โ : (โ : Label) โ Expr ฮ ๐

    -- โโ โ-? โโ tests if โโ can flow to โโ
    _โ-?_ : Expr ฮ ๐ โ Expr ฮ ๐ โ Expr ฮ Bool

    --------------------------------------------------------------------------------
    -- Basic ฮป-calculus

    -- Variables with De Bruijn indexes
    var : โ {ฯ} โ  (ฯโฮ : ฯ โ ฮ) โ Expr ฮ ฯ

    -- Functions
    ฮ : โ {ฯโ ฯโ} โ Expr (ฯโ โท ฮ) ฯโ โ Expr ฮ (ฯโ โ ฯโ)

    -- Function application
    _โ_ : โ {ฯโ ฯโ} โ Expr ฮ (ฯโ โ ฯโ) โ Expr ฮ ฯโ โ Expr ฮ ฯโ

    --------------------------------------------------------------------------------
    -- Pairs

    โจ_,_โฉ : โ {ฯโ ฯโ} โ Expr ฮ ฯโ โ Expr ฮ ฯโ โ Expr ฮ (ฯโ ร ฯโ)

    fst : โ {ฯโ ฯโ} โ Expr ฮ (ฯโ ร ฯโ) โ Expr ฮ ฯโ

    snd : โ {ฯโ ฯโ} โ Expr ฮ (ฯโ ร ฯโ) โ Expr ฮ ฯโ

    --------------------------------------------------------------------------------
    -- Sum

    inl : โ {ฯโ ฯโ} โ Expr ฮ ฯโ โ Expr ฮ (ฯโ + ฯโ)

    inr : โ {ฯโ ฯโ} โ Expr ฮ ฯโ โ Expr ฮ (ฯโ + ฯโ)

    case : โ {ฯโ ฯโ ฯโ} โ Expr ฮ (ฯโ + ฯโ) โ Expr (ฯโ โท ฮ) ฯโ โ Expr (ฯโ โท ฮ) ฯโ โ Expr ฮ ฯโ

    --------------------------------------------------------------------------------
    -- Lifts a Thunk (LIO computation) to Expr.

    โ_โแต : โ {ฯ} โ (t : Thunk ฮ (LIO ฯ)) โ Expr ฮ (LIO ฯ)

    --------------------------------------------------------------------------------
    -- Explicit weakening

    wken : โ {ฯ ฮ'} โ Expr ฮ' ฯ โ ฮ' โ ฮ โ Expr ฮ ฯ

  -- LIO monad
  data Thunk (ฮ : Ctx) : Ty โ Set where

    -- Encapsulates a value in the monad
    return : โ {ฯ} โ Expr ฮ ฯ โ Thunk ฮ (LIO ฯ)

    -- Monadic bind
    bind : โ {ฯโ ฯโ} โ Expr ฮ (LIO ฯโ) โ Expr (ฯโ โท ฮ) (LIO ฯโ) โ Thunk ฮ (LIO ฯโ)

    --------------------------------------------------------------------------------
    -- Basic labeled values

    -- Unlabel a labeled value
    unlabel : โ {ฯ} โ Expr ฮ (Labeled ฯ) โ Thunk ฮ (LIO ฯ)

    -- toLabeled creates a labeled value out of an LIO computation
    toLabeled : โ {ฯ} โ Expr ฮ (LIO ฯ) โ Thunk ฮ (LIO (Labeled ฯ))

   --------------------------------------------------------------------------------
   -- Label introspection.

    -- Retrieve the label of a labeled value
    labelOf : โ {ฯ} โ Expr ฮ (Labeled ฯ) โ Thunk ฮ (LIO ๐)

    -- Retrieve the current label of the context, i.e., the program counter
    getLabel : Thunk ฮ (LIO ๐)

    -- taint(โ) raises the program counter to โ
    taint : Expr ฮ ๐ โ Thunk ฮ (LIO unit)

   --------------------------------------------------------------------------------
   -- Memory operations

    -- Creates a new mutable reference at a given security level
    new : โ {ฯ s} โ Expr ฮ (Labeled ฯ) โ Thunk ฮ (LIO (Ref s ฯ))

    -- Reads the content of a mutable reference
    !_ : โ {ฯ s} โ Expr ฮ (Ref s ฯ) โ Thunk ฮ (LIO ฯ)

    -- Overvwrites the content of a mutable reference
    _โ_ : โ {ฯ s} โ Expr ฮ (Ref s ฯ) โ Expr ฮ (Labeled ฯ) โ Thunk ฮ (LIO unit)

    -- Retrieve the label of a labeled reference
    labelOfRef : โ {ฯ s} โ Expr ฮ (Ref s ฯ) โ Thunk ฮ (LIO ๐)

  -- Value enviroment
  data Env : (ฮ : Ctx) โ Set where
    [] : Env []
    _โท_  : โ {ฮ ฯ} โ (v : Value ฯ) (ฮธ : Env ฮ) โ Env (ฯ โท ฮ)

  -- Value.
  data Value : Ty โ Set where

    ๏ผ๏ผ : Value unit

    -- Function closure
    โจ_,_โฉแถ : โ {ฮ ฯโ ฯโ} โ (e : Expr (ฯโ โท ฮ) ฯโ) (ฮธ : Env ฮ) โ Value (ฯโ โ ฯโ)

    -- Thunk closure
    โจ_,_โฉแต : โ {ฮ ฯ} โ (t : Thunk ฮ (LIO ฯ)) (ฮธ : Env ฮ) โ Value (LIO ฯ)

    inl : โ {ฯโ ฯโ} โ Value ฯโ โ Value (ฯโ + ฯโ)

    inr : โ {ฯโ ฯโ} โ Value ฯโ โ Value (ฯโ + ฯโ)

    โจ_,_โฉ : โ {ฯโ ฯโ} โ Value ฯโ โ Value ฯโ โ Value (ฯโ ร ฯโ)

    -- Labeled value
    Labeled : โ {ฯ} (โ : Label) โ Value ฯ โ Value (Labeled ฯ)

    -- Labeled reference (flow insensitive)
    Refแดต : โ {ฯ} (โ : Label) (n : โ) โ Value (Ref I ฯ)

    -- Labeled reference (flow sensitive)
    Refหข : โ {ฯ} โ โ โ Value (Ref S ฯ)

    -- First class labels
    โ_โ : (โ : Label) โ Value ๐


infixr 5 _โท_

-- Shorthands for Booleans

true : Value Bool
true = inl ๏ผ๏ผ

false : Value Bool
false = inr ๏ผ๏ผ

if_then_else_ : โ {ฮ ฯ} โ Expr ฮ Bool โ Expr ฮ ฯ โ Expr ฮ ฯ โ Expr ฮ ฯ
if_then_else_ c t e = case c (wken t (drop refl-โ)) (wken e (drop refl-โ))

--------------------------------------------------------------------------------
-- Configurations

-- Pair of value and label (isomorphic to labeled value)
LValue : Ty โ Set
LValue ฯ = Value ฯ P.ร Label
  where import Data.Product as P

-- Generic store and flow-sensitive heap
open import Generic.PState Ty Ty Value LValue public

-- Generic configuration container.
record Conf (F : Ctx โ Ty โ Set) (ฮ : Ctx) (ฯ : Ty) : Set where
  constructor โจ_,_,_,_โฉ
  field store : Store
        heap : Heap
        pc : Label
        term : F ฮ ฯ

-- Initial Configuration (Expr)
EConf : Ctx โ Ty โ Set
EConf ฮ ฯ = Conf Expr ฮ ฯ

-- Initial Configuration (Thunk)
TConf : Ctx โ Ty โ Set
TConf ฮ ฯ = Conf Thunk ฮ ฯ

-- Final configuration (Value)
FConf : Ty โ Set
FConf ฯ = Conf (const Value) [] ฯ
  where open import Function

--------------------------------------------------------------------------------
-- Weakening once and twice.

_โยน : โ {ฮ ฯ ฯโ} โ Expr ฮ ฯ โ Expr (ฯโ โท ฮ) ฯ
e โยน = wken e (drop refl-โ)

_โยฒ : โ {ฮ ฯ ฯโ ฯโ} โ Expr ฮ ฯ โ Expr (ฯโ โท ฯโ โท ฮ) ฯ
e โยฒ = wken e (drop (drop refl-โ))

--------------------------------------------------------------------------------
-- Environment operations and proofs

-- Merge environments.
_++แดฑ_ : โ {ฮโ ฮโ} โ Env ฮโ โ Env ฮโ โ Env (ฮโ ++ ฮโ)
[] ++แดฑ ฮธโ = ฮธโ
(v โท ฮธโ) ++แดฑ ฮธโ = v โท (ฮธโ ++แดฑ ฮธโ)

-- Lookup a variable in the environment.
_!!_ : โ {ฯ ฮ} โ Env ฮ โ ฯ โ ฮ โ Value ฯ
(v โท ฮธ) !! here = v
(v โท ฮธ) !! (there ฯโฮ) = ฮธ !! ฯโฮ

-- Shrink enviroment.
slice : โ {ฮโ ฮโ} โ Env ฮโ โ ฮโ โ ฮโ โ Env ฮโ
slice [] base = []
slice (v โท ฮธ) (cons p) = v โท slice ฮธ p
slice (v โท ฮธ) (drop p) = slice ฮธ p

--------------------------------------------------------------------------------
-- Basic proofs and rewriting.

open import Relation.Binary.PropositionalEquality

slice-refl-โ-โก : โ {ฮ} {ฮธ : Env ฮ} โ slice ฮธ refl-โ โก ฮธ
slice-refl-โ-โก {ฮธ = []} = refl
slice-refl-โ-โก {ฮธ = v โท ฮธ} rewrite slice-refl-โ-โก {_} {ฮธ} = refl

{-# REWRITE slice-refl-โ-โก #-}

slice-drop-โ-โก : โ {ฮโ ฮโ} (ฮธโ : Env ฮโ) (ฮธโ : Env ฮโ) โ slice (ฮธโ ++แดฑ ฮธโ) (drop-โโ ฮโ ฮโ) โก ฮธโ
slice-drop-โ-โก ฮธโ [] = refl
slice-drop-โ-โก ฮธโ (v โท ฮธโ) = slice-drop-โ-โก ฮธโ ฮธโ

{-# REWRITE slice-drop-โ-โก #-}
