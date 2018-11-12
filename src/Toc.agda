-- Table of Contents
--
-- This module provides direct references to the Agda objects that
-- encode the definitions and proofs of the paper "From Fine- to
-- Coarse-Grained Dynamic Information Flow Control and Back" by
-- Vassena, Russo, Vineet, Deepak, Stefan.
--
-- In emacs agda-mode, use command `C-c C-l` to load and compile the
-- proof script and command `M-.' to jump to definition of the
-- identifier under the cursor.  In the html generated files, simply
-- click on a term to jump to its definition.

module Toc where

open import Lattice.TwoPoint renaming (Low to L)

--------------------------------------------------------------------------------
-- §2. Fine Grained Calculus (λ^FG)
--------------------------------------------------------------------------------
module §2 where

  -- Well-typed syntax with De Brujin indexes.
  -- Expr Γ τ encodes a well-typed term: Γ ⊢ e : τ.
  figure₁ : Set
  figure₁ = ∀ {Γ : Ctx} {τ : Ty} → Expr Γ τ
    where open import FG.Types
          open import FG.Syntax

  -- Big-step semantics: c₁ ⇓⟨ θ , pc ⟩ c₂
  figure₂₃₄ : Set
  figure₂₃₄ = ∀ {τ Γ} {pc : Label} {c₁ : IConf Γ τ} {θ : Env Γ} {c₂ : FConf τ} →
                c₁ ⇓⟨ θ , pc ⟩ c₂
    where open import FG.Syntax
          open import FG.Semantics

  open import FG

  -- "The label of the result is at least as sensitive as the program counter"
  property₁ : ∀ {Σ Σ' Γ τ pc r ℓ} {e : Expr Γ τ} {v : Value τ} {θ : Env Γ} →
               ⟨ Σ , e ⟩ ⇓⟨ θ , pc ⟩ ⟨ Σ' , r ^ ℓ ⟩ →
               pc ⊑ ℓ
  property₁ = step-⊑

  -- L-equivalence
  figure₅ : Set
  figure₅ = ∀ {τ : Ty} {v₁ v₂ : Value τ} → v₁ ≈ⱽ⟨ L ⟩ v₂

  -- λ^FG TINI
  theorem₁ : ∀ {τ Γ θ₁ θ₂ pc} {c₁ c₂ : IConf Γ τ} {c₁' c₂' : FConf τ} →
             c₁ ⇓⟨ θ₁ , pc ⟩ c₁' →
             c₂ ⇓⟨ θ₂ , pc ⟩ c₂' →
             c₁ ≈ᴵ⟨ L ⟩ c₂ →
             θ₁ ≈ᴱ⟨ L ⟩ θ₂ →
             c₁' ≈ᶜ⟨ L ⟩ c₂'
  theorem₁ = tini
    where open import FG.Security L

  -- In the following TINI λ abbreviates the above definition of
  -- termination-insensitive non-interference for a generic calculus λ
  -- and generalizes to an arbitrary security level A.  For example:

  open import Generic.Calculus
  open import Data.Product
  open import Relation.Binary.PropositionalEquality

  theorem₁′ : TINI λ^FG
  theorem₁′ {A = A} c₁⇓ c₂⇓ c₁≈c₂ (θ₁≈θ₂ , refl) = tini c₁⇓ c₂⇓ c₁≈c₂ θ₁≈θ₂
    where open import FG.Security A

--------------------------------------------------------------------------------
-- §3. Coarse Grained Calculus (λ^CG)
--------------------------------------------------------------------------------
module §3 where

  -- Well-typed syntax with De Brujin indexes.
  -- Thunk Γ τ encodes a well-typed thunk: Γ ⊢ t : (LIO τ).
  figure₆ : Set
  figure₆ = ∀ {Γ : Ctx} {τ : Ty} → Thunk Γ τ
    where open import CG.Types
          open import CG.Syntax

  -- Forcing semantics.
  figure₇ᵃ : Set
  figure₇ᵃ =  ∀ {Γ τ θ} {c₁ : EConf Γ (LIO τ)} {c₂ : FConf τ} → c₁ ⇓ᶠ⟨ θ ⟩ c₂
    where open import CG.Types
          open import CG.Syntax
          open import CG.Semantics

  -- Pure semantics.
  figure₇ᵇ : Set
  figure₇ᵇ = ∀ {Γ τ} {e : Expr Γ τ} {θ : Env Γ} {v : Value τ} → e ⇓ᴾ⟨ θ ⟩ v
    where open import CG.Syntax
          open import CG.Semantics

  -- Thunk semantics (also Figure 8).
  figure₇ᶜ : Set
  figure₇ᶜ = ∀ {Γ τ θ} {c₁ : TConf Γ (LIO τ)} {c₂ : FConf τ} → c₁ ⇓⟨ θ ⟩ c₂
    where open import CG.Types
          open import CG.Syntax
          open import CG.Semantics

  open import CG

  -- "The final value of the program counter is at least as sensitive
  -- as the intial value."
  property₂ : ∀ {Γ τ Σ Σ' pc pc' v} {θ : Env Γ} {t : Thunk Γ (LIO τ)} →
                    ⟨ Σ , pc , t ⟩ ⇓⟨ θ ⟩ ⟨ Σ' , pc' , v ⟩ →
                    pc ⊑ pc'
  property₂ = step-⊑

  property₂′ : ∀ {Γ τ Σ Σ' pc pc' v} {θ : Env Γ} {e : Expr Γ (LIO τ)} →
                    ⟨ Σ , pc , e ⟩ ⇓ᶠ⟨ θ ⟩ ⟨ Σ' , pc' , v ⟩ →
                    pc ⊑ pc'
  property₂′ = stepᶠ-⊑

  -- L-equivalence
  figure₉ : Set
  figure₉  = ∀ {τ} {v₁ v₂ : Value τ} → v₁ ≈ⱽ v₂
    where open import CG.LowEq L

  open import Generic.Calculus

  -- λ^CG TINI
  theorem₂ : TINI λ^CG
  theorem₂ {A = A} = tiniᶠ
    where open import CG.Security A

--------------------------------------------------------------------------------
-- §4. Translation from λ^FG to λ^CG
--------------------------------------------------------------------------------
module §4 where

  open import FG2CG
  open import FG as FG
  open import CG as CG
  open import FG2CG.Syntax
  open import FG2CG.Correct

  -- Type translation
  figure·10ᵃ : FG.Ty → CG.Ty
  figure·10ᵃ = ⟪_⟫ᵗ

  -- Value translation.
  figure·10ᵇ : ∀ {τ} → FG.Value τ → CG.Value ⟪ τ ⟫ᵗ
  figure·10ᵇ = ⟪_⟫ⱽ

  -- Expression translation (Figure 11 and 13) and type preservation.
  lemma-4·1 : ∀ {Γ τ} → FG.Expr Γ τ → CG.Thunk ⟪ Γ ⟫ᶜ (LIO ⟪ τ ⟫ᵗ)
  lemma-4·1 = ⟪_⟫ᵀ

  -- Semantics Preservation.
  theorem₃ : ∀ {Σ Σ' Γ τ pc} {e : FG.Expr Γ τ} {v : FG.Value τ} {θ : FG.Env Γ} →
             ⟨ Σ , e ⟩ ⇓⟨ θ , pc ⟩ ⟨ Σ' , v ⟩ →
             ⟨ ⟪ Σ ⟫ˢ , pc , ⟪ e ⟫ᴱ ⟩ ⇓ᶠ⟨ ⟪ θ ⟫ᵉ ⟩  ⟨ ⟪ Σ' ⟫ˢ , pc , ⟪ v ⟫ⱽ ⟩
  theorem₃ = fg2cgᶠ

  open import Function.Equivalence
  open import FG2CG.Recovery L

  -- Lifting and unlifting L-equivalence of initial configurations and
  -- all syntactic categories.
  lemma-4·2 : ∀ {Γ τ} {c₁ c₂ : FG.IConf Γ τ} pc → c₁ FG.≈ᴵ⟨ L ⟩ c₂ ⇔ (⟪ c₁ ⟫ᴵ pc) CG.≈ᴵ⟨ L ⟩ (⟪ c₂ ⟫ᴵ pc)
  lemma-4·2 pc = equivalence (lift-≈ᴵ pc) (unlift-≈ᴵ pc)

  -- Back-translation of L-equivalence from target to source for final
  -- configurations with public program counter.
  lemma-4·3 : ∀ {τ pc} {c₁ c₂ : FG.FConf τ} →
                     let ⟨ Σ₁ , r₁ ^ ℓ₁ ⟩ = c₁
                         ⟨ Σ₂ , r₂ ^ ℓ₂ ⟩ = c₂ in
                     pc ⊑ ℓ₁ →
                     pc ⊑ ℓ₂ →
                     (⟪ c₁ ⟫ pc) CG.≈ᶜ⟨ L ⟩ (⟪ c₂ ⟫ pc) →
                     c₁ FG.≈ᶜ⟨ L ⟩ c₂
  lemma-4·3 = unlift-≈ᶜ

  open import Generic.Calculus
  open import Relation.Binary.PropositionalEquality
  open import Data.Product

  -- Recovery of λ^FG TINI via ⟪·⟫
  theorem₄ : TINI λ^FG
  theorem₄ {A = A} c₁⇓ c₂⇓ c₁≈c₂ (θ₁≈θ₂ , refl) = R.tini-via-cg c₁⇓ c₂⇓ c₁≈c₂ θ₁≈θ₂
    where open import FG2CG.Recovery A as R

--------------------------------------------------------------------------------
-- §5. Translation from λ^CG to λ^FG
--------------------------------------------------------------------------------
module §5 where

  open import CG2FG
  open import FG as FG hiding (_×_)
  open import CG as CG hiding (_×_)
  open import CG2FG.Syntax
  open import CG2FG.Correct
  open import Data.Product as P using (_×_ ; ∃ ; uncurry) renaming (_,_ to _∧_)

  -- Type translation
  figure·14ᵃ : CG.Ty → FG.Ty
  figure·14ᵃ = ⟦_⟧ᵗ

  -- Value translation.
  figure·14ᵇ : ∀ {τ} → CG.Value τ → Label → FG.Value ⟦ τ ⟧ᵗ
  figure·14ᵇ = ⟦_⟧ⱽ

  -- Expression translation (Figure 15a) and type preservation.
  lemma-5·1 : ∀ {Γ τ} (e : CG.Expr Γ τ) → FG.Expr ⟦ Γ ⟧ᶜ ⟦ τ ⟧ᵗ
  lemma-5·1 = ⟦_⟧ᴱ

  -- Thunk translation (also Figure 16).
  figure·15ᵇ : ∀ {Γ τ} (t : CG.Thunk Γ (LIO τ)) → FG.Expr ⟦ Γ ⟧ᶜ ⟦ τ ⟧ᵗ
  figure·15ᵇ = ⟦_⟧ᵀ

  open import CG2FG.CrossEq

  -- Cross-language semantics equivalence up to extra annotations.
  figure·17 : ∀ {τ} → FG.Value ⟦ τ ⟧ᵗ → Label → CG.Value τ → Set
  figure·17 v₁ pc v₂ = v₁ ↓≈⟨ pc ⟩ⱽ v₂
    where open import CG2FG.Graph

  open import Function.Equivalence

  -- Equivalence of configurations.
  definition₁ : ∀ {Γ τ Σ₁ Σ₂ pc} {e : CG.Expr Γ (LIO τ)} →
                   ⟨ Σ₁ , ⟦ e ⟧ᴱ FG.∘ Id （） ⟩ ↓≈ᴵ ⟨ Σ₂ , pc , e ⟩ ⇔ (Σ₁ ↓≈ˢ Σ₂)
  definition₁ = equivalence ⌜_⌝ᴵ ⌞_⌟ᴵ

  definition₁′ : ∀ {Γ τ Σ₁ Σ₂ pc} {t : CG.Thunk Γ (LIO τ)} →
                   ⟨ Σ₁ , ⟦ t ⟧ᵀ ⟩ ↓≈ᵀ ⟨ Σ₂ , pc , t ⟩ ⇔ (Σ₁ ↓≈ˢ Σ₂)
  definition₁′ = equivalence ⌜_⌝ᵀ ⌞_⌟ᵀ

  definition₁′′ : ∀ {τ Σ₁ Σ₂ pc} {v : CG.Value τ} {r : FG.Raw ⟦ τ ⟧ᵗ} →
                     ⟨ Σ₁ , r ^ pc ⟩ ↓≈ᶜ ⟨ Σ₂ , pc , v ⟩ ⇔ ((Σ₁ ↓≈ˢ Σ₂) × (r ↓≈⟨ pc ⟩ᴿ v))
  definition₁′′ = equivalence ( λ { ⟨ Σ₁≈Σ₂ , r≈v ⟩ → Σ₁≈Σ₂ ∧ ⌞ r≈v ⌟ᴿ }) (uncurry ⟨_,_⟩)

  -- Reflexivity of ↓≈
  property₃ : ∀ {Γ τ} (c : CG.EConf Γ (LIO τ)) → ⟦ c ⟧ᴵ ↓≈ᴵ c
  property₃ c = refl-≈ᴵ c

  open import Function

  -- Weakening of ↓≈
  property₄ :  ∀ {τ pc pc'} {r₁ : FG.Raw ⟦ τ ⟧ᵗ} {v₂ : CG.Value τ} →
                  pc ⊑ pc' →
                  r₁ ↓≈⟨ pc ⟩ᴿ v₂ →
                  r₁ ↓≈⟨ pc' ⟩ᴿ v₂
  property₄ = flip ≈ᴿ-⊑

  property₄′ :  ∀ {τ pc pc'} {v₁ : FG.Value ⟦ τ ⟧ᵗ} {v₂ : CG.Value τ} →
                  pc ⊑ pc' →
                  v₁ ↓≈⟨ pc ⟩ⱽ v₂ →
                  v₁ ↓≈⟨ pc' ⟩ⱽ v₂
  property₄′ = flip ≈ⱽ-⊑

  property₄′′ :  ∀ {Γ pc pc'} {θ₁ : FG.Env ⟦ Γ ⟧ᶜ} {θ₂ : CG.Env Γ} →
                  pc ⊑ pc' →
                  θ₁ ↓≈⟨ pc ⟩ᵉ θ₂ →
                  θ₁ ↓≈⟨ pc' ⟩ᵉ θ₂
  property₄′′ = flip ≈ᵉ-⊑

  -- ⟦·⟧ preserves pure semantics.
  lemma-5·2 : ∀ {Γ τ Σ pc} {θ : CG.Env Γ} {θ' : FG.Env ⟦ Γ ⟧ᶜ} {e : CG.Expr Γ τ} {v : CG.Value τ} →
                θ' ↓≈⟨ pc ⟩ᵉ θ →
                e ⇓ᴾ⟨ θ ⟩ v →
                ∃ (λ r → (r ↓≈⟨ pc ⟩ᴿ v) × (⟨ Σ , ⟦ e ⟧ᴱ ⟩ ⇓⟨ θ' , pc ⟩ ⟨ Σ , r ^ pc ⟩))
  lemma-5·2 = cg2fgᴾ _ _

  -- ⟦·⟧ preserves forcing semantics.
  theorem₅ : ∀ {Γ τ θ₁ c₂' c₁} {θ₂ : CG.Env Γ} {c₂ : EConf Γ (LIO τ)} →
                let ⟨ Σ , pc , t ⟩ = c₂ in
                    θ₁ ↓≈⟨ pc ⟩ᵉ θ₂ →
                    c₁ ↓≈ᴵ c₂ →
                    c₂ ⇓ᶠ⟨ θ₂ ⟩ c₂' →
                    ∃ (λ c₁' → c₁' ↓≈ᶜ c₂' × c₁ ⇓⟨ θ₁ , pc ⟩ c₁' )
  theorem₅ = cg2fgᶠ

  -- ⟦·⟧ preserves thunk semantics.
  theorem₅′ : ∀ {Γ τ θ₁ c₂' c₁} {θ₂ : CG.Env Γ} {c₂ : CG.TConf Γ (LIO τ)} →
               let ⟨ Σ , pc , e ⟩ = c₂ in
                   θ₁ ↓≈⟨ pc ⟩ᵉ θ₂ →
                   c₁ ↓≈ᵀ c₂ →
                   c₂ ⇓⟨ θ₂ ⟩ c₂' →
                   ∃ (λ c₁' → c₁' ↓≈ᶜ c₂' × c₁ ⇓⟨ θ₁ , pc ⟩ c₁' )
  theorem₅′ = cg2fg


  -- Correctness ⟦·⟧
  corollary₁ : ∀ {τ Γ c₂'} {θ : CG.Env Γ} {c₂ : CG.EConf Γ (LIO τ)} →
                let ⟨ Σ , pc , e ⟩ = c₂ in
                c₂ ⇓ᶠ⟨ θ ⟩ c₂' →
                ∃ (λ c₁' → c₁' ↓≈ᶜ c₂' × ⟦ c₂ ⟧ᴵ ⇓⟨ ⟦ θ ⟧ᵉ pc  , pc ⟩ c₁' )
  corollary₁ = ⟦·⟧-correct

  open import CG2FG.Recovery L

  -- Lifting L-equivalence from source to target.
  lemma-5·3 : ∀ {Γ τ} {c₁ c₂ : CG.EConf Γ (LIO τ)} →
                  c₁ CG.≈ᴵ⟨ L ⟩ c₂ →
                  ⟦ c₁ ⟧ᴵ FG.≈ᴵ⟨ L ⟩ ⟦ c₂ ⟧ᴵ
  lemma-5·3 = lift-≈ᴵ

  -- Unlifting L-equivalence from target to source
  lemma-5·4 : ∀ {pc τ} {v₁ v₂ : FG.Value ⟦ τ ⟧ᵗ} {v₁' v₂' : CG.Value τ} →
                  pc ⊑ L →
                  v₁ FG.≈ⱽ⟨ L ⟩ v₂ →
                  v₁ ↓≈⟨ pc ⟩ⱽ v₁'  →
                  v₂ ↓≈⟨ pc ⟩ⱽ v₂'  →
                  v₁' CG.≈ⱽ⟨ L ⟩ v₂'
  lemma-5·4 = unlift-≈ⱽ

  lemma-5·4′ : ∀ {pc τ} {r₁ r₂ : FG.Raw ⟦ τ ⟧ᵗ} {v₁' v₂' : CG.Value τ} →
                  pc ⊑ L →
                  r₁ FG.≈ᴿ⟨ L ⟩ r₂ →
                  r₁ ↓≈⟨ pc ⟩ᴿ v₁'  →
                  r₂ ↓≈⟨ pc ⟩ᴿ v₂'  →
                  v₁' CG.≈ⱽ⟨ L ⟩ v₂'
  lemma-5·4′ = unlift-≈ᴿ

  lemma-5·4′′ : ∀ {pc Γ} {θ₁ θ₂ : FG.Env ⟦ Γ ⟧ᶜ} {θ₁' θ₂' : CG.Env Γ} →
                  pc ⊑ L →
                  θ₁ FG.≈ᴱ⟨ L ⟩ θ₂ →
                  θ₁ ↓≈⟨ pc ⟩ᵉ θ₁'  →
                  θ₂ ↓≈⟨ pc ⟩ᵉ θ₂'  →
                  θ₁' CG.≈ᴱ⟨ L ⟩ θ₂'
  lemma-5·4′′ = unlift-≈ᴱ

  lemma-5·4′′′ : ∀ {ℓ} {M₁' M₂'} {M₁ M₂ : FG.Memory ℓ} →
                 M₁ FG.≈ᴹ⟨ L ⟩ M₂ →
                 M₁ ↓≈ᴹ M₁' →
                 M₂ ↓≈ᴹ M₂' →
                 M₁' CG.≈ᴹ⟨ L ⟩ M₂'
  lemma-5·4′′′ = unlift-≈⟨ _ ⟩ᴹ

  lemma-5·4′′′′  : ∀ {Σ₁ Σ₂ Σ₁' Σ₂'} →
                      Σ₁ FG.≈ˢ⟨ L ⟩ Σ₂ →
                      Σ₁ ↓≈ˢ Σ₁' →
                      Σ₂ ↓≈ˢ Σ₂' →
                      Σ₁' CG.≈ˢ⟨ L ⟩ Σ₂'
  lemma-5·4′′′′ = unlift-≈ˢ

  lemma-5·5 : ∀ {τ τ'} {c₁' c₂' : CG.FConf τ} {c₁ c₂ : FG.FConf τ'} →
              c₁ FG.≈ᶜ⟨ L ⟩ c₂ →
              c₁ ↓≈ᶜ c₁' →
              c₂ ↓≈ᶜ c₂' →
              c₁' CG.≈ᶜ⟨ L ⟩ c₂'
  lemma-5·5 = unlift-≈ᶜ

  open import Generic.Calculus

  -- Recovery of λ^CG TINI via ⟦·⟧
  theorem₆ : TINI λ^CG
  theorem₆ {A = A} = R.tini-via-fg
    where open import CG2FG.Recovery A as R
