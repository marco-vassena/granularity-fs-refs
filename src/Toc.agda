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

open import Lattice using (_⋤_)
open import Lattice.TwoPoint renaming (Low to L)
open import Generic.Bijection hiding (_⇔_)

--------------------------------------------------------------------------------
-- §2. Fine Grained Calculus (λ^FG)
--------------------------------------------------------------------------------
module §2 where

  open import Relation.Binary.PropositionalEquality

  -- Well-typed syntax with De Brujin indexes.
  -- Expr Γ τ encodes a well-typed term: Γ ⊢ e : τ.
  figure-2·1 : Set
  figure-2·1 = ∀ {Γ : Ctx} {τ : Ty} → Expr Γ τ
    where open import FG.Types
          open import FG.Syntax

  -- Big-step semantics: c₁ ⇓⟨ θ , pc ⟩ c₂ (also figure 2.3 and 2.4)
  figure-2·2 : Set
  figure-2·2 = ∀ {τ Γ} {pc : Label} {c₁ : IConf Γ τ} {θ : Env Γ} {c₂ : FConf τ} →
                c₁ ⇓⟨ θ , pc ⟩ c₂
    where open import FG.Syntax
          open import FG.Semantics

  open import FG hiding (_⊆_ ; _×_ ; _∘_)

  -- "The label of the result is at least as sensitive as the program counter"
  property-1 : ∀ {Σ Σ' μ μ' Γ τ pc r ℓ} {e : Expr Γ τ} {v : Value τ} {θ : Env Γ} →
               ⟨ Σ , μ , e ⟩ ⇓⟨ θ , pc ⟩ ⟨ Σ' , μ' , r ^ ℓ ⟩ →
               pc ⊑ ℓ
  property-1 = step-⊑

  -- L-equivalence
  figure-2·5 : Set
  figure-2·5 = ∀ {β : Bij} {τ : Ty} {v₁ v₂ : Value τ} → v₁ ≈ⱽ⟨ L , β ⟩ v₂

  -- Bijection
  definition-1 : Set
  definition-1 = Bij

  -- Property 3: Identity laws for bijections
  -- Inverse Identity
  property-3·1 : ∀ n → (ι n) ≡ (ι n)⁻¹
  property-3·1 = ι-inv

  -- Absorb Left
  property-3·2 : ∀ {n β} →  β ⊆ᴿ (ι n) → (ι n ∘ β) ≡ β
  property-3·2 = absorb-ι₁

  -- Absorb Right
  property-3·3 : ∀ {n β} → β ⊆ᴰ (ι n) → (β ∘ ι n) ≡ β
  property-3·3 = absorb-ι₂

  -- Heap L-equivalence
  definition-2 : Set
  definition-2 = ∀ {μ₁ μ₂ : Heap} {β : Bij} → μ₁ ≈⟨ β ⟩ᴴ μ₂
    where open import FG.LowEq L

  -- Valid raw value judgment
  figure-2·8ᵃ : Set
  figure-2·8ᵃ = ∀ {n} {τ : Ty} {r : Raw τ} → Validᴿ n r

  -- Valid output judgment
  figure-2·8ᵇ : Set
  figure-2·8ᵇ = ∀ {τ} {c : FConf τ} → Valid-Outputs c

  open import Data.Nat

  -- Valid weakinig for values, raw values, and environments.

  lemma-2·5·1 : ∀ {τ n n'} (v : Value τ) → n ≤ n' → Validⱽ n v → Validⱽ n' v
  lemma-2·5·1 = wken-validⱽ

  lemma-2·5·2 : ∀ {τ n n'} (r : Raw τ) → n ≤ n' → Validᴿ n r → Validᴿ n' r
  lemma-2·5·2 = wken-validᴿ

  lemma-2·5·3 : ∀ {Γ n n'} (θ : Env Γ) → n ≤ n' → Validᴱ n θ → Validᴱ n' θ
  lemma-2·5·3 = wken-validᴱ

  -- Heaps only grow
  lemma-2·6 : ∀ {τ Γ θ pc} {c : IConf Γ τ} {c' : FConf τ} →
                c ⇓⟨ θ , pc ⟩ c' →
                ∥ Conf.heap c ∥ᴴ ≤ ∥ Conf.heap c' ∥ᴴ
  lemma-2·6 = step-≤

  open import Data.Product renaming (_,_ to _∧_)

  -- Valid invariant
  property-4 : ∀ {τ Γ ℓ} {θ : Env Γ} {c : IConf Γ τ} {c' : FConf τ} →
                 c ⇓⟨ θ , ℓ ⟩ c' →
                 Valid-Inputs c θ →
                 Valid-Outputs c'
  property-4 x y = proj₂ (valid-invariant x y)

  -- Reflexivity
  property-5·1 : ∀ {μ : Heap} {{validᴴ : Validᴴ μ}} → μ ≈ᴴ⟨ L , ι ∥ μ ∥ᴴ ⟩ μ
  property-5·1 {{validᴴ}} = refl-≈ᴴ {{validᴴ}}
    where open import FG.LowEq L

  -- Symmetricity
  property-5·2 : ∀ {β} {μ₁ μ₂ : Heap} →
                   μ₁ ≈ᴴ⟨ L , β ⟩ μ₂ →
                   μ₂ ≈ᴴ⟨ L , β ⁻¹ ⟩ μ₁
  property-5·2 = sym-≈ᴴ
    where open import FG.LowEq L

  -- Transitivity
  property-5·3 : ∀ {β₁ β₂} {μ₁ μ₂ μ₃ : Heap} →
                   μ₁ ≈ᴴ⟨ L , β₁ ⟩ μ₂ →
                   μ₂ ≈ᴴ⟨ L , β₂ ⟩ μ₃ →
                   μ₁ ≈ᴴ⟨ L , β₂ ∘ β₁ ⟩ μ₃
  property-5·3 = trans-≈ᴴ
    where open import FG.LowEq L

  -- Weakening
  property-5·4 : ∀ {β β' τ} {v₁ v₂ : Value τ} →
                   β ⊆ β' →
                   v₁ ≈ⱽ⟨ L , β ⟩ v₂ →
                   v₁ ≈ⱽ⟨ L , β' ⟩ v₂
  property-5·4 = wken-≈ⱽ
    where open import FG.LowEq L

  -- Square commuatitve digram for heaps
  lemma-2·7 : ∀ {μ₁ μ₁' μ₂ μ₂' β β₁ β₂} →
                μ₁ ≈ᴴ⟨ L , β ⟩ μ₂ →
                μ₁ ≈ᴴ⟨ L , β₁ ⟩ μ₁' →
                μ₂ ≈ᴴ⟨ L , β₂ ⟩ μ₂' →
                μ₁' ≈ᴴ⟨ L , β₂ ∘ β ∘ (β₁ ⁻¹) ⟩ μ₂'
  lemma-2·7 = square-≈ᴴ
    where open import FG.LowEq L


  -- Square simplified with identity bijections.
  lemma-2·7' : ∀ {β μ₁ μ₁' μ₂ μ₂'} →
                μ₁ ≈ᴴ⟨ L , β ⟩ μ₂ →
                μ₁ ≈ᴴ⟨ L , ι ∥ μ₁ ∥ᴴ ⟩ μ₁' →
                μ₂ ≈ᴴ⟨ L , ι ∥ μ₂ ∥ᴴ ⟩ μ₂' →
                μ₁' ≈ᴴ⟨ L , β ⟩ μ₂'
  lemma-2·7' = square-≈ᴴ-ι
    where open import FG.LowEq L

  -- Store and heap confinement
  lemma-2·8 :  ∀ {τ Γ θ pc} {c : IConf Γ τ} {c' : FConf τ} →
               let ⟨ Σ , μ , _ ⟩ = c
                   ⟨ Σ' , μ' , _ ⟩ = c' in
                   {{validᴾ : Validᴾ ⟨ Σ , μ ⟩ }} {{validᴱ : Validᴱ ∥ μ ∥ᴴ θ}} →
                   c ⇓⟨ θ , pc ⟩ c' →
                   pc ⋤ L →
                   ⟨ Σ , μ ⟩ ≈ᴾ⟨ L , ι ∥ μ ∥ᴴ ⟩ ⟨ Σ' , μ' ⟩
  lemma-2·8 = step-≈ᴾ
    where open import FG.Security L

  -- L-equivalence preservation in secret contexts
  lemma-2·9 : ∀ {τ Γ₁ Γ₂ θ₁ θ₂ pc₁ pc₂ β} {c₁ : IConf Γ₁ τ} {c₂ : IConf Γ₂ τ}
                {c₁' c₂' : FConf τ} →
             let ⟨ Σ₁ , μ₁ , _ ⟩ = c₁
                 ⟨ Σ₂ , μ₂ , _ ⟩ = c₂ in
             {{valid₁ : Valid-Inputs c₁ θ₁}} {{valid₂ : Valid-Inputs c₂ θ₂}} →
             ⟨ Σ₁ , μ₁ ⟩ ≈ᴾ⟨ L , β ⟩ ⟨ Σ₂ , μ₂ ⟩ →
             c₁ ⇓⟨ θ₁ , pc₁ ⟩ c₁' →
             c₂ ⇓⟨ θ₂ , pc₂ ⟩ c₂' →
             pc₁ ⋤ L → pc₂ ⋤ L →
             ∃ (λ β' → β ⊆ β' × c₁' ≈ᶜ⟨ L , β' ⟩ c₂')
  lemma-2·9 = tiniᴴ
     where open import FG.Security L

  -- L-equivalence preservation in public contexts
  lemma-2·10 : ∀ {pc β τ Γ μ₁ μ₂ Σ₁ Σ₂ e} {θ₁ θ₂ : Env Γ} {c₁' c₂' : FConf τ} →
                    let c₁ = ⟨ Σ₁ , μ₁ , e ⟩
                        c₂ = ⟨ Σ₂ , μ₂ , e ⟩ in
                    {{valid₁ : Valid-Inputs c₁ θ₁}} {{valid₂ : Valid-Inputs c₂ θ₂}} →
                    c₁ ⇓⟨ θ₁ , pc ⟩ c₁' →
                    c₂ ⇓⟨ θ₂ , pc ⟩ c₂' →
                    ⟨ Σ₁ , μ₁ ⟩ ≈ᴾ⟨ L , β ⟩ ⟨ Σ₂ , μ₂ ⟩ →
                    θ₁ ≈ᴱ⟨ L , β ⟩ θ₂ →
                    pc ⊑ L →
                    ∃ (λ β' → β ⊆ β' × c₁' ≈ᶜ⟨ L , β' ⟩ c₂')
  lemma-2·10 = tiniᴸ
     where open import FG.Security L

  -- λ^FG TINI with Bijections
  theorem-2 : ∀ {τ Γ θ₁ θ₂ pc β} {c₁ c₂ : IConf Γ τ} {c₁' c₂' : FConf τ} →
             Valid-Inputs c₁ θ₁ →
             Valid-Inputs c₂ θ₂ →
             c₁ ⇓⟨ θ₁ , pc ⟩ c₁' →
             c₂ ⇓⟨ θ₂ , pc ⟩ c₂' →
             c₁ ≈ᴵ⟨ L , β ⟩ c₂ →
             θ₁ ≈ᴱ⟨ L , β ⟩ θ₂ →
             ∃ (λ β' → β ⊆ β' × c₁' ≈ᶜ⟨ L , β' ⟩ c₂')
  theorem-2 valid₁ valid₂ = tini {{valid₁}} {{valid₂}}
    where open import FG.Security L

  -- In the following TINI λ abbreviates the above definition of
  -- termination-insensitive non-interference for a generic calculus λ
  -- and generalizes to an arbitrary security level A.  For example:

  open import Generic.Calculus
  open import Relation.Binary.PropositionalEquality

  theorem-2′ : TINI λ^FG
  theorem-2′ {A = A} isV₁ isV₂ c₁⇓ c₂⇓ c₁≈c₂ (θ₁≈θ₂ ∧ refl) = tini {{isV₁}} {{isV₂}} c₁⇓ c₂⇓ c₁≈c₂ θ₁≈θ₂
    where open import FG.Security A

--------------------------------------------------------------------------------
-- §3. Coarse Grained Calculus (λ^CG)
--------------------------------------------------------------------------------
module §3 where

  -- Well-typed syntax with De Brujin indexes.
  -- Thunk Γ τ encodes a well-typed thunk: Γ ⊢ t : (LIO τ).
  figure-3·1 : Set
  figure-3·1 = ∀ {Γ : Ctx} {τ : Ty} → Thunk Γ τ
    where open import CG.Types
          open import CG.Syntax

  -- Pure semantics.
  figure-3·2 : Set
  figure-3·2 = ∀ {Γ τ} {e : Expr Γ τ} {θ : Env Γ} {v : Value τ} → e ⇓ᴾ⟨ θ ⟩ v
    where open import CG.Syntax
          open import CG.Semantics

  -- Forcing semantics.
  figure-3·3ᵃ : Set
  figure-3·3ᵃ =  ∀ {Γ τ θ} {c₁ : EConf Γ (LIO τ)} {c₂ : FConf τ} → c₁ ⇓ᶠ⟨ θ ⟩ c₂
    where open import CG.Types
          open import CG.Syntax
          open import CG.Semantics

  -- Thunk semantics (also figure 3.4)
  figure-3·3ᵇ : Set
  figure-3·3ᵇ = ∀ {Γ τ θ} {c₁ : TConf Γ (LIO τ)} {c₂ : FConf τ} → c₁ ⇓⟨ θ ⟩ c₂
    where open import CG.Types
          open import CG.Syntax
          open import CG.Semantics

  open import CG hiding (_×_ ; _⊆_)

  -- "The final value of the program counter is at least as sensitive
  -- as the intial value." for thunk semantics
  property-6 : ∀ {Γ τ Σ Σ' μ μ' pc pc' v} {θ : Env Γ} {t : Thunk Γ (LIO τ)} →
                    ⟨ Σ , μ , pc , t ⟩ ⇓⟨ θ ⟩ ⟨ Σ' , μ' , pc' , v ⟩ →
                    pc ⊑ pc'
  property-6 = step-⊑

  -- Same for forcing semantics.
  property-6′ : ∀ {Γ τ Σ Σ' μ μ' pc pc' v} {θ : Env Γ} {e : Expr Γ (LIO τ)} →
                    ⟨ Σ , μ , pc , e ⟩ ⇓ᶠ⟨ θ ⟩ ⟨ Σ' , μ' , pc' , v ⟩ →
                    pc ⊑ pc'
  property-6′ = stepᶠ-⊑

  -- L-equivalence
  figure-3·5 : Set
  figure-3·5  = ∀ {τ β} {v₁ v₂ : Value τ} → v₁ ≈⟨ β ⟩ⱽ v₂
    where open import CG.LowEq L

  -- Valid inputs judgment
  figure-3·7 : Set₁
  figure-3·7 = ∀ {F} {Γ} {τ} {c : Conf F Γ τ} {θ : Env Γ} → Valid-Inputs c θ

  -- Valid outputs judgment
  figure-3·7' : Set
  figure-3·7' = ∀ {τ} {c : FConf τ} → Valid-Outputs c

  -- Valid invariant (pure semantics)
  property-7 : ∀ {τ Γ n} {e : Expr Γ τ} {θ : Env Γ} {v : Value τ} →
               e ⇓ᴾ⟨ θ ⟩ v →
               Validᴱ n θ →
               Validⱽ n v
  property-7 = validⱽ-⇓ᴾ

  -- Valid invariant (forcing semantics)
  property-7' : ∀ {τ Γ} {θ : Env Γ} {c : EConf Γ (LIO τ)} {c' : FConf τ} →
                c ⇓ᶠ⟨ θ ⟩ c' →
                let ⟨ Σ' , μ' , _  , v ⟩ = c' in
                Valid-Inputs c θ →
                Valid-Outputs c'
  property-7' = validᴼ-⇓ᶠ

  open import CG.LowEq L

  -- Store and heap confinement (forcing semantics)
  lemma-3·5 : ∀ {τ Γ θ} {c : EConf Γ (LIO τ)} {c' : FConf τ} →
               let ⟨ Σ , μ , pc , e ⟩ = c
                   ⟨ Σ' , μ' , _ , _ ⟩ = c' in
               {{validᴾ : Validᴾ ⟨ Σ , μ ⟩ }} {{validᴱ : Validᴱ ∥ μ ∥ᴴ θ}} →
               c ⇓ᶠ⟨ θ ⟩ c' →
               pc ⋤ L →
               ⟨ Σ , μ ⟩ ≈⟨ ι ∥ μ ∥ᴴ ⟩ᴾ ⟨ Σ' , μ' ⟩
  lemma-3·5 = stepᶠ-≈ᴾ
    where open import CG.Security L

  open import Data.Product renaming (_,_ to _∧_)

  -- L-equivalence preservation in secret contexts
  lemma-3·6 : ∀ {τ Γ₁ Γ₂ θ₁ θ₂ β} {c₁ : TConf Γ₁ (LIO τ)} {c₂ : TConf Γ₂ (LIO τ)} {c₁' c₂' : FConf τ} →
           let ⟨ Σ₁ , μ₁ , pc₁ , t₁ ⟩ = c₁
               ⟨ Σ₂ , μ₂ , pc₂ , t₂ ⟩ = c₂ in
             {{valid₁ : Valid-Inputs c₁ θ₁}} {{valid₂ : Valid-Inputs c₂ θ₂}} →
           c₁ ⇓⟨ θ₁ ⟩ c₁' →
           c₂ ⇓⟨ θ₂ ⟩ c₂' →
           ⟨ Σ₁ , μ₁ ⟩ ≈⟨ β ⟩ᴾ ⟨ Σ₂ , μ₂ ⟩ →
           pc₁ ⋤ L →
           pc₂ ⋤ L →
           ∃ (λ β' → β ⊆ β' × c₁' ≈⟨ β' ⟩ᶜ c₂')
  lemma-3·6 = tiniᴴ
    where open import CG.Security L

  -- L-equivalence preservation (pure semantics)
  lemma-3·7 : ∀ {τ Γ θ₁ θ₂ v₁ v₂ β} {e : Expr Γ τ} →
         e ⇓ᴾ⟨ θ₁ ⟩ v₁ →
         e ⇓ᴾ⟨ θ₂ ⟩ v₂ →
         θ₁ ≈⟨ β ⟩ᴱ θ₂ →
         v₁ ≈⟨ β ⟩ⱽ v₂
  lemma-3·7 = tiniᴾ
    where open import CG.Security L

  -- L-equivalence preservation in public contexts
  lemma-3·8 : ∀ {pc τ Γ Σ₁ Σ₂ μ₁ μ₂ θ₁ θ₂ β} {t : Thunk Γ (LIO τ)} {c₁' c₂' : FConf τ} →
                    let c₁ = ⟨ Σ₁ , μ₁ , pc , t ⟩
                        c₂ = ⟨ Σ₂ , μ₂ , pc , t ⟩ in
                   {{valid₁ : Valid-Inputs c₁ θ₁}} {{valid₂ : Valid-Inputs c₂ θ₂}} →
                      c₁ ⇓⟨ θ₁ ⟩ c₁' →
                      c₂ ⇓⟨ θ₂ ⟩ c₂' →
                      ⟨ Σ₁ , μ₁ ⟩ ≈⟨ β ⟩ᴾ ⟨ Σ₂ , μ₂ ⟩ →
                      θ₁ ≈⟨ β ⟩ᴱ θ₂ →
                      pc ⊑ L →
                      ∃ (λ β' → β ⊆ β' × c₁' ≈⟨ β' ⟩ᶜ c₂')
  lemma-3·8 = tiniᴸ
    where open import CG.Security L

  open import Generic.Calculus

  -- λ^CG TINI
  theorem-4 : TINI λ^CG
  theorem-4 {A = A} valid₁ valid₂ = tiniᶠ {{valid₁}} {{valid₂}}
    where open import CG.Security A

--------------------------------------------------------------------------------
-- §5. Translation from λ^FG to λ^CG
--------------------------------------------------------------------------------
module §5 where

  open import FG2CG
  open import FG as FG
  open import CG as CG
  open import FG2CG.Syntax
  open import FG2CG.Correct

  -- Type translation
  figure-5·1ᵃ : FG.Ty → CG.Ty
  figure-5·1ᵃ = ⟪_⟫ᵗ

  -- Value translation.
  figure-5·1ᵇ : ∀ {τ} → FG.Value τ → CG.Value ⟪ τ ⟫ᵗ
  figure-5·1ᵇ = ⟪_⟫ⱽ

  -- Expression translation (also Figure 5.4) and type preservation (lemma 5.1)
  figure-5·2 : ∀ {Γ τ} → FG.Expr Γ τ → CG.Thunk ⟪ Γ ⟫ᶜ (LIO ⟪ τ ⟫ᵗ)
  figure-5·2 = ⟪_⟫ᵀ

  -- Semantics Preservation.
  theorem-5 : ∀ {Σ Σ' μ μ' Γ τ pc} {e : FG.Expr Γ τ} {v : FG.Value τ} {θ : FG.Env Γ} →
             ⟨ Σ , μ , e ⟩ ⇓⟨ θ , pc ⟩ ⟨ Σ' , μ' , v ⟩ →
             ⟨ ⟪ Σ ⟫ˢ , ⟪ μ ⟫ᴴ ,  pc , ⟪ e ⟫ᴱ ⟩ ⇓ᶠ⟨ ⟪ θ ⟫ᵉ ⟩  ⟨ ⟪ Σ' ⟫ˢ , ⟪ μ' ⟫ᴴ , pc , ⟪ v ⟫ⱽ ⟩
  theorem-5 = fg2cgᶠ

  open import Function.Equivalence
  open import FG2CG.Recovery L

  -- Lifting and unlifting L-equivalence of initial configurations and
  -- all syntactic categories.
  lemma-5·2 : ∀ {Γ τ β} {c₁ c₂ : FG.IConf Γ τ} pc →
              c₁ FG.≈ᴵ⟨ L , β ⟩ c₂ ⇔ (⟪ c₁ ⟫ᴵ pc) CG.≈ᴵ⟨ L , β ⟩ (⟪ c₂ ⟫ᴵ pc)
  lemma-5·2 pc = equivalence (lift-≈ᴵ pc) (unlift-≈ᴵ pc)

  -- Back-translation of L-equivalence from target to source for final
  -- configurations with public program counter.
  lemma-5·3 : ∀ {τ pc β} {c₁ c₂ : FG.FConf τ} →
                     let ⟨ Σ₁ , μ₁ , r₁ ^ ℓ₁ ⟩ = c₁
                         ⟨ Σ₂ , μ₂ , r₂ ^ ℓ₂ ⟩ = c₂ in
                     pc ⊑ ℓ₁ →
                     pc ⊑ ℓ₂ →
                     (⟪ c₁ ⟫ᶠ pc) CG.≈ᶜ⟨ L , β ⟩ (⟪ c₂ ⟫ᶠ pc) →
                     c₁ FG.≈ᶜ⟨ L , β ⟩ c₂
  lemma-5·3 = unlift-≈ᶜ

  -- ⟪·⟫ preserves validity
  lemma-5·4 : ∀ {τ Γ} pc (c : FG.IConf Γ τ) (θ : FG.Env Γ) →
                 FG.Valid-Inputs c θ → CG.Valid-Inputs (⟪ c ⟫ᴵ pc) ⟪ θ ⟫ᵉ
  lemma-5·4 = lift-Valid-Inputs

  open import Generic.Calculus
  open import Relation.Binary.PropositionalEquality
  open import Data.Product renaming (_,_ to _∧_)

  -- Recovery of λ^FG TINI via ⟪·⟫
  theorem-6 : TINI λ^FG
  theorem-6 {A = A} valid₁ valid₂ c₁⇓ c₂⇓ c₁≈c₂ (θ₁≈θ₂ ∧ refl)
    = R.tini-via-cg {{valid₁}} {{valid₂}} c₁⇓ c₂⇓ c₁≈c₂ θ₁≈θ₂
    where open import FG2CG.Recovery A as R

--------------------------------------------------------------------------------
-- §6. Translation from λ^CG to λ^FG
--------------------------------------------------------------------------------
module §6 where

  open import CG2FG
  open import FG as FG hiding (_×_)
  open import CG as CG hiding (_×_)
  open import CG2FG.Syntax
  open import CG2FG.Correct
  open import Data.Product as P using (_×_ ; ∃ ; uncurry) renaming (_,_ to _∧_)

  -- Type translation
  figure-6·1ᵃ : CG.Ty → FG.Ty
  figure-6·1ᵃ = ⟦_⟧ᵗ

  -- Value translation.
  figure-6·1ᵇ : ∀ {τ} → CG.Value τ → Label → FG.Value ⟦ τ ⟧ᵗ
  figure-6·1ᵇ = ⟦_⟧ⱽ

  -- Expression translation and type preservation (lemma 5.1)
  figure-6·2ᵃ : ∀ {Γ τ} (e : CG.Expr Γ τ) → FG.Expr ⟦ Γ ⟧ᶜ ⟦ τ ⟧ᵗ
  figure-6·2ᵃ = ⟦_⟧ᴱ

  -- Thunk translation (also figure 6.3).
  figure-6·2ᵇ : ∀ {Γ τ} (t : CG.Thunk Γ (LIO τ)) → FG.Expr ⟦ Γ ⟧ᶜ ⟦ τ ⟧ᵗ
  figure-6·2ᵇ = ⟦_⟧ᵀ

  open import CG2FG.CrossEq

  -- Cross-language semantics equivalence up to extra annotations.
  figure-6·4 : ∀ {τ} → FG.Value ⟦ τ ⟧ᵗ → Label → CG.Value τ → Set
  figure-6·4 v₁ pc v₂ = v₁ ↓≈⟨ pc ⟩ⱽ v₂
    where open import CG2FG.Graph

  open import Function.Equivalence

  -- Equivalence of configurations.
  definition-4 : ∀ {Γ τ Σ₁ Σ₂ μ₁ μ₂ pc} {e : CG.Expr Γ (LIO τ)} →
                  ⟨ Σ₁ , μ₁ , ⟦ e ⟧ᴱ FG.∘ Id （） ⟩ ↓≈ᴵ ⟨ Σ₂ , μ₂ , pc , e ⟩ ⇔ FG.⟨ Σ₁ , μ₁ ⟩ ↓≈ᴾ CG.⟨ Σ₂ , μ₂ ⟩
  definition-4 = equivalence ⌜_⌝ᴵ ⌞_⌟ᴵ

  definition-4′ : ∀ {Γ τ Σ₁ Σ₂ μ₁ μ₂ pc} {t : CG.Thunk Γ (LIO τ)} →
                   ⟨ Σ₁ , μ₁ , ⟦ t ⟧ᵀ ⟩ ↓≈ᵀ ⟨ Σ₂ , μ₂ , pc , t ⟩ ⇔ FG.⟨ Σ₁ , μ₁ ⟩ ↓≈ᴾ CG.⟨ Σ₂ , μ₂ ⟩
  definition-4′ = equivalence ⌜_⌝ᵀ ⌞_⌟ᵀ

  definition-4′′ : ∀ {τ Σ₁ Σ₂ μ₁ μ₂ pc} {v : CG.Value τ} {r : FG.Raw ⟦ τ ⟧ᵗ} →
                    ⟨ Σ₁ , μ₁ , r ^ pc ⟩ ↓≈ᶜ ⟨ Σ₂ , μ₂ , pc , v ⟩ ⇔ (FG.⟨ Σ₁ , μ₁ ⟩ ↓≈ᴾ CG.⟨ Σ₂ , μ₂ ⟩ × (r ↓≈⟨ pc ⟩ᴿ v))
  definition-4′′ = equivalence ( λ { ⟨ ≈ᴾ , r≈v ⟩ → ≈ᴾ ∧ ⌞ r≈v ⌟ᴿ }) (uncurry ⟨_,_⟩)

  -- Reflexivity of ↓≈
  property-8 : ∀ {Γ τ} (c : CG.EConf Γ (LIO τ)) → ⟦ c ⟧ᴵ ↓≈ᴵ c
  property-8 c = refl-≈ᴵ c

  open import Function

  -- Weakening of ↓≈
  property-9 :  ∀ {τ pc pc'} {r₁ : FG.Raw ⟦ τ ⟧ᵗ} {v₂ : CG.Value τ} →
                  pc ⊑ pc' →
                  r₁ ↓≈⟨ pc ⟩ᴿ v₂ →
                  r₁ ↓≈⟨ pc' ⟩ᴿ v₂
  property-9 = flip ≈ᴿ-⊑

  property-9′ :  ∀ {τ pc pc'} {v₁ : FG.Value ⟦ τ ⟧ᵗ} {v₂ : CG.Value τ} →
                  pc ⊑ pc' →
                  v₁ ↓≈⟨ pc ⟩ⱽ v₂ →
                  v₁ ↓≈⟨ pc' ⟩ⱽ v₂
  property-9′ = flip ≈ⱽ-⊑

  property-9′′ :  ∀ {Γ pc pc'} {θ₁ : FG.Env ⟦ Γ ⟧ᶜ} {θ₂ : CG.Env Γ} →
                  pc ⊑ pc' →
                  θ₁ ↓≈⟨ pc ⟩ᵉ θ₂ →
                  θ₁ ↓≈⟨ pc' ⟩ᵉ θ₂
  property-9′′ = flip ≈ᵉ-⊑

  -- ⟦·⟧ preserves pure semantics.
  lemma-6·2 : ∀ {Γ τ Σ μ pc} {θ : CG.Env Γ} {θ' : FG.Env ⟦ Γ ⟧ᶜ} {e : CG.Expr Γ τ} {v : CG.Value τ} →
                θ' ↓≈⟨ pc ⟩ᵉ θ →
                e ⇓ᴾ⟨ θ ⟩ v →
                ∃ (λ r → (r ↓≈⟨ pc ⟩ᴿ v) × (⟨ Σ , μ , ⟦ e ⟧ᴱ ⟩ ⇓⟨ θ' , pc ⟩ ⟨ Σ , μ , r ^ pc ⟩))
  lemma-6·2 = cg2fgᴾ _ _

  -- ⟦·⟧ preserves forcing semantics.
  theorem-7 : ∀ {Γ τ θ₁ c₂' c₁} {θ₂ : CG.Env Γ} {c₂ : EConf Γ (LIO τ)} →
                let ⟨ Σ , μ , pc , t ⟩ = c₂ in
                    θ₁ ↓≈⟨ pc ⟩ᵉ θ₂ →
                    c₁ ↓≈ᴵ c₂ →
                    c₂ ⇓ᶠ⟨ θ₂ ⟩ c₂' →
                    ∃ (λ c₁' → c₁' ↓≈ᶜ c₂' × c₁ ⇓⟨ θ₁ , pc ⟩ c₁' )
  theorem-7 = cg2fgᶠ

  -- ⟦·⟧ preserves thunk semantics.
  theorem-7′ : ∀ {Γ τ θ₁ c₂' c₁} {θ₂ : CG.Env Γ} {c₂ : CG.TConf Γ (LIO τ)} →
               let ⟨ Σ , μ , pc , e ⟩ = c₂ in
                   θ₁ ↓≈⟨ pc ⟩ᵉ θ₂ →
                   c₁ ↓≈ᵀ c₂ →
                   c₂ ⇓⟨ θ₂ ⟩ c₂' →
                   ∃ (λ c₁' → c₁' ↓≈ᶜ c₂' × c₁ ⇓⟨ θ₁ , pc ⟩ c₁' )
  theorem-7′ = cg2fg


  -- Correctness ⟦·⟧
  corollary-1 : ∀ {τ Γ c₂'} {θ : CG.Env Γ} {c₂ : CG.EConf Γ (LIO τ)} →
                let ⟨ Σ , μ , pc , e ⟩ = c₂ in
                c₂ ⇓ᶠ⟨ θ ⟩ c₂' →
                ∃ (λ c₁' → c₁' ↓≈ᶜ c₂' × ⟦ c₂ ⟧ᴵ ⇓⟨ ⟦ θ ⟧ᵉ pc  , pc ⟩ c₁' )
  corollary-1 = ⟦·⟧-correct

  open import CG2FG.Recovery L

  -- Lifting L-equivalence from source to target.
  lemma-6·3 : ∀ {Γ τ β} {c₁ c₂ : CG.EConf Γ (LIO τ)} →
                  c₁ CG.≈ᴵ⟨ L , β ⟩ c₂ →
                  ⟦ c₁ ⟧ᴵ FG.≈ᴵ⟨ L , β ⟩ ⟦ c₂ ⟧ᴵ
  lemma-6·3 = lift-≈ᴵ

  -- Unlifting L-equivalence from target to source
  lemma-6·4 : ∀ {pc τ β} {v₁ v₂ : FG.Value ⟦ τ ⟧ᵗ} {v₁' v₂' : CG.Value τ} →
                  pc ⊑ L →
                  v₁ FG.≈ⱽ⟨ L , β ⟩ v₂ →
                  v₁ ↓≈⟨ pc ⟩ⱽ v₁'  →
                  v₂ ↓≈⟨ pc ⟩ⱽ v₂'  →
                  v₁' CG.≈ⱽ⟨ L , β ⟩ v₂'
  lemma-6·4 = unlift-≈ⱽ

  lemma-6·4′ : ∀ {pc τ β} {r₁ r₂ : FG.Raw ⟦ τ ⟧ᵗ} {v₁' v₂' : CG.Value τ} →
                  pc ⊑ L →
                  r₁ FG.≈ᴿ⟨ L , β ⟩ r₂ →
                  r₁ ↓≈⟨ pc ⟩ᴿ v₁'  →
                  r₂ ↓≈⟨ pc ⟩ᴿ v₂'  →
                  v₁' CG.≈ⱽ⟨ L , β ⟩ v₂'
  lemma-6·4′ = unlift-≈ᴿ

  lemma-6·4′′ : ∀ {pc Γ β} {θ₁ θ₂ : FG.Env ⟦ Γ ⟧ᶜ} {θ₁' θ₂' : CG.Env Γ} →
                  pc ⊑ L →
                  θ₁ FG.≈ᴱ⟨ L , β ⟩ θ₂ →
                  θ₁ ↓≈⟨ pc ⟩ᵉ θ₁'  →
                  θ₂ ↓≈⟨ pc ⟩ᵉ θ₂'  →
                  θ₁' CG.≈ᴱ⟨ L , β ⟩ θ₂'
  lemma-6·4′′ = unlift-≈ᴱ

  lemma-6·5 : ∀ {ℓ β} {M₁' M₂'} {M₁ M₂ : FG.Memory ℓ} →
                 M₁ FG.≈ᴹ⟨ L , β ⟩ M₂ →
                 M₁ ↓≈ᴹ M₁' →
                 M₂ ↓≈ᴹ M₂' →
                 M₁' CG.≈ᴹ⟨ L , β ⟩ M₂'
  lemma-6·5 = unlift-≈⟨ _ ⟩ᴹ

  lemma-6·5′  : ∀ {Σ₁ Σ₂ Σ₁' Σ₂' β} →
                  Σ₁ FG.≈ˢ⟨ L , β ⟩ Σ₂ →
                  Σ₁ ↓≈ˢ Σ₁' →
                  Σ₂ ↓≈ˢ Σ₂' →
                  Σ₁' CG.≈ˢ⟨ L , β ⟩ Σ₂'
  lemma-6·5′ = unlift-≈ˢ

  lemma-6·5′′  : ∀ {μ₁ μ₂ μ₁' μ₂' β} →
                  μ₁ FG.≈ᴴ⟨ L , β ⟩ μ₂ →
                  μ₁ ↓≈ᴴ μ₁' →
                  μ₂ ↓≈ᴴ μ₂' →
                  μ₁' CG.≈ᴴ⟨ L , β ⟩ μ₂'
  lemma-6·5′′ = unlift-≈ᴴ

  lemma-6·6 : ∀ {τ τ' β} {c₁' c₂' : CG.FConf τ} {c₁ c₂ : FG.FConf τ'} →
              c₁ FG.≈ᶜ⟨ L , β ⟩ c₂ →
              c₁ ↓≈ᶜ c₁' →
              c₂ ↓≈ᶜ c₂' →
              c₁' CG.≈ᶜ⟨ L , β ⟩ c₂'
  lemma-6·6 = unlift-≈ᶜ

  -- ⟦ · ⟧ preserves validity
  lemma-6·7 : ∀ {τ Γ} (c : CG.EConf Γ (LIO τ)) (θ : CG.Env Γ) →
                CG.Valid-Inputs c θ →
                FG.Valid-Inputs ⟦ c ⟧ᴵ (⟦ θ ⟧ᵉ (CG.Conf.pc c))
  lemma-6·7 = lift-Valid-Inputs

  open import Generic.Calculus

  -- Recovery of λ^CG TINI via ⟦·⟧
  theorem-8 : TINI λ^CG
  theorem-8 {A = A} valid₁ valid₂ = R.tini-via-fg {{ valid₁ }} {{ valid₂ }}
    where open import CG2FG.Recovery A as R
