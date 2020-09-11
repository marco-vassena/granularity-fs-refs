open import Generic.Graph

module Generic.IGraph
  {A B : Set}
  {⟪_⟫ᴵ : A → B}
  (𝑮 : Graph ⟪_⟫ᴵ)
  where

open Graph 𝑮 renaming
  ( ⌞_⌟ to ⌞_⌟ᴵ
  ; ⌜_⌝ to ⌜_⌝ᴵ)

-- Is this ever used?
open import Relation.Binary.PropositionalEquality
open import Data.Product

record IGraph {F : A → Set} {G : B → Set}
       (⟪_⟫ : ∀ {a} → F a → G ⟪ a ⟫ᴵ) : Set₁ where
  field R : ∀ {a b} → Graph.P 𝑮 a b → F a → G b → Set
        ⌜_⌝ : ∀ {a} → (x : F a) → R ⌜ a ⌝ᴵ x ⟪ x ⟫
        ⌞_⌟ : ∀ {a} {p : P a ⟪ a ⟫ᴵ} {x : F a} {y : G ⟪ a ⟫ᴵ} → R p x y → y ≡ ⟪ x ⟫
--        ⌞_⌟ᴵ : ∀ {a b} {x : F a} {y : G b} → R x y → Graph.P 𝑮 a b

--  open Graph 𝑮 renaming public
