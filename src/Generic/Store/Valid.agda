open import Data.Nat
open import Lattice

module Generic.Store.Valid
  (Ty : Set)
  (Value : Ty → Set)
  {{𝑳 : Lattice}}
  (∥_∥ⱽ : ∀ {τ} → Value τ → ℕ) where

open import Generic.Store.Base Ty Value as S
open import Data.Unit hiding (_≤_)
open import Data.Product

∥_∥ᶜ : ∀ {τ} → Cell τ → ℕ
-- ∥ ⌞ v ⌟ᴵ ∥ᶜ = ∥ v ∥ⱽ
-- ∥ ⌞ v , ℓ ⌟ˢ ∥ᶜ = ∥ v ∥ⱽ
∥  v , ℓ  ∥ᶜ = ∥ v ∥ⱽ

Validᶜ : ∀ {τ} → Store → Cell τ → Set
Validᶜ Σ c = ∥ c ∥ᶜ ≤ ∥ Σ ∥

-- All-Valid : ℕ → Store → Set
-- All-Valid n [] = ⊤
-- All-Valid n (c ∷ Σ) = Validᶜ n c × All-Valid n Σ

Validˢ : Store → Set
Validˢ Σ = ∀ {n τ} {c : Cell τ } → n ↦ c ∈ Σ → Validᶜ Σ c

-- valid-++ˢ : ∀ {s s' τ τ'} {c : Cell τ s} {c' : Cell τ' s'} →
--             (Σ Σ' : Store) →
--             Validᶜ ∥ Σ ∥ c → All-Valid ∥ Σ' ++ˢ Σ ∥ Σ → All-Valid ∥ Σ' ++ˢ Σ ∥ {!!}
-- valid-++ˢ = {!!}

-- valid-∷ : ∀ {Σ s s' τ τ'} {c : Cell τ s} {c' : Cell τ' s'} →
--           Validᶜ ∥ Σ ∥ c →  Validᶜ ∥ c' ∷ Σ ∥ c
-- valid-∷ v = {!v!}

-- valid-get : ∀ {Σ n τ s} {c : Cell τ s} → Validˢ Σ → n ↦ c ∈ Σ → Validᶜ ∥ Σ ∥ c
-- valid-get (valid , _) Here = valid
-- valid-get (validᶜ , valid) (There x) = {!valid-get ? x!}
