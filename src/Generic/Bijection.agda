{-# OPTIONS --allow-unsolved-metas #-}

module Generic.Bijection where

open import Data.Empty
open import Data.Fin hiding (_≤?_ ; _≤_ ; _<_ ; #_)
open import Data.Maybe as M
open import Data.Nat renaming (_+_ to _+ᴺ_)
open import Data.Nat.Properties hiding (suc-injective)
open import Data.Product
open import Generic.Partial.Bijection public
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

--------------------------------------------------------------------------------

suc-injective : ∀ {n} {x y : Fin n} → _≡_ {A = Fin (suc n)} (suc x) (suc y) → x ≡ y
suc-injective refl = refl

-- Bijection for heap addresses.  It restricts the domain and codomain
-- using the Fin type (Fin n contains addresses from 0 to n - 1).
-- This is useful to avoid partial bijections (for which the agda
-- library provides no support) and carrying extra assumptions about
-- domain and codomain.
Bij : Set
Bij = ℕ ⤖ᴾ ℕ
  -- dom : ℕ
  -- rng : ℕ
  -- ∈-dom : ∀ {n} → n ≤ dom → ?
  -- ∈-dom : ∀ {n} → n ≤ dom → ?

-- ι-≡ : ∀ {x y} → (x , y) ∈ᵗ ι → x ≡ y
-- ι-≡ refl = refl

-- ι n is the identity bijection over the domain {0, ... n-1}
ι : ℕ → Bij
ι n = bijᴾ idᴾ idᴾ (inv , inv)
  where open Id n

ι-∈ : ∀ {m n} → m < n → (m , m) ∈ᵗ (ι n)
ι-∈ {m} {n} m<n with m <? n
ι-∈ {m} {n} m<n | yes _ = refl
ι-∈ {m} {n} m<n | no m≮n = ⊥-elim (m≮n m<n)

ι-≡ : ∀ {a b c} → (a , b) ∈ᵗ (ι c) → a ≡ b
ι-≡ {c = c} = idᴾ-≡
  where open Id c

ι-≤ᴰ : ∀ {a b c} → (a , b) ∈ᵗ (ι c) → a < c
ι-≤ᴰ {c = c} = idᴾ-<ᴰ
  where open Id c

--------------------------------------------------------------------------------
-- Manipulations and lemmas for the Fin typesx

-- instance
--   _≟ᶠ_ : ∀ {n} → (x y : Fin n) → Dec (x ≡ y)
--   zero ≟ᶠ zero = yes refl
--   zero ≟ᶠ suc y = no (λ ())
--   suc x ≟ᶠ zero = no (λ ())
--   suc x ≟ᶠ suc y with x  ≟ᶠ y
--   suc x ≟ᶠ suc .x | yes refl = yes refl
--   suc x ≟ᶠ suc y | no ¬p = no λ { refl → ¬p refl }

-- reduce₁ : ∀ {n} (x : Fin (suc n)) → toℕ x < n → Fin n
-- reduce₁ zero (s≤s x<n) = zero
-- reduce₁ (suc x) (s≤s x<n) = suc (reduce₁ x x<n)

-- inj∘red-≡-id : ∀ {n} (x : Fin (suc n)) (x<n : toℕ x < n) → inject₁ (reduce₁ x x<n) ≡ x
-- inj∘red-≡-id zero (s≤s x<n) = refl
-- inj∘red-≡-id (suc x) (s≤s x<n) = cong suc (inj∘red-≡-id x x<n)

-- red∘inj-≡-id : ∀ {n} (x : Fin n) (x<n : toℕ (inject₁ x) < n) → reduce₁ (inject₁ x) x<n ≡ x
-- red∘inj-≡-id zero (s≤s z≤n) = refl
-- red∘inj-≡-id (suc x) (s≤s x<n) = cong suc (red∘inj-≡-id x x<n)

-- toℕ-inject₁-≡ : ∀ {n} (x : Fin n) → toℕ x ≡ toℕ (inject₁ x)
-- toℕ-inject₁-≡ zero = refl
-- toℕ-inject₁-≡ (suc x) = cong suc (toℕ-inject₁-≡ x)

-- fin-< : ∀ {n} (x : Fin n) → toℕ x < n
-- fin-< zero = s≤s z≤n
-- fin-< (suc x) = s≤s (fin-< x)

irr-< : ∀ {n m} → (p q : n < m) → p ≡ q
irr-< (s≤s z≤n) (s≤s z≤n) = refl
irr-< (s≤s (s≤s p)) (s≤s (s≤s q)) = cong s≤s (irr-< (s≤s p) (s≤s q))

--------------------------------------------------------------------------------

-- Extends the codomain with one more address
-- _↑ᴿ  : ∀ {n m} → Bij n m → Bij n (suc m)
-- _↑ᴿ {n} {m} β = record { to = to¹ ; from = from¹ ; inverse-of = left , right }
--   where open Bijectionᴾ β
--         open import Function as F

--         to¹ : Fin n ⇀ Fin (suc m)
--         to¹ = M.map inject₁ F.∘ to

--         from¹ : Fin (suc m) ⇀ Fin n
--         from¹ y with (toℕ y) <? m
--         from¹ y | yes p = from (reduce₁ y p)
--         from¹ y | no ¬p = nothing

--         -- Definition of from¹ after the bounds test.
--         def-from¹ : ∀ {y} (y<m : toℕ y < m) → from¹ y ≡ from (reduce₁ y y<m)
--         def-from¹ {y} y<m with toℕ y <? m
--         def-from¹ {y} y<m | yes y<m' rewrite equal-< y<m y<m' = refl
--         def-from¹ {y} y<m | no y≮m = ⊥-elim (y≮m y<m)

--         -- If (x , y) belong to the extended bijection, then y can be
--         -- reduced and x and reduced y are in the original bijection. (case "to")
--         ∈¹-∈-to : ∀ {x y} (y<m : toℕ y < m) → (x , y) ∈ to¹ → (x , reduce₁ y y<m) ∈ to
--         ∈¹-∈-to {x} {y} y<m xy∈t¹ with to x
--         ∈¹-∈-to {x} {y} y<m () | nothing
--         ∈¹-∈-to {x} {y} y<m xy∈t¹ | just y'
--           rewrite sym (just-injective xy∈t¹) |
--                   toℕ-inject₁-≡ y' | red∘inj-≡-id y' y<m = refl

--         -- If (x , y) belong to the extended bijection, then y can be
--         -- reduced and x and reduced y are in the original bijection. (case "from")
--         ∈¹-∈-from : ∀ {x y} (y<m : toℕ y < m) → (y , x) ∈ from¹ → (reduce₁ y y<m , x ) ∈ from
--         ∈¹-∈-from {x} {y} y<m yx∈f with toℕ y <? m
--         ∈¹-∈-from {x} {y} y<m yx∈f | yes y<m' rewrite equal-< y<m y<m' = yx∈f
--         ∈¹-∈-from {x} {y} y<m yx∈f | no y≮m = ⊥-elim (y≮m y<m)

--         -- Fact about the domain (D) of from
--         from-<ᴰ : ∀ {y x} → (y , x) ∈ from¹ → toℕ y < m
--         from-<ᴰ {y} yx∈f with toℕ y <? m
--         from-<ᴰ {y} yx∈f | yes p = p
--         from-<ᴰ {y} () | no ¬p

--         -- Fact about the range (R) of to
--         to-<ᴿ : ∀ {x y} → (x , y) ∈ to¹ → toℕ y < m
--         to-<ᴿ {x} {y} xy∈t with to x
--         to-<ᴿ {x} {y} xy∈t | just y' with fin-< y'
--         ... | y<m rewrite sym (just-injective xy∈t) | toℕ-inject₁-≡ y' = y<m
--         to-<ᴿ {x} {y} () | nothing

--         -- Left inverse
--         left : ∀ {x y} → (y , x) ∈ from¹ → (x , y) ∈ to¹
--         left {x} {y} yx∈f =
--           let  y<m = from-<ᴰ yx∈f
--                xy∈t = left-inverse-of (∈¹-∈-from y<m yx∈f) in
--           to¹ x ≡⟨ refl ⟩
--           M.map inject₁ (to x) ≡⟨ cong (M.map inject₁) xy∈t ⟩
--           just (inject₁ (reduce₁ y y<m)) ≡⟨ cong just (inj∘red-≡-id y y<m) ⟩
--           just y ∎
--           where open ≡-Reasoning

--         -- Right inverse
--         right : ∀ {x y} → (x , y) ∈ to¹ → (y , x) ∈ from¹
--         right {x} {y} xy∈t =
--           let y<m = to-<ᴿ xy∈t
--               xy∈f = right-inverse-of (∈¹-∈-to y<m xy∈t) in
--           from¹ y ≡⟨ def-from¹ y<m ⟩
--           from (reduce₁ y y<m) ≡⟨ xy∈f ⟩
--           just x ∎
--           where open ≡-Reasoning

-- -- Extends the domain with one more address
-- _↑ᴰ  : ∀ {n m} → Bij n m → Bij (suc n) m
-- β ↑ᴰ =  ((β ⁻¹) ↑ᴿ) ⁻¹

-- -- Extend both the domain and the codomain
-- _↑ : ∀ {n m} → Bij n m → Bij (suc n) (suc m)
-- β ↑ = (β ↑ᴿ) ↑ᴰ


-- ↑ᴿ-∈ : ∀ {n m} {β : Bij n m} {x y} → (x , y) ∈ᵗ (β ↑ᴿ) → Σ (toℕ y < m) (λ y<m → (x , reduce₁ y y<m) ∈ᵗ β)
-- ↑ᴿ-∈ {β = β} {x} xy∈βᴿ with Bijectionᴾ.to (β ↑ᴿ) x | inspect (Bijectionᴾ.to (β ↑ᴿ)) x
-- ↑ᴿ-∈ {β = β} {x} xy∈βᴿ | just y' | [ eq ] with Bijectionᴾ.to β x
-- ↑ᴿ-∈ {β = β} {x} {y} xy∈βᴿ | just y' | [ eq ] | just y'' with fin-< y''
-- ... | y<m rewrite just-injective (sym xy∈βᴿ) | just-injective (sym eq)
--     | toℕ-inject₁-≡ y'' | red∘inj-≡-id y'' y<m = y<m , (cong just (sym (red∘inj-≡-id y'' y<m)))
-- ↑ᴿ-∈ {β = β} {x} xy∈βᴿ | just y' | [ () ] | nothing
-- ↑ᴿ-∈ {β = β} {x} () | nothing | w

--------------------------------------------------------------------------------
-- Equivalence class up to bijection.

-- Relᴮ : {Ty : Set} → (Ty → Set) → Set₁
-- Relᴮ V = ∀ {n m τ} → V τ → Bij n m → V τ → Set

-- I could define Rel : ∀ x y → Bij (Dom x) (Dom y), however this is
-- to restrictive. Definitions for values typically require at least
-- (Dom x) but that is too restrictive when values contain composite
-- values with different domains.
-- record IsEquivalenceᴮ {Ty : Set} {V : Ty → Set} (R : Relᴮ V) : Set where
--   field Dom : ∀ {τ} → V τ → ℕ
--         reflᴮ : ∀ {τ} {x : V τ} → R x (ι′ (Dom x)) x
--         symᴮ : ∀ {τ} {x y : V τ} {n m} {β : Bij n m} → R x β y → R y (β ⁻¹) x
--         transᴮ : ∀ {τ} {x y z : V τ} {n₁ n₂ n₃} {β₁ : Bij n₁ n₂} {β₂ : Bij n₂ n₃} →
--                    R x β₁ y → R y β₂ z → R x (β₂ ∘ β₁) z


--------------------------------------------------------------------------------
-- version without indexes
-- Relᴮ : Set → Set₁
-- Relᴮ A = A → Bij → A → Set

-- Wkenᴮ : {A : Set} (R : Relᴮ A) → Set
-- Wkenᴮ R = ∀ {n m x} → n ≤ m → R x (ι n) x → R x (ι m) x

-- Reflexiveᴮ : {A : Set} (R : Relᴮ A) (Dom : A → ℕ) → Set
-- Reflexiveᴮ R Dom = ∀ {x} → R x (ι (Dom x)) x

-- Symmetricᴮ : {A : Set} (R : Relᴮ A) → Set
-- Symmetricᴮ R =  ∀ {x y β} → R x β y → R y (β ⁻¹) x

-- Transitiveᴮ : {A : Set} (R : Relᴮ A) → Set
-- Transitiveᴮ R = ∀ {x y z β₁ β₂} → R x β₁ y → R y β₂ z → R x (β₂ ∘ β₁) z

-- record IsEquivalenceᴮ {A : Set} (R : Relᴮ A) : Set where
--   field Dom : A → ℕ
--         wkenᴮ : Wkenᴮ R
--         reflᴮ : Reflexiveᴮ R Dom
--         symᴮ : Symmetricᴮ R
--         transᴮ : Transitiveᴮ R

--------------------------------------------------------------------------------
-- Explicitly indexed

Relᴮ : {A : Set} → (A → Set) → Set₁
Relᴮ F = ∀ {a} → F a → Bij → F a → Set

Wkenᴮ : {A : Set} {F : A → Set} (R : Relᴮ F) → Set
Wkenᴮ {F = F}  R = ∀ {a n m} {x : F a} → n ≤ m → R x (ι n) x → R x (ι m) x

Reflexiveᴮ : {A : Set} {F : A → Set} (R : Relᴮ F) (Dom : ∀ {a} → F a → ℕ) → Set
Reflexiveᴮ {F = F} R Dom = ∀ {a} {x : F a} → R x (ι (Dom x)) x

Symmetricᴮ : {A : Set} {F : A → Set} (R : Relᴮ F) → Set
Symmetricᴮ {F = F} R =  ∀ {a β} {x y : F a} → R x β y → R y (β ⁻¹) x

Transitiveᴮ : {A : Set} {F : A → Set} (R : Relᴮ F) → Set
Transitiveᴮ {F = F} R = ∀ {a β₁ β₂} {x y z : F a} → R x β₁ y → R y β₂ z → R x (β₂ ∘ β₁) z

record IsEquivalenceᴮ {A : Set} {F : A → Set} (R : Relᴮ F) : Set where
  field Dom : ∀ {a} → F a → ℕ
        wkenᴮ : Wkenᴮ {A} {F} R
        reflᴮ : Reflexiveᴮ {A} {F} R Dom
        symᴮ : Symmetricᴮ {A} {F} R
        transᴮ : Transitiveᴮ {A} {F} R
