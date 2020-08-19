-- {-# OPTIONS --allow-unsolved-metas #-}

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

-- TODO: remove
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

open Bijectionᴾ  -- Why?


ι-extends : ∀ {n m} → n ≤ m → (ι m) Extends (ι n)
ι-extends {n} {m} n≤m {a , b} ∈₁ with a <? m | a <? n
ι-extends {n} {m} n≤m {a , b} ∈₁ | yes p | yes p₁ = ∈₁
ι-extends {n} {m} n≤m {a , b} () | yes p | no ¬p
ι-extends {n} {m} n≤m {a , .a} refl | no ¬p | yes p = ⊥-elim (¬p (≤-trans p n≤m))
ι-extends {n} {m} n≤m {a , b} () | no ¬p | no ¬p₁

ι-⊆ : ∀ {n m} → n ≤ m → ι n ⊆ ι m
ι-⊆ n≤m = record { bij-⊆ = ι-extends n≤m }

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


-- foo : ∀ a b c x → a ≤ c → b ≤ c → x ≤ b → x ≤ c → ¬ (x ≤ a) → ⊥
-- foo .0 .0 zero .0 z≤n z≤n z≤n z≤n x≰a = ⊥-elim (x≰a z≤n)
-- foo a b (suc c) x a≤c b≤c x≤b x≤c x≰a = {!!}

-- bar : ∀ a c → a ≤ c → c ≰ a → ⊥
-- bar .0 zero z≤n c≰a = ⊥-elim (c≰a z≤n)
-- bar .0 (suc c) z≤n c≰a = bar 0 c z≤n (λ { z≤n → c≰a {!!} })
-- bar .(suc _) (suc c) (s≤s a≤c) c≰a = bar _ c a≤c (λ z → c≰a (s≤s z))

-- ι-∘-≈′ : ∀ a b c → a ≤ c → b ≤ c → (ι a ∘ ι b) ≈ ι c
-- ι-∘-≈′ a b c a≤c b≤c x with x <? c
-- ι-∘-≈′ a b c a≤c b≤c x | yes p with x <? b
-- ι-∘-≈′ a b c a≤c b≤c x | yes p | yes p₁ with x <? a
-- ι-∘-≈′ a b c a≤c b≤c x | yes p | yes p₁ | yes p₂ = refl
-- ι-∘-≈′ a b c a≤c b≤c x | yes x<c | yes x<b | no x≮a with c ≤? a
-- ι-∘-≈′ a b c a≤c b≤c x | yes x<c | yes x<b | no x≮a | yes c≤a = ⊥-elim ((x≮a (≤-trans x<c c≤a)))
-- ι-∘-≈′ a b c a≤c b≤c x | yes x<c | yes x<b | no x≮a | no c≰a = ⊥-elim (bar a c a≤c c≰a)
--  -- = ⊥-elim ((x≮a (≤-trans x<c {!!}))) -- (foo a c (suc x) a≤c p ¬p) -- (foo a c (suc x) a≤c p {!!})
-- ι-∘-≈′ a b c a≤c b≤c x | yes p | no ¬p = ⊥-elim (¬p (≤-trans p {!!})) -- ?
-- ι-∘-≈′ a b c a≤c b≤c x | no ¬p with x <? b
-- ι-∘-≈′ a b c a≤c b≤c x | no ¬p | yes p with x <? a
-- ι-∘-≈′ a b c a≤c b≤c x | no ¬p | yes p | yes p₁ = ⊥-elim (¬p (≤-trans p b≤c))
-- ι-∘-≈′ a b c a≤c b≤c x | no ¬p | yes p | no ¬p₁ = refl
-- ι-∘-≈′ a b c a≤c b≤c x | no ¬p | no ¬p₁ = refl


-- ι-∘-≈ : ∀ n m → ((ι n) ∘ (ι m)) ≈ ι (n ⊔ m)
-- ι-∘-≈ n m x with ⊔-sel n m
-- ι-∘-≈ n m x | inj₁ n≡n⊔m rewrite n≡n⊔m with x <? n | x <? m
-- ... | yes p | b = {!!}
-- ... | no ¬p | no –p' = refl
-- ... | no ¬p | yes p with m≤m⊔n m n
-- ... | m≤m⊔n rewrite ⊔-comm n m | sym n≡n⊔m | sym (⊔-assoc m m n) | ⊔-idem m = ⊥-elim (¬p (≤-trans p m≤m⊔n))
-- ι-∘-≈ n m x | inj₂ eq₂ rewrite eq₂ = {!!}


-- x with x <? (n ⊔ m) | x <? n | x <? m
-- ι-∘-≈ n m x | yes p | q | s = {!!}
-- ι-∘-≈ n m x | no ¬p | yes p | s = {!!}
-- ι-∘-≈ n m x | no ¬p | no ¬p₁ | yes p = ⊥-elim (¬p (≤-trans p {!m≤m⊔n m n!}))
-- ι-∘-≈ n m x | no ¬p | no ¬p₁ | no ¬p₂ = refl

--------------------------------------------------------------------------------
-- Equality about composition of identity bijections

ι-⊆ᴿ : ∀ {n m} → n ≤ m → ι n ⊆ᴿ ι m
ι-⊆ᴿ {n} {m} n≤m (x , ∈₁) rewrite ι-≡ ∈₁ = _ , bij-⊆ (ι-⊆ n≤m) ∈₁′
  where ∈₁′ = left-inverse-of (ι n) ∈₁

-- Absorbs the ι with the greater domain.
absorb-ι₁ : ∀ {n β} →  β ⊆ᴿ (ι n) → (ι n ∘ β) ≡ β
absorb-ι₁ {n} {β} ⊆₁ = bij-≡ (ι n ∘ β) β (funext _ _ to-ι) (funext _ _ from-ι)

  where to-ι : ∀ x → to (ι n ∘ β) x ≡ to β x
        to-ι x with to β x | inspect (to β) x
        to-ι x | just y | [ eq ] with y <? n
        to-ι x | just y | [ eq ] | yes p = refl
        to-ι x | just y | [ eq ] | no ¬p with ⊆₁ (_ , right-inverse-of β eq)
        to-ι x | just y | [ eq ] | no ¬p | _ , eq' with y <? n
        to-ι x | just y | [ eq ] | no ¬p | _ , eq' | yes p = ⊥-elim (¬p p)
        to-ι x | just y | [ eq ] | no ¬p | _ , () | no ¬p₁
        to-ι x | nothing | [ eq ] = refl


        from-ι : (x : ℕ) → from (ι n ∘ β) x ≡ from β x
        from-ι x with x <? n
        from-ι x | yes p = refl
        from-ι x | no ¬p with from β x | inspect (from β) x
        from-ι x | no ¬p | just y | [ eq ] with ⊆₁ (_ , eq)
        from-ι x | no ¬p | just y | [ eq ] | _ , eq' with x <? n
        from-ι x | no ¬p | just y | [ eq ] | _ , eq' | yes p = ⊥-elim (¬p p)
        from-ι x | no ¬p | just y | [ eq ] | _ , () | no ¬p₁
        from-ι x | no ¬p | nothing | [ eq ] = refl

absorb-ι₂ : ∀ {n β} → β ⊆ᴰ (ι n) → (β ∘ ι n) ≡ β
absorb-ι₂ {n} {β} ⊆₁ = bij-≡ (β ∘ ι n) β (funext _ _ to-ι) (funext _ _ from-ι)
  where to-ι : (x : ℕ) → to (β ∘ ι n) x ≡ to β x
        to-ι x with x <? n
        to-ι x | yes p = refl
        to-ι x | no ¬p with to β x | inspect (to β) x
        to-ι x | no ¬p | just x₁ | [ eq ] with ⊆₁ (_ , eq)
        to-ι x | no ¬p | just x₁ | [ eq ] | _ , eq' with x <? n
        to-ι x | no ¬p | just x₁ | [ eq ] | _ , eq' | yes p = ⊥-elim (¬p p)
        to-ι x | no ¬p | just x₁ | [ eq ] | _ , () | no ¬p₁
        to-ι x | no ¬p | nothing | [ eq ] = refl

        from-ι : (x : ℕ) → from (β ∘ ι n) x ≡ from β x
        from-ι x with from β x | inspect (from β) x
        from-ι x | just y | [ eq ] with y <? n
        from-ι x | just y | [ eq ] | yes p = refl
        from-ι x | just y | [ eq ] | no ¬p with ⊆₁ (_ , left-inverse-of β eq)
        from-ι x | just y | [ eq ] | no ¬p | _ , eq' with y <? n
        from-ι x | just y | [ eq ] | no ¬p | _ , eq' | yes p = ⊥-elim (¬p p)
        from-ι x | just y | [ eq ] | no ¬p | _ , () | no ¬p₁
        from-ι x | nothing | [ eq ] = refl

-- Absorbs the ι with the greater domain.
-- This seems a particular instance of the above.
absorb-ι : ∀ {n m} → m ≤ n → (ι n ∘ ι m) ≡ ι m
absorb-ι {n} {m} m≤n = absorb-ι₁ (ι-⊆ᴿ m≤n)

ι-inv : ∀ n → (ι n) ≡ (ι n)⁻¹
ι-inv n = bij-≡ _ _ refl refl

cong₃ : ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d}
        (f : A → B → C → D) {x y u v w z} → x ≡ y → u ≡ v → z ≡ w → f x u z ≡ f y v w
cong₃ f refl refl refl = refl

square-lemma : ∀ {n₁ n₂ β} → β ⊆ᴿ (ι n₂) → β ⊆ᴰ (ι n₁) → (ι n₂ ∘ β ∘ (ι n₁) ⁻¹) ≡ β
square-lemma {n₁} {n₂} {β} ⊆₁ ⊆₂ = ≡β
  where open ≡-Reasoning

        ⊆₁′ : (β ∘ ι n₁) ⊆ᴿ (ι n₂)
        ⊆₁′ {x} (_ , ∈₁) with split-∈ᶠ {β₁ = ι n₁} {β₂ = β} ∈₁
        ... | y , ∈ᴵ , ∈ᴮ = ⊆₁ (_ , ∈ᴮ)

        ≡β : (ι n₂ ∘ β ∘ (ι n₁) ⁻¹) ≡ β
        ≡β = begin
               ι n₂ ∘ β ∘ (ι n₁) ⁻¹
             ≡⟨ cong₃ (λ a b c → a ∘ b ∘ c) refl refl (ι-inv n₁) ⟩
               ι n₂ ∘ β ∘ (ι n₁)
             ≡⟨ absorb-ι₁ ⊆₁′ ⟩
               β ∘ (ι n₁)
             ≡⟨ absorb-ι₂ ⊆₂ ⟩
               β
             ∎


--------------------------------------------------------------------------------

-- Bijection-indexed equivalence relations for indexed types
module IProps (A : Set) (F : A → Set) where

  Relᴮ : Set₁
  Relᴮ = ∀ {a} → F a → Bij → F a → Set

  Wkenᴮ : Relᴮ → Set
  Wkenᴮ R = ∀ {a β β'} {x y : F a} → β ⊆ β' → R x β y → R x β' y

  Reflexiveᴮ : Relᴮ → (Dom : ∀ {a} → F a → ℕ) → Set
  Reflexiveᴮ R Dom = ∀ {a} {x : F a} → R x (ι (Dom x)) x

  Symmetricᴮ : Relᴮ → Set
  Symmetricᴮ R = ∀ {a β} {x y : F a} → R x β y → R y (β ⁻¹) x

  Transitiveᴮ : Relᴮ → Set
  Transitiveᴮ R = ∀ {a β₁ β₂} {x y z : F a} → R x β₁ y → R y β₂ z → R x (β₂ ∘ β₁) z

  record IsEquivalenceᴮ (R : Relᴮ) (Dom : ∀ {a} → F a → ℕ) : Set where
    field wkenᴮ : Wkenᴮ R
          reflᴮ : Reflexiveᴮ R Dom
          symᴮ : Symmetricᴮ R
          transᴮ : Transitiveᴮ R

  open IsEquivalenceᴮ public


-- Bijection-indexed equivalence relations for simple (not-indexed) types
module SProps (F : Set) where

  open import Data.Unit
  open IProps ⊤ (λ _ → F) public
