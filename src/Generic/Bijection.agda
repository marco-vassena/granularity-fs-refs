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

open import Relation.Binary.HeterogeneousEquality hiding (inspect ; sym ; cong ; cong₂)

-- Basic functional extensionality.
postulate funext : ∀ {A : Set} {B : Set} (f g : A → B) → (∀ x → f x ≡ g x) → f ≡ g

-- Extended to dependently typed functions with 2 arguments.
postulate funext₂ : ∀ {A B : Set} {F : A → B → Set} (f g : ∀ x y → F x y) → (∀ x y → f x y ≅ g x y) → f ≅ g


_≈ᵀ_ : Bij → Bij → Set
β₁ ≈ᵀ β₂ = ∀ x → to β₁ x ≡ to β₂ x
  where open Bijectionᴾ

_≈ᶠ_ : Bij → Bij → Set
β₁ ≈ᶠ β₂ = ∀ x → from β₁ x ≡ from β₂ x
  where open Bijectionᴾ

-- TODO: We proved this postulate below. We just need to redefine inverse-of to take
-- the indexes explicitly instead of as implicit paramters
postulate bij-≡ : ∀ (β₁ β₂ : Bij) → to β₁ ≡ to β₂ → from β₁ ≡ from β₂ → β₁ ≡ β₂

-- Move to bijection
_⊆ᴿ_ : ∀ {A B C} → A ⤖ᴾ B → B ⤖ᴾ C → Set
β₁ ⊆ᴿ β₂ = ∀ {y} → y ∈ᴿ′ β₁ → y ∈ᴰ β₂

_⊆ᴰ_ : ∀ {A B} → A ⤖ᴾ B → A ⤖ᴾ B → Set
β₁ ⊆ᴰ β₂ = ∀ {x} → x ∈ᴰ β₁ → x ∈ᴰ β₂

-- TODO: Remove, this seems unused
-- open import Generic.Partial.Function as P
-- open import Data.Sum
-- from-∈? : ∀ (n : ℕ) (β : Bij) → (n P.∈ᴰ (from β)) ⊎ n P.∉ᴰ (from β)
-- from-∈? n β with from β n
-- from-∈? n β | just x = inj₁ (just _)
-- from-∈? n β | nothing = inj₂ nothing

-- to-∈? : ∀ (n : ℕ) (β : Bij) → (n P.∈ᴰ (to β)) ⊎ n P.∉ᴰ (to β)
-- to-∈? n β with to β n
-- to-∈? n β | just x = inj₁ (just _)
-- to-∈? n β | nothing = inj₂ nothing


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
absorb-ι {n} {m} m≤n = bij-≡ (ι n ∘ ι m) (ι m) (funext _ _ (ι-∘ᵀ n m m≤n)) (funext _ _ (ι-∘ᶠ n m m≤n))
  where

        ι-∘ᵀ : ∀ n m → m ≤ n → (ι n ∘ ι m) ≈ᵀ ι m
        ι-∘ᵀ n m m≤n x with x <? m
        ι-∘ᵀ n m m≤n x | yes p with x <? n
        ι-∘ᵀ n m m≤n x | yes p | yes p₁ = refl
        ι-∘ᵀ n m m≤n x | yes x<m | no x≮n = ⊥-elim (x≮n (≤-trans x<m m≤n))
        ι-∘ᵀ n m m≤n x | no ¬p = refl

        ι-∘ᶠ : ∀ n m → m ≤ n → (ι n ∘ ι m) ≈ᶠ ι m
        ι-∘ᶠ n m m≤n x with x <? n | x <? m
        ι-∘ᶠ n m m≤n x | yes p | yes p₁ with x <? m
        ι-∘ᶠ n m m≤n x | yes p | yes p₁ | yes p₂ = refl
        ι-∘ᶠ n m m≤n x | yes x<m | yes x<n | no x≮n = ⊥-elim (x≮n x<n)
        ι-∘ᶠ n m m≤n x | yes p | no ¬p with x <? m
        ι-∘ᶠ n m m≤n x | yes p | no x≮m | yes x<m = ⊥-elim (x≮m x<m)
        ι-∘ᶠ n m m≤n x | yes p | no ¬p | no ¬p₁ = refl
        ι-∘ᶠ n m m≤n x | no x≮n | yes x<m = ⊥-elim (x≮n (≤-trans x<m m≤n))
        ι-∘ᶠ n m m≤n x | no ¬p | no ¬p₁ = refl

ι-inv : ∀ {n} → (ι n) ≡ (ι n)⁻¹
ι-inv {n} = bij-≡ _ _ refl refl

--------------------------------------------------------------------------------

-- _▻_ : Bij → (ℕ × ℕ) → Bij
-- β ▻ (x , y) = record { to = to' ; from = from' ; inverse-of = {!!} }
--   where
--         to' : ℕ ⇀ ℕ
--         to' x' with to β x'
--         to' x' | just y' = just y'
--         to' x' | nothing with x ≟ x'
--         to' x' | nothing | yes refl = just y
--         to' x' | nothing | no ¬p = nothing

--         from' : ℕ ⇀ ℕ
--         from' y' with from β y'
--         from' y' | just x' = just x'
--         from' y' | nothing with y ≟ y'
--         from' y' | nothing | yes refl = just x
--         from' y' | nothing | no ¬p = nothing

--         proof : from' InverseOfᴾ to'
--         proof = {!!} , {!!}

--         proof₁
--------------------------------------------------------------------------------
-- TODO: Adapt the definition of partial bijections to use the following
-- definition of InverseOf to avoid trouble with implicit parameters.

-- _InverseOf'_ : ℕ ⇀ ℕ → ℕ ⇀ ℕ → Set
-- _InverseOf'_ f g = ∀ x y → (x , y) ∈ f ⇔ (y , x) ∈ g

-- record Bij' : Set where
--   field to' : ℕ ⇀ ℕ
--         from' : ℕ ⇀ ℕ
--         inverse-of' : from' InverseOf' to' -- Irrelevance does not seem to help either :-(

-- open Bij'

-- -- Functions over equalities are equal
-- ≡-equality-funs : ∀ {A B : Set} {a b : A} {c d : B} (f g : a ≡ b → c ≡ d) (eq : a ≡ b) → f eq ≡ g eq
-- ≡-equality-funs f g eq rewrite ≡-irrelevance (f eq) (g eq) = refl

-- help : ∀ {f g : ℕ ⇀ ℕ} → (p q : f InverseOf' g) (x y : ℕ) → p x y ≅ q x y
-- help p q x y with p x y | q x y
-- ... | a , b | c , d with funext a c (≡-equality-funs a c) | funext b d (≡-equality-funs b d)
-- ... | eq₁ | eq₂ rewrite eq₁ | eq₂ = refl


-- bij-≡ : ∀ (β₁ β₂ : Bij') → to' β₁ ≡ to' β₂ → from' β₁ ≡ from' β₂ → β₁ ≡ β₂
-- bij-≡
--   record { to' = to₁ ; from' = from₁ ; inverse-of' = inverse-of₁ }
--   record { to' = to₂ ; from' = from₂ ; inverse-of' = inverse-of₂ } refl refl
--   with funext₂′ inverse-of₁ inverse-of₂ (help inverse-of₁ inverse-of₂)
-- ... | refl = refl

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

-- TODO: I would even remove the ᴮ from the names
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

-- TODO: remove
-- module ValidEquivᴮ {A : Set} {F : A → Set} (Valid : ∀ {a} → ℕ → F a → Set) where

--   open IProps A F

--   record VEquivalenceᴮ {R : Relᴮ} (𝑹 : IsEquivalenceᴮ R) : Set where
--     field isEq : IsEquivalenceᴮ R
--           valid-≤ : ∀ {a n} {x : F a} → Valid n x → Dom 𝑹 x ≤ n


-- TODO: remove
-- Simple (not indexed) props
-- It does not seem we need this because store
-- are restricted anyway
module SProps (F : Set) where

  open import Data.Unit
  open IProps ⊤ (λ _ → F) public

  -- Wkenᴮ : Relᴮ → Set
  -- Wkenᴮ R = ∀ {a n m} {x : F a} → n ≤ m → R x (ι n) x → R x (ι m) x

  -- Reflexiveᴮ : Relᴮ → (Dom : ∀ {a} → F a → ℕ) → Set
  -- Reflexiveᴮ R Dom = ∀ {a} {x : F a} → R x (ι (Dom x)) x

  -- Symmetricᴮ : Relᴮ → Set
  -- Symmetricᴮ R = ∀ {a β} {x y : F a} → R x β y → R y (β ⁻¹) x

  -- Transitiveᴮ : Relᴮ → Set
  -- Transitiveᴮ R = ∀ {a β₁ β₂} {x y z : F a} → R x β₁ y → R y β₂ z → R x (β₂ ∘ β₁) z
