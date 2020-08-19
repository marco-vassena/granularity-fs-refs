-- TODO: rename Σ to C

module Generic.Container.Lemmas (Label : Set) (Ty : Set) (Value : Ty → Set) where

open import Generic.Container.Base Label Ty Value

open import Relation.Binary.PropositionalEquality
open import Data.Product
open import Function

-- For heterogeneous values.
inj-∈′ : ∀ {ℓ n τ₁ τ₂} {C : Container ℓ} {v₁ : Value τ₁} {v₂ : Value τ₂} →
        n ↦ v₁ ∈ C → n ↦ v₂ ∈ C → Σ (τ₁ ≡ τ₂) (λ {refl → v₁ ≡ v₂})
inj-∈′ Here Here = refl , refl
inj-∈′ (There x) (There y) with inj-∈′ x y
... | refl , refl = refl , refl

inj-∈ : ∀ {ℓ n τ} {C : Container ℓ} {v₁ v₂ : Value τ} →
        n ↦ v₁ ∈ C → n ↦ v₂ ∈ C → v₁ ≡ v₂
inj-∈ x y with inj-∈′ x y
... | refl , eq = eq

open import Data.Nat

∥snoc∥ : ∀ {ℓ τ} (C : Container ℓ) (v : Value τ) → ∥ C ∷ᴿ v ∥ ≡ suc ∥ C ∥
∥snoc∥ [] v = refl
∥snoc∥ (x ∷ C) v = cong suc (∥snoc∥ C v)

-- {-# REWRITE ∥snoc∥ #-}

<-∈ : ∀ {n ℓ} {C : Container ℓ} → n < ∥ C ∥ → n ∈ C
<-∈ {C = []} ()
<-∈ {zero} {C = v ∷ C} (s≤s x) = _ , v , Here
<-∈ {suc n} {C = v ∷ C} (s≤s x) = map id (map id There) (<-∈ x)


--------------------------------------------------------------------------------
-- Moved from Store

-- Cell = Value
-- Store = Container ℓ

-- -- Sytactic sugar for Lookup
-- _↦_∈_ : ∀ {τ} → ℕ → Value τ → Store → Set
-- _↦_∈_ n c Σ = Lookup c n Σ

-- _∈_ :  ℕ → Store → Set
-- n ∈ Σ = ∃ (λ τ → P.Σ (Value τ) (λ c → n ↦ c ∈ Σ))
--   where import Data.Product as P

-- Extracts the value from a flow-insensitive cell
-- _↦_∈ᴵ_ : ∀ {τ} → ℕ → Value τ → Container ℓ → Set
-- _↦_∈ᴵ_ n v Σ = Lookup ⌞ v ⌟ᴵ n Σ

-- Extracts the value and the label from a flow-sensitive cell
-- _↦_∈ˢ_ : ∀ {τ} → ℕ → (Value τ × Label) → Container ℓ → Set
-- _↦_∈ˢ_ n x Σ = Lookup ⌞ x ⌟ˢ n Σ


trans-⊆ : ∀ {ℓ} {Σ₁ Σ₂ Σ₃ : Container ℓ} → Σ₁ ⊆ Σ₂ → Σ₂ ⊆ Σ₃ → Σ₁ ⊆ Σ₃
trans-⊆ ⊆₁ ⊆₂ ∈₁ = ⊆₂ (proj₂ (⊆₁ ∈₁))

⊆-⊆′ : ∀ {ℓ} {Σ Σ' : Container ℓ} → Σ ⊆ Σ' → Σ ⊆′ Σ'
⊆-⊆′ ⊆₁ (_ , _ , ∈₁) with ⊆₁ ∈₁
... | _ , ∈₂ = _ , _ , ∈₂

cons-∈ : ∀ {ℓ τ n} {Σ : Container ℓ} {c : Value τ} → n ∈ Σ → n ∈ (c ∷ Σ)
cons-∈ (_ , _ , Here) = _ , _ , Here
cons-∈ {c = c} (τ , c' , There x) with cons-∈ (τ , c' , x)
... | (τ' , c'' , x') = τ' , c'' , There x'

cons-∈′ : ∀ {ℓ τ τ' n} {Σ : Container ℓ} {v : Value τ} {v' : Value τ'} → n ↦ v' ∈ Σ → (suc n) ↦ v' ∈ (v ∷ Σ)
cons-∈′ Here = There Here
cons-∈′ (There ∈₁) = There (cons-∈′ ∈₁)

open import Data.Empty
open import Relation.Binary.PropositionalEquality

⊥-∉[] : ∀ {ℓ n} → n ∈ ([] {ℓ = ℓ}) → ⊥
⊥-∉[] (_ , _ , ())

∈-<  : ∀ {ℓ n} {Σ : Container ℓ} → n ∈ Σ → n < ∥ Σ ∥
∈-< (_ , _ , Here) = s≤s z≤n
∈-< (_ , _ , There x) = s≤s (∈-< (_ , _ , x))

open import Data.Nat
open import Relation.Binary.PropositionalEquality
open import Data.Nat.Properties

suc-snoc : ∀ {ℓ τ} (c : Value τ) (Σ : Container ℓ) → ∥ Σ ∷ᴿ c ∥ ≡ suc ∥ Σ ∥
suc-snoc c [] = refl
suc-snoc c (x ∷ Σ) = cong suc (suc-snoc c Σ)

-- Lemma snoc
snoc-≤ : ∀ {ℓ τ} {Σ : Container ℓ} {c : Value τ} → ∥ Σ ∥ ≤ ∥ Σ ∷ᴿ c ∥
snoc-≤ {Σ = Σ} {c = c} rewrite suc-snoc c Σ = ≤-step ≤-refl

-- TODO: rename snoc-∈
wken-∈ : ∀ {ℓ n τ τ'} {Σ : Container ℓ} {c : Value τ} {c' : Value τ'} → n ↦ c ∈ Σ → n ↦ c ∈ (Σ ∷ᴿ c')
wken-∈ Here = Here
wken-∈ (There x) = There (wken-∈ x)

wken-∈′ : ∀ {ℓ n τ} {Σ : Container ℓ} {c : Value τ} → n ∈ Σ → n ∈ (Σ ∷ᴿ c)
wken-∈′ (_ , _ , ∈₁) = (_ , _ , wken-∈ ∈₁)

pred-∈ : ∀ {ℓ n τ} {Σ : Container ℓ} {c : Value τ} → suc n ∈ (c ∷ Σ) → n ∈ Σ
pred-∈ (_ , _ , There x) = _ , _ , x

write-length-≡ : ∀ {ℓ n τ} {Σ Σ' : Container ℓ} {c : Value τ} → Σ' ≔ Σ [ n ↦ c ] → ∥ Σ' ∥ ≡ ∥ Σ ∥
write-length-≡ Here = refl
write-length-≡ (There x) = cong suc (write-length-≡ x)

-- Lemmas
-- TODO: Probably not needed this one in the end
≤-⊆ : ∀ {ℓ} {Σ₁ Σ₂ : Container ℓ} → ∥ Σ₁ ∥ ≤ ∥ Σ₂ ∥ → Σ₁ ⊆′ Σ₂
≤-⊆ {_} {Σ₁ = []} {Σ₂} z≤n ()
≤-⊆ {_} {v₁ ∷ Σ₁} {[]} () x
≤-⊆ {_} {v₁ ∷ Σ₁} {v₂ ∷ Σ₂} (s≤s n≤n') (τ , .v₁ , Here) = _ , _ , Here
≤-⊆ {_} {v₁ ∷ Σ₁} {v₂ ∷ Σ₂} (s≤s n≤n') (τ , c , There x) with ≤-⊆ n≤n'(τ , c , x)
... | (τ' , c' , x') =  τ' , c' , (There x')

≰-∉ : ∀ {ℓ} {Σ₁ Σ₂ : Container ℓ} → ∥ Σ₁ ∥ ≰ ∥ Σ₂ ∥ → ∃ (λ n → n ∈ Σ₁ × n ∉ Σ₂)
≰-∉ {_} {[]} {Σ₂} ≰ = ⊥-elim (≰ z≤n)
≰-∉ {_} {x ∷ Σ₁} {[]} ≰ = 0 , (_ , _ , Here) , ⊥-∉[]
≰-∉ {_} {x ∷ Σ₁} {x₁ ∷ Σ₂} ≰ with ≰-∉ {_} {Σ₁} {Σ₂} (λ ≤₁ → ≰ (s≤s ≤₁) )
... | n , (_ , _ , ∈₁) , ∉₂ = suc n , (_ , _ , There ∈₁) , (λ ∈₂ → ∉₂ (pred-∈ ∈₂) )

open import Relation.Nullary

-- TODO: every time we use this we could also use the one below
⊆-≤ : ∀ {ℓ} {Σ₁ Σ₂ : Container ℓ} → Σ₁ ⊆′ Σ₂ →  ∥ Σ₁ ∥ ≤ ∥ Σ₂ ∥
⊆-≤ {_} {Σ₁} {Σ₂} ⊆ with ∥ Σ₁ ∥ ≤? ∥ Σ₂ ∥
⊆-≤ {_} {Σ₁} {Σ₂} ⊆ | yes p = p
⊆-≤ {_} {Σ₁} {Σ₂} ⊆ | no ¬p with ≰-∉ ¬p
... | n , ∈₁ , ∉₂ = ⊥-elim (∉₂ (⊆ ∈₁))

⊆⇒≤ : ∀ {ℓ} {Σ₁ Σ₂ : Container ℓ} → Σ₁ ⊆ Σ₂ →  ∥ Σ₁ ∥ ≤ ∥ Σ₂ ∥
⊆⇒≤ ⊆₁ = ⊆-≤ (⊆-⊆′ ⊆₁)

pred-≢ : ∀ {n n'} → suc n ≢ suc n' → n ≢ n'
pred-≢ {n} {.n} ¬p refl = ⊥-elim (¬p refl)

open import Relation.Binary.HeterogeneousEquality as H
open import Data.Product as P

lookup-∈ : ∀ {n τ ℓ} {c : Value τ} {Σ : Container ℓ} → n ↦ c ∈ Σ → n ∈ Σ
lookup-∈ Here = _ , _ , Here
lookup-∈ (There x) with lookup-∈ x
... | _ , _ , ∈₁ = _ , _ , There ∈₁

write-only-one : ∀ {n τ ℓ} {Σ Σ' : Container ℓ} {c : Value τ} → Σ' ≔ Σ [ n ↦ c ] →
                   (∀ {n' τ' τ''} {c' : Value τ'} {c'' : Value τ''} →
                     n ≢ n' →
                     n' ↦ c' ∈ Σ →
                     n' ↦ c'' ∈ Σ' →
                     P.Σ (τ' ≡ τ'') (λ { refl → c' ≡ c''}))
write-only-one Here n≠n' Here Here = ⊥-elim (n≠n' refl)
write-only-one (There w) n≠n' Here Here = refl , refl
write-only-one Here n≠n' (There ∈₁) (There ∈₂) with inj-∈′ ∈₁ ∈₂
... | refl , refl  = refl , refl
write-only-one (There w) n≠n' (There ∈₁) (There ∈₂) with write-only-one w (pred-≢ n≠n') ∈₁ ∈₂
... | refl , refl = refl , refl

write-only-one′ : ∀ {n n' τ τ' τ'' ℓ} {Σ Σ' : Container ℓ}
                    {c : Value τ}  {c' : Value τ'} {c'' : Value τ''} →
                    Σ' ≔ Σ [ n ↦ c ] →
                    n ≢ n' →
                    n' ↦ c' ∈ Σ →
                    n' ↦ c'' ∈ Σ'
                    → P.Σ (τ' ≡ τ'') (λ { refl → c' ≡ c''})
write-only-one′ Here n≠n' Here Here = ⊥-elim (n≠n' refl)
write-only-one′ Here n≠n' (There ∈₁) (There ∈₂) with inj-∈′ ∈₁ ∈₂
... | refl , refl =  refl , refl
write-only-one′ (There w) n≠n' Here Here = refl , refl
write-only-one′ (There w) n≠n' (There ∈₁) (There ∈₂) with write-only-one′ w (pred-≢ n≠n') ∈₁ ∈₂
... | refl , refl = refl , refl


-- TODO: better switch name in write-∈ ?

write-∈ : ∀ {τ n ℓ} {Σ Σ' : Container ℓ} {c : Value τ} →
            Σ' ≔ Σ [ n ↦ c ] →
            n ↦ c ∈ Σ'
write-∈ Here = Here
write-∈ (There x) = There (write-∈ x)

write-∈′ : ∀ {ℓ τ n} {Σ Σ' : Container ℓ} {c : Value τ} →
             Σ' ≔ Σ [ n ↦ c ] →
             n ∈ Σ
write-∈′ Here = _ , _ , Here
write-∈′ (There x) with write-∈′ x
... | _ , _ , y = _ , _ , There y

write-∈′′ : ∀ {ℓ τ n n'} {Σ Σ' : Container ℓ} {c : Value τ} →
               Σ' ≔ Σ [ n ↦ c ] →
               n' ∈ Σ' →
               n' ∈ Σ
write-∈′′ Here (_ , _ , Here) = _ , _ , Here
write-∈′′ (There w) (_ , _ , Here) = _ , _ , Here
write-∈′′ Here (_ , _ , There x) = _ , _ , There x
write-∈′′ (There w) (_ , _ , There x) with write-∈′′ w (_ , _ , x)
... | _ , _ , y =  _ , _ , There y

n≮0 : ∀ {n} → n ≮ 0
n≮0 {n} ()

lookup-snoc : ∀ {n τ τ' ℓ} {Σ : Container ℓ} {c : Value τ} {c' : Value τ'} →
                n ↦ c ∈ (Σ ∷ᴿ c') →
                n < ∥ Σ ∥ →
                n ↦ c ∈ Σ
lookup-snoc {Σ = []} ∈₁ <₁ = ⊥-elim (n≮0 <₁)
lookup-snoc {Σ = x ∷ Σ₁} Here <₁ = Here
lookup-snoc {Σ = x ∷ Σ₁} (There ∈₁) (s≤s <₁) = There (lookup-snoc ∈₁ <₁)

∉-oob : ∀ {ℓ} {Σ : Container ℓ} → ∥ Σ ∥ ∈ Σ → ⊥
∉-oob {Σ = []} (_ , _ , ())
∉-oob {Σ = _ ∷ Σ₁} (_ , _ , There x) = ∉-oob (_ , _ , x)

last-∈ : ∀ {ℓ τ} {c : Value τ} (Σ : Container ℓ) → ∥ Σ ∥ ↦ c ∈ (Σ ∷ᴿ c)
last-∈ [] = Here
last-∈ (x ∷ Σ₁) = There (last-∈ Σ₁)

last-∈′ : ∀ {ℓ τ} {c : Value τ} (Σ : Container ℓ) → ∥ Σ ∥ ∈ (Σ ∷ᴿ c)
last-∈′ Σ = _ , _ , last-∈ Σ

last-≡ : ∀ {ℓ τ τ'} {Σ : Container ℓ}{c : Value τ} {c' : Value τ'} →
           ∥ Σ ∥ ↦ c' ∈ (Σ ∷ᴿ c) →
           P.Σ (τ ≡ τ') (λ { refl → c ≡ c' })
last-≡ {Σ = []} Here = refl , refl
last-≡ {Σ = _ ∷ Σ₁} (There x) with last-≡ x
... | refl , refl = refl , refl

-- TODO: remove
-- Is this needed?
-- postulate snoc-⊆ : ∀ {ℓ τ} (C : Container ℓ) (v : Value τ) → C ⊆ (C ∷ᴿ v)

refl-⊆ : ∀ {ℓ} {C : Container ℓ} → C ⊆ C
refl-⊆ = _,_ _

-- postulate write-⊆ᴹ : ∀ {ℓ τ n} {v : Value τ} {C C' : Container ℓ} → C' ≔ C [ n ↦ v ] → C ⊆ C'

open import Data.Sum

split-lookup : ∀ {ℓ τ τ' n} {v : Value τ} (C : Container ℓ) (v' : Value τ') →
                 n ↦ v ∈ (C ∷ᴿ v') → (n ↦ v ∈ C) ⊎ (Σ (τ ≡ τ') (λ { refl → v ≡ v' }))
split-lookup [] v' Here = inj₂ (refl , refl)
split-lookup [] v' (There ())
split-lookup (x ∷ C) v' Here = inj₁ Here
split-lookup (x ∷ C) v' (There ∈₁) with split-lookup C v' ∈₁
... | inj₁ ∈₁' = inj₁ (There ∈₁')
... | inj₂ (refl , refl) = inj₂ (refl , refl)


split-write :  ∀ {ℓ τ τ' n n'} {v : Value τ} {C C' : Container ℓ} {v' : Value τ'} →
                 C' ≔ C [ n' ↦ v' ] → n ↦ v ∈ C' →
                 (n ↦ v ∈ C) ⊎ (Σ (τ ≡ τ') (λ { refl → v ≡ v' }))
split-write {n = n} {n'} w ∈₁′ with n' ≟  n
split-write {n = n} {n'} w ∈₁′ | yes refl with inj-∈′ ∈₁′ (write-∈ w)
... | refl , refl = inj₂ (refl , refl)
split-write {n = n} {n'} w ∈₁′ | no ¬p with write-∈′′ w (_ , _ , ∈₁′)
... | _ , _ , ∈₁ with write-only-one′ w ¬p ∈₁ ∈₁′
... | refl , refl = inj₁ ∈₁

join-≤ : ∀ {x y z} → x ≤ z → y ≤ z → x ⊔ y ≤ z
join-≤ {z = z} x≤z y≤z with ⊔-mono-≤ x≤z y≤z
... | ≤₁ rewrite m≤n⇒m⊔n≡n {z} ≤-refl = ≤₁
