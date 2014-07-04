open import Nat
open import Equality
open import Decidable
open import Product

module Vec where

infixr 5 _∷_
data Vec (A : Set) : ℕ → Set where
  []  : Vec A 0
  _∷_ : ∀ {n} → A → Vec A n → Vec A (S n)

data All {A : Set} (P : A → Set) : ∀ {n} → Vec A n → Set where
  []  : All P []
  _∷_ : ∀ {n x xs} → P x → All P {n} xs → All P {S n} (x ∷ xs)

data Any {A : Set} (P : A → Set) : ∀ {n} → Vec A n → Set where
  Z : ∀ {n x xs} → P x → Any P {S n} (x ∷ xs)
  S : ∀ {n x xs} → Any P {n} xs → Any P {S n} (x ∷ xs)

--infix 3 _∈_
_∈_ : ∀ {A n} (x : A) → Vec A n → Set
x ∈ xs = Any (_≡_ x) xs

_∈?_ : ∀ {A n} {{EqA : Eq A}} (x : A) (xs : Vec A n) → Dec (x ∈ xs)
x ∈? [] = no (λ ())
x ∈? (y ∷ xs) with x == y
.y ∈? (y ∷ xs) | yes refl = yes (Z refl)
x ∈? (y ∷ xs) | no _ with x ∈? xs
x ∈? (y ∷ xs) | no _ | yes pf = yes (S pf)
x ∈? (y ∷ xs) | no ¬eq | no ¬rec = no (λ { (Z h) → ¬eq h
                                         ; (S h) → ¬rec h})

_∪_ : ∀ {A n} {{EqA : Eq A}} → A → Vec A n → Σ ℕ ** (Vec A)
x ∪ xs with x ∈? xs
x ∪ xs | yes pf = _ , xs
x ∪ xs | no ¬pf = S _ , (x ∷ xs)
