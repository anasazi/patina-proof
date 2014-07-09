open import Nat
open import Equality
open import Decidable
open import Product

module Vec where

infixr 5 _∷_
data Vec (A : Set) : ℕ → Set where
  []  : Vec A 0
  _∷_ : ∀ {n} → A → Vec A n → Vec A (S n)

infix 4 [_
[_ : ∀ {A n} → Vec A n → Vec A n
[ xs = xs

infixr 5 _,,_
_,,_ : ∀ {A n} → A → Vec A n → Vec A (S n)
x ,, xs = x ∷ xs

infixr 5 _]
_] : ∀ {A} → A → Vec A 1
x ] = x ∷ []

data All {A} (P : A → Set) : ∀ {n} → Vec A n → Set where
  []  : All P []
  _∷_ : ∀ {n x} {xs : Vec A n} → P x → All P xs → All P (x ∷ xs)

data Any {A : Set} (P : A → Set) : ∀ {n} → Vec A n → Set where
  Z : ∀ {n x} {xs : Vec A n} → P x → Any P (x ∷ xs)
  S : ∀ {n x} {xs : Vec A n} → Any P xs → Any P (x ∷ xs)

map : ∀ {A B n} (f : A → B) → Vec A n → Vec B n
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

foldr : ∀ {A B : Set} {n} → (A → B → B) → B → Vec A n → B
foldr f z [] = z
foldr f z (x ∷ xs) = f x (foldr f z xs)

sum : ∀ {n} → Vec ℕ n → ℕ
sum = foldr _+_ 0

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
