open import Nat
open import Equality
open import Decidable
open import Product
module List where
  infixr 5 _∷_
  data List (A : Set) : Set where
    []  : List A
    _∷_ : A → List A → List A

  [_ : {A : Set} → List A → List A
  [ as = as

  _,,_ : {A : Set} → A → List A → List A
  a ,, as = a ∷ as

  _] : {A : Set} → A → List A
  a ] = a ∷ []

  map : {A B : Set} → (A → B) → List A → List B
  map f [] = []
  map f (x ∷ xs) = f x ∷ map f xs

  data Map {A B : Set} (f : A → B) : List A → List B → Set where
    Z : Map f [] []
    S : ∀ {x xs ys} → Map f xs ys → Map f (x ∷ xs) (f x ∷ ys)

  foldr : {A B : Set} → (A → B → B) → B → List A → B
  foldr f z [] = z
  foldr f z (x ∷ xs) = f x (foldr f z xs)

  sum = foldr _+_ 0

  data All {A : Set} (P : A → Set) : List A → Set where
    []  : All P []
    _∷_ : ∀ {x xs} → P x → All P xs → All P (x ∷ xs)

  data Any {A : Set} (P : A → Set) : List A → Set where
    aZ : ∀ {x xs} → P x → Any P (x ∷ xs)
    aS : ∀ {x xs} → Any P xs → Any P (x ∷ xs)

  infix 3 _∈_
  _∈_ : ∀ {A : Set} (x : A) → List A → Set
  x ∈ xs = Any (_≡_ x) xs

  _∈?_ : ∀ {A} {{EqA : Eq A}} (x : A) (xs : List A) → Dec (x ∈ xs)
  x ∈? [] = no (λ ())
  x ∈? (y ∷ xs) with x == y | x ∈? xs
  .y ∈? (y ∷ xs) | yes refl | there = yes (aZ refl)
  x ∈? (y ∷ xs) | no ¬here | yes there = yes (aS there)
  x ∈? (y ∷ xs) | no ¬here | no ¬there = no (λ { (aZ h) → ¬here h
                                               ; (aS h) → ¬there h })

  _∪_ : {A : Set} {{EqA : Eq A}} → A → List A → List A
  x ∪ xs with x ∈? xs
  x ∪ xs | yes _ = xs
  x ∪ xs | no  _ = x ∷ xs

  data GoesTo {A B : Set} (k : A) : B → List (A × B) → Set where
    Z : ∀ {v xs} → GoesTo k v ((k , v) ∷ xs)
    S : ∀ {v kv xs} → GoesTo k v xs → GoesTo k v (kv ∷ xs)

  KeyIn : {A B : Set} → A → List (A × B) → Set
  KeyIn k kvs = Any (λ kv → fst kv ≡ k) kvs --∀ {v} → GoesTo k v kvs

  update : ∀ {A B} (k : A) (v : B) kvs → KeyIn k kvs → List (A × B)
  update k v .(x ∷ xs) (aZ {x} {xs} x₁) = k , v ∷ xs
  update k v .(x ∷ xs) (aS {x} {xs} loc) = x ∷ update k v xs loc

  data Update {A B : Set} (k : A) (v : B) : List (A × B) → List (A × B) → Set where
    Z : ∀ {v′ kvs} → Update k v ((k , v′) ∷ kvs) ((k , v) ∷ kvs)
    S : ∀ {kv kvs kvs′} → Update k v kvs kvs′ → Update k v (kv ∷ kvs) (kv ∷ kvs′)
