open import Util.Nat
open import Util.Equality
open import Util.Decidable
open import Util.Fin
open import Util.Product
open import Util.Function
open import Util.Empty

module Util.Vec where

infixr 5 _∷_
data Vec (A : Set) : ℕ → Set where
  []  : Vec A 0
  _∷_ : ∀ {n} → A → Vec A n → Vec A (S n)

private
  ∷-inj : ∀ {A n x y xs} {ys : Vec A n} → x ∷ xs ≡ y ∷ ys → x ≡ y × xs ≡ ys
  ∷-inj refl = refl , refl

  _=vec=_ : ∀ {A n} {{EqA : Eq A}} (xs ys : Vec A n) → Dec (xs ≡ ys)
  [] =vec= [] = yes refl
  (x ∷ xs) =vec= (y ∷ ys) with x == y | xs =vec= ys
  (x ∷ xs) =vec= (.x ∷ .xs) | yes refl | yes refl = yes refl
  (x ∷ xs) =vec= (y ∷ ys)   | _        | no neq   = no (neq ∘ snd ∘ ∷-inj)
  (x ∷ xs) =vec= (y ∷ ys)   | no neq   | _        = no (neq ∘ fst ∘ ∷-inj)

EqVec : ∀ {A n} {{EqA : Eq A}} → Eq (Vec A n)
EqVec = record { _==_ = _=vec=_ }

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

data All2 {A B} (P : A → B → Set) : ∀ {n} → Vec A n → Vec B n → Set where
  [] : All2 P [] []
  _∷_ : ∀ {n x y xs ys} → P x y → All2 P {n} xs ys → All2 P (x ∷ xs) (y ∷ ys)

data Any {A : Set} (P : A → Set) : ∀ {n} → Vec A n → Set where
  Z : ∀ {n x} {xs : Vec A n} → P x → Any P (x ∷ xs)
  S : ∀ {n x} {xs : Vec A n} → Any P xs → Any P (x ∷ xs)

Any-ix : ∀ {A P n} {xs : Vec A n} → Any P xs → Fin n
Any-ix (Z px) = fZ
Any-ix (S pf) = fS (Any-ix pf)

Any-pf : ∀ {A P n} {xs : Vec A n} → Any P xs → Σ A ** (λ x →  P x)
Any-pf (Z px) = _ , px
Any-pf (S pf) = Any-pf pf

All-Any : ∀ {A P Q n} {xs : Vec A n} → All P xs → Any Q xs → Σ A ** (λ x → P x × Q x)
All-Any (p ∷ ps) (Z q) = _ , (p , q)
All-Any (p ∷ ps) (S qs) = All-Any ps qs

infixl 8 _!_
_!_ : ∀ {A n} → Vec A n → Fin n → A
(x ∷ xs) ! fZ = x
(x ∷ xs) ! fS i = xs ! i

_All!_ : ∀ {A n P xs} → All {A} P {n} xs → (i : Fin n) → P (xs ! i)
(p ∷ ps) All! fZ = p
(p ∷ ps) All! fS i = ps All! i

_All2!_ : ∀ {A B n P xs ys} → All2 {A} {B} P {n} xs ys → (i : Fin n) → P (xs ! i) (ys ! i)
(p ∷ ps) All2! fZ = p
(p ∷ ps) All2! fS i = ps All2! i

set : ∀ {A n} → Vec A n → Fin n → A → Vec A n
set (x ∷ xs) fZ v = v ∷ xs
set (x ∷ xs) (fS i) v = x ∷ set xs i v

set! : ∀ {A n} → (xs : Vec A n) (i : Fin n) → set xs i (xs ! i) ≡ xs
set! (x ∷ xs) fZ = refl
set! (x ∷ xs) (fS i) = cong (_∷_ x) (set! xs i)

All2set : ∀ {A B n P xs ys x y}
        → All2 {A} {B} P {n} xs ys → (i : Fin n) → P x y → All2 P (set xs i x) (set ys i y)
All2set (_ ∷ ps) fZ p = p ∷ ps
All2set (p′ ∷ ps) (fS i) p = p′ ∷ All2set ps i p

All2set′ : ∀ {A B n P xs ys x}
         → All2 {A} {B} P {n} xs ys → (i : Fin n) → P x (ys ! i) → All2 P (set xs i x) ys
All2set′ (_ ∷ ps) fZ p = p ∷ ps
All2set′ (p′ ∷ ps) (fS i) p = p′ ∷ All2set′ ps i p

all? : ∀ {A n} {P : A → Set} (p? : Decidable P) → Decidable (All P {n})
all? p? [] = yes []
all? p? (x ∷ xs) with p? x | all? p? xs
all? p? (x ∷ xs) | yes px | yes pxs = yes (px ∷ pxs)
all? p? (x ∷ xs) | yes px | no ¬pxs = no (λ { (Hpx ∷ Hpxs) → ¬pxs Hpxs })
all? p? (x ∷ xs) | no ¬px | IH = no (λ { (Hpx ∷ Hpxs) → ¬px Hpx })

any? : ∀ {A n} {P : A → Set} (p? : Decidable P) → Decidable (Any P {n})
any? p? [] = no (λ ())
any? p? (x ∷ xs) with p? x
any? p? (x ∷ xs) | yes px = yes (Z px)
any? p? (x ∷ xs) | no ¬px with any? p? xs
any? p? (x ∷ xs) | no ¬px | yes pxs = yes (S pxs)
any? p? (x ∷ xs) | no ¬px | no ¬pxs = no (λ {(Z px) → ¬px px ; (S pxs) → ¬pxs pxs })

_⊗_ : ∀ {n A B} → Vec (A → B) n → Vec A n → Vec B n
[] ⊗ [] = []
(f ∷ fs) ⊗ (x ∷ xs) = f x ∷ fs ⊗ xs

rep : ∀ {A} → A → (n : ℕ) → Vec A n
rep x Z = []
rep x (S n) = x ∷ rep x n

map′ : ∀ {n A B} (f : A → B) → Vec A n → Vec B n
map′ f xs = rep f _ ⊗ xs

map : ∀ {A B n} (f : A → B) → Vec A n → Vec B n
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

foldr : ∀ {A B : Set} {n} → (A → B → B) → B → Vec A n → B
foldr f z [] = z
foldr f z (x ∷ xs) = f x (foldr f z xs)

sum : ∀ {n} → Vec ℕ n → ℕ
sum = foldr plus 0

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

uniqcons : ∀ {A n} {{EqA : Eq A}} → A → Vec A n → Σ ℕ ** (Vec A)
uniqcons x xs with x ∈? xs
uniqcons x xs | yes pf = _ , xs
uniqcons x xs | no ¬pf = S _ , (x ∷ xs)

_∪_ : ∀ {A n m} {{EqA : Eq A}} → Vec A n → Vec A m → Σ ℕ ** (Vec A)
[] ∪ ys = _ , ys
(x ∷ xs) ∪ ys with xs ∪ ys
(x ∷ xs) ∪ ys | _ , xys = uniqcons x xys 

_++_ : ∀ {A n m} → Vec A n → Vec A m → Vec A (plus n m)
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ xs ++ ys

snoc : ∀ {A n} → Vec A n → A → Vec A (S n)
snoc [] x = [ x ]
snoc (y ∷ xs) x = y ∷ snoc xs x

rev : ∀ {A n} → Vec A n → Vec A n
rev [] = []
rev (x ∷ xs) = snoc (rev xs) x

zip : ∀ {A B n} → Vec A n → Vec B n → Vec (A × B) n
zip [] [] = []
zip (x ∷ xs) (y ∷ ys) = x , y ∷ zip xs ys

range : ∀ n → Vec ℕ n
range Z = []
range (S n) = snoc (range n) n

range′ : ∀ n → Vec (Fin n) n
range′ Z = []
range′ (S n) = fZ ∷ map fS (range′ n)

range′-test : range′ 3 ≡ ([ fin 0 ,, fin 1 ,, fin 2 ])
range′-test = refl

map-!-comm : ∀ {A B n} (f : A → B) xs (ix : Fin n) → map f xs ! ix ≡ f (xs ! ix)
map-!-comm f (x ∷ xs) fZ = refl
map-!-comm f (x ∷ xs) (fS ix) = map-!-comm f xs ix

range′-spec : ∀ {n} f → range′ n ! f ≡ f
range′-spec fZ = refl
range′-spec {S n} (fS f) rewrite map-!-comm fS (range′ n) f = cong fS (range′-spec f)

range′′ : ∀ n m → Vec (Fin (plus n m)) n
range′′ n m = map (expand m) (range′ n)

take : ∀ {A m} n → Vec A (plus n m) → Vec A n
take Z xs = []
take (S n) (x ∷ xs) = x ∷ (take n xs)

drop : ∀ {A m} n → Vec A (plus n m) → Vec A m
drop Z xs = xs
drop (S n) (x ∷ xs) = drop n xs

{-
remove : ∀ {A n} → Vec A (S n) → Fin (S n) → Vec A n
remove (x ∷ xs) fZ = xs
remove (x ∷ xs) (fS i) = {!!}
-}

data remove-elem {A} : ∀ {n} → Vec A (S n) → Fin (S n) → Vec A n → Set where
  re-Z : ∀ {n x xs} → remove-elem {_} {n} (x ∷ xs) fZ xs
  re-S : ∀ {n x xs i xs′}
       → remove-elem {_} {n} xs i xs′
       → remove-elem (x ∷ xs) (fS i) (x ∷ xs′) 

test-remove-elem-1 : remove-elem ([ 0 ,, 1 ,, 2 ]) (fin 0) ([ 1 ,, 2 ])
test-remove-elem-1 = re-Z
test-remove-elem-2 : remove-elem ([ 0 ,, 1 ,, 2 ]) (fin 1) ([ 0 ,, 2 ])
test-remove-elem-2 = re-S re-Z
test-remove-elem-3 : remove-elem ([ 0 ,, 1 ,, 2 ]) (fin 2) ([ 0 ,, 1 ])
test-remove-elem-3 = re-S (re-S re-Z)

{-
data ↓xs {n} : ∀ {m} → ℕ → Vec (Fin (S n)) m → Vec (Fin n) m → Set where
  [] : ∀ {c} → ↓xs c [] []
  _∷_ : ∀ {m c i is j} {js : Vec (Fin n) m}
      → ↓c c i j
      → ↓xs c is js
      → ↓xs c (i ∷ is) (j ∷ js)
      -}

      {-
data FIsMax : ∀ n → Fin n → Set where
  Z : FIsMax 1 fZ
  S : ∀ {n f} → FIsMax n f → FIsMax (S n) (fS f)

FIsMax? : ∀ n → (f : Fin n) → Dec (FIsMax n f)
FIsMax? Z ()
FIsMax? (S Z) fZ = yes Z
FIsMax? (S (S n)) fZ = no (λ ())
FIsMax? (S n) (fS f) with FIsMax? n f
FIsMax? (S n) (fS f) | yes pf = yes (S pf)
FIsMax? (S n) (fS f) | no ¬pf = no (λ { (S pf) → ¬pf pf })
-}

snoc-ismax : ∀ {A n} (xs : Vec A n) → (x : A) → (f : Fin (S n)) → FIsMax f → snoc xs x ! f ≡ x
snoc-ismax [] x .fZ Z = refl
snoc-ismax [] x ._ (S ())
snoc-ismax (_ ∷ xs) x fZ ()
snoc-ismax (_ ∷ xs) x (fS f) (S pf) = snoc-ismax xs x f pf

-- snoc xs x ! f → xs ! ↓¬max f ¬pf
snoc-notmax : ∀ {A n} (xs : Vec A n) (x : A) (f : Fin (S n)) (¬pf : ¬ (FIsMax f))
            → snoc xs x ! f ≡ xs ! ↓¬max f ¬pf
snoc-notmax [] x fZ ¬pf = exfalso (¬pf Z)
snoc-notmax [] x (fS ()) ¬pf
snoc-notmax (x′ ∷ xs) x fZ ¬pf = refl
snoc-notmax (x′ ∷ xs) x (fS f) ¬pf = snoc-notmax xs x f (λ z → ¬pf (S z))

!->→shrink : ∀ {A n} {x : A} {xs : Vec A n} {f : Fin (S n)} (f>0 : fZ F< f)
           → (x ∷ xs) ! f ≡ xs ! >→shrink f f>0
!->→shrink z<s = refl
