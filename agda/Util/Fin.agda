open import Util.Nat
open import Util.Decidable
open import Util.Equality
open import Util.Function
open import Util.Product
open import Util.Bool
module Util.Fin where

data Fin : ℕ → Set where
  fZ : ∀ {n} → Fin (S n)
  fS : ∀ {n} → Fin n → Fin (S n)

fS-inj : ∀ {n} {a b : Fin n} → fS a ≡ fS b → a ≡ b
fS-inj refl = refl

_=Fin=_ : ∀ {n} (a b : Fin n) → Dec (a ≡ b)
fZ =Fin= fZ = yes refl
fZ =Fin= fS b = no (λ ())
fS a =Fin= fZ = no (λ ())
fS a =Fin= fS b with a =Fin= b
fS a =Fin= fS b | yes pf = yes (cong fS pf)
fS a =Fin= fS b | no ¬pf = no (¬pf ∘ fS-inj)

EqFin : ∀ {n} → Eq (Fin n)
EqFin = record { _==_ = _=Fin=_ }

ℕ→Fin : ∀ {m} (n : ℕ) {n<m : IsTrue (lessNat n m)} → Fin m
ℕ→Fin {Z} n {}
ℕ→Fin {S m} Z = fZ
ℕ→Fin {S m} (S n) {n<m} = fS (ℕ→Fin n {n<m})
{-
ℕ→Fin : ∀ {m} (n : ℕ) {n<m : n < m} → Fin m
ℕ→Fin {Z} n {()}
ℕ→Fin {S m} Z = fZ
ℕ→Fin {S m} (S n) {s<s n<m} = fS (ℕ→Fin n {n<m})
-}

{-
ℕ→Fin : ∀ {m} (n : ℕ) {n<m : Σ ℕ ** (λ k → m ≡ S k + n)} → Fin m
ℕ→Fin {Z} n {_ , ()}
ℕ→Fin {S m} Z {_} = fZ
ℕ→Fin {S .(k + S n)} (S n) {k , refl} = fS (ℕ→Fin n {k , +-n-Sm k n})
-}
{-
ℕ→Fin : ∀ {m : ℕ} (n : ℕ) (n<m : Σ ℕ ** (λ k → m ≡ S k + n)) → Fin m
ℕ→Fin {Z} n (_ , ())
ℕ→Fin {S m} Z n<m = fZ
ℕ→Fin {S .(k + S n)} (S n) (k , refl) = ℕ→Fin n ((S k) , cong S (+-n-Sm k n))
-}

fin = ℕ→Fin
