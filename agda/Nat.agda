open import Function
open import Decidable
open import Equality
open import Bool
module Nat where
  data ℕ : Set where
    Z : ℕ
    S : ℕ → ℕ

  {-# BUILTIN NATURAL ℕ #-}
  {-# BUILTIN ZERO Z #-}
  {-# BUILTIN SUC S #-}

  _+_ : ℕ → ℕ → ℕ
  Z   + m = m
  S n + m = S (n + m)

  S-inj : ∀ {n m} → S n ≡ S m → n ≡ m
  S-inj refl = refl

  _=ℕ=_ : (a b : ℕ) → Dec (a ≡ b)
  Z =ℕ= Z = yes refl
  Z =ℕ= S b = no (λ ())
  S a =ℕ= Z = no (λ ())
  S a =ℕ= S b with a =ℕ= b
  ... | yes p = yes (cong S p)
  ... | no p = no (p ∘ S-inj)

  EqNat : Eq ℕ
  EqNat = record { _==_ = _=ℕ=_ }

  +-n-Sm : ∀ n m → n + S m ≡ S (n + m)
  +-n-Sm Z m = refl
  +-n-Sm (S n) m = cong S (+-n-Sm n m)

  data _<_ : ℕ → ℕ → Set where
    z<s : ∀ {n} → Z < S n
    s<s : ∀ {n m} → n < m → S n < S m

  lessNat : ℕ → ℕ → Bool
  lessNat n Z = false
  lessNat Z (S m) = true
  lessNat (S n) (S m) = lessNat n m
