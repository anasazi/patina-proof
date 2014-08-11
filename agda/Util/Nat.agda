open import Util.Function
open import Util.Decidable
open import Util.Equality
open import Util.Bool
module Util.Nat where
  data ℕ : Set where
    Z : ℕ
    S : ℕ → ℕ

  {-# BUILTIN NATURAL ℕ #-}
  --{-# BUILTIN ZERO Z #-}
  --{-# BUILTIN SUC S #-}

  plus : ℕ → ℕ → ℕ
  plus Z     m = m
  plus (S n) m = S (plus n m)

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
  
  max : ℕ → ℕ → ℕ
  max Z m = m
  max (S n) Z = S n
  max (S n) (S m) = S (max n m)

  +-n-Sm : ∀ n m → plus n (S m) ≡ S (plus n m)
  +-n-Sm Z m = refl
  +-n-Sm (S n) m = cong S (+-n-Sm n m)

  data _<_ : ℕ → ℕ → Set where
    z<s : ∀ {n} → Z < S n
    s<s : ∀ {n m} → n < m → S n < S m

  lessNat : ℕ → ℕ → Bool
  lessNat n Z = false
  lessNat Z (S m) = true
  lessNat (S n) (S m) = lessNat n m
