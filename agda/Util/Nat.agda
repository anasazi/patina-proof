open import Util.Function
open import Util.Decidable
open import Util.Equality
open import Util.Bool
open import Util.Empty
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

  instance
    _=ℕ=_ : (a b : ℕ) → Dec (a ≡ b)
    Z =ℕ= Z = yes refl
    Z =ℕ= S b = no (λ ())
    S a =ℕ= Z = no (λ ())
    S a =ℕ= S b with a =ℕ= b
    ... | yes p = yes (cong S p)
    ... | no p = no (p ∘ S-inj)

    EqNat : Eq ℕ
    EqNat = record { _==_ = _=ℕ=_ }

  plus-0-r : ∀ n → plus n 0 ≡ n
  plus-0-r Z = refl
  plus-0-r (S n) = cong S (plus-0-r n)

  plus-S : ∀ n m → plus n (S m) ≡ S (plus n m)
  plus-S Z m = refl
  plus-S (S n) m = cong S (plus-S n m)

  plus-comm : ∀ n m → plus n m ≡ plus m n
  plus-comm Z m = sym (plus-0-r m)
  plus-comm (S n) m rewrite (plus-S m n) = cong S (plus-comm n m)

  plus-assoc : ∀ n m o → plus (plus n m) o ≡ plus n (plus m o)
  plus-assoc Z m o = refl
  plus-assoc (S n) m o = cong S (plus-assoc n m o)

  plus-swap : ∀ n m o → plus n (plus m o) ≡ plus m (plus n o)
  plus-swap n m o = sym (plus-assoc n m o)
                  ~ (cong (λ x → plus x o) (plus-comm n m)
                  ~ plus-assoc m n o)
  
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

  _≤_ : ℕ → ℕ → Set
  n ≤ m = n < S m

  _≥_ : ℕ → ℕ → Set
  n ≥ m = m ≤ n

  S-< : ∀ {n m} → S n < S m → n < m
  S-< (s<s pf) = pf

  n-<-Sm : ∀ {n m} → n < m → n < S m
  n-<-Sm z<s = z<s
  n-<-Sm (s<s pf) = s<s (n-<-Sm pf)

  Sn-<-m : ∀ {n m} → S n < m → n < m
  Sn-<-m (s<s pf) = n-<-Sm pf

  _<?_ : (a b : ℕ) → Dec (a < b)
  Z <? Z = no (λ ())
  Z <? S b = yes z<s
  S a <? Z = no (λ ())
  S a <? S b with a <? b
  S a <? S b | yes ih = yes (s<s ih)
  S a <? S b | no ¬ih = no (¬ih ∘ S-<)

  lessNat : ℕ → ℕ → Bool
  lessNat n Z = false
  lessNat Z (S m) = true
  lessNat (S n) (S m) = lessNat n m
