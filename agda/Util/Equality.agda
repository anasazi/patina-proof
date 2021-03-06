open import Util.Decidable
open import Util.Level
module Util.Equality where
  infix 4 _≡_
  data _≡_ {α} {A : Set α} (x : A) : A → Set α where
    refl : x ≡ x

  {-# BUILTIN EQUALITY _≡_ #-}
  {-# BUILTIN REFL refl #-}

  record Eq {a} (A : Set a) : Set a where
    infix 4 _==_
    field
      _==_ : (x y : A) → Dec (x ≡ y)
  open Eq {{...}} public

  sym : {A : Set} {x y : A} → x ≡ y → y ≡ x
  sym refl = refl

  cong : ∀ {A B : Set} (f : A → B) {x y} → x ≡ y → f x ≡ f y
  cong f refl = refl

  _~_ : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
  refl ~ refl = refl

  subst : ∀ {a b} {A : Set a} (B : A → Set b) {x y} → x ≡ y → B x → B y
  subst B refl b = b
