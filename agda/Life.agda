open import Decidable
open import Equality
open import Function
open import Nat
module Life where

data Life : Set where
  life : ℕ → Life

life-inj : ∀ {a b} → life a ≡ life b → a ≡ b
life-inj refl = refl

_=Life=_ : (a b : Life) → Dec (a ≡ b)
life a =Life= life b with a == b
... | yes p = yes (cong life p)
... | no p = no (p ∘ life-inj)

EqLife : Eq Life
EqLife = record { _==_ = _=Life=_ }
