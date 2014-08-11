open import Common
module Life where

data Life : Set where
  static : Life
  life : ℕ → Life

life-inj : ∀ {a b} → life a ≡ life b → a ≡ b
life-inj refl = refl

_=Life=_ : (a b : Life) → Dec (a ≡ b)
static =Life= static = yes refl
static =Life= life b = no (λ ())
life a =Life= static = no (λ ())
life a =Life= life b with a == b
life a =Life= life b | yes pf = yes (cong life pf)
life a =Life= life b | no ¬pf = no (¬pf ∘ life-inj)

EqLife : Eq Life
EqLife = record { _==_ = _=Life=_ }
