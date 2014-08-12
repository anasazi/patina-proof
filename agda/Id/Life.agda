open import Common
module Id.Life where

data Life : Set where
  `static : Life
  ` : ℕ → Life

`-inj : ∀ {a b} → ` a ≡ ` b → a ≡ b
`-inj refl = refl

_=Life=_ : (a b : Life) → Dec (a ≡ b)
`static =Life= `static = yes refl
`static =Life= ` b = no (λ ())
` a =Life= `static = no (λ ())
` a =Life= ` b with a == b
` a =Life= ` b | yes pf = yes (cong ` pf)
` a =Life= ` b | no ¬pf = no (¬pf ∘ `-inj)

EqLife : Eq Life
EqLife = record { _==_ = _=Life=_ }

test-b1 = ` 0
