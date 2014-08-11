open import Common
module Id where

data ID : Set where
  iD : ℕ → ID

iD-inj : ∀ {a b} → iD a ≡ iD b → a ≡ b
iD-inj refl = refl

_=ID=_ : (a b : ID) → Dec (a ≡ b)
iD a =ID= iD b with a == b
... | yes p = yes (cong iD p)
... | no p = no (p ∘ iD-inj)

EqId : Eq ID
EqId = record { _==_ = _=ID=_ }
