open import Equality
open import Decidable
open import Nat
open import Function
module Id where

data Id : Set where
  id : ℕ → Id

id-inj : ∀ {a b} → id a ≡ id b → a ≡ b
id-inj refl = refl

_=Id=_ : (a b : Id) → Dec (a ≡ b)
id a =Id= id b with a == b
... | yes p = yes (cong id p)
... | no p = no (p ∘ id-inj)

EqId : Eq Id
EqId = record { _==_ = _=Id=_ }
