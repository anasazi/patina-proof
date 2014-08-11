open import Common
module Id.Func where

record Func : Set where
  constructor `f
  field
    name : ℕ

`f-inj : ∀ {a b} → `f a ≡ `f b → a ≡ b
`f-inj refl = refl

==Func : (a b : Func) → Dec (a ≡ b)
==Func (`f a) (`f b) with a == b
==Func (`f a) (`f .a) | yes refl = yes refl
==Func (`f a) (`f b)  | no neq = no (neq ∘ `f-inj)

EqFunc : Eq Func
EqFunc = record { _==_ = ==Func }
