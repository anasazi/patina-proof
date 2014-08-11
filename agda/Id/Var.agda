open import Common
module Id.Var where

record Var : Set where
  constructor `v
  field
    name : ℕ

`v-inj : ∀ {a b} → `v a ≡ `v b → a ≡ b
`v-inj refl = refl

==Var : (a b : Var) → Dec (a ≡ b)
==Var (`v a) (`v b) with a == b
==Var (`v a) (`v .a) | yes refl = yes refl
==Var (`v a) (`v b)  | no neq = no (neq ∘ `v-inj)

EqVar : Eq Var
EqVar = record { _==_ = ==Var }
