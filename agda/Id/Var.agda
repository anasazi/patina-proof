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

test-i = `v 0
test-p = `v 1
test-a = `v 2
test-b = `v 3
test-c = `v 4
test-q = `v 5
test-r = `v 6
test-s = `v 7
