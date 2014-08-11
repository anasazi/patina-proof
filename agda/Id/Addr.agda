open import Common
module Id.Addr where

record Addr : Set where
  constructor _#_
  field
    base : ℕ
    off : ℕ
open Addr

base-inj : ∀ {b₁ b₂ o₁ o₂} → b₁ # o₁ ≡ b₂ # o₂ → b₁ ≡ b₂
base-inj refl = refl

off-inj : ∀ {b₁ b₂ o₁ o₂} → b₁ # o₁ ≡ b₂ # o₂ → o₁ ≡ o₂
off-inj refl = refl

_=Addr=_ : (x y : Addr) → Dec (x ≡ y)
(b₁ # o₁) =Addr= (b₂ # o₂) with b₁ == b₂ | o₁ == o₂
(b₁ # o₁) =Addr= (.b₁ # .o₁) | yes refl | yes refl = yes refl
(b₁ # o₁) =Addr= (b₂ # o₂)   | _        | no neq   = no (neq ∘ off-inj)
(b₁ # o₁) =Addr= (b₂ # o₂)   | no neq   | _        = no (neq ∘ base-inj)

EqAddr : Eq Addr
EqAddr = record { _==_ = _=Addr=_ }
