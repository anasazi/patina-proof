open import Common
open import Id.Var
open import Id.Addr
module Context.AddrMap where

record VarMap : Set where
  constructor _⇒_
  field
    var : Var
    addr : Addr
open VarMap

VMap = List (List VarMap)

_⊢_⇒_ : VMap → Var → Addr → Set
V ⊢ x ⇒ α = Any (Any (_≡_ x ∘ var)) V
