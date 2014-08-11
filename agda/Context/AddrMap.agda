open import Common
open import Id.Var
open import Id.Addr
module Context.AddrMap where

record VarMap : Set where
  constructor _⇒_
  field
    var : Var
    addr : Addr

VMap = List (List VarMap)
