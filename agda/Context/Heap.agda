open import Common
open import Id.Addr
open import Syntax.Value
module Context.Heap where

record Slot : Set where
  constructor _≔_
  field
    addr : Addr
    val : Value

Heap = List Slot
