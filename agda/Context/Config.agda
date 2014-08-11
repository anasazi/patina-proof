open import Syntax.Program
open import Context.Heap
open import Context.AddrMap
open import Context.TypeMap
open import Context.Stack
module Context.Config where

record Config : Set where
  constructor config
  field
    program : Program
    heap : Heap
    vmap : VMap
    tmap : TMap
    stack : Stack
