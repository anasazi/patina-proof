open import Common
open import Context.StructSet
open import Context.FuncSet
module Context.Program where

record Program : Set where
  constructor prgm
  field
    structs : StructSet
    functions : FuncSet
