open import Common
open import Syntax.StructDecl
open import Syntax.FuncDecl
module Syntax.Program where

record Program : Set where
  constructor prgm
  field
    structs : List StructDecl
    functions : List FuncDecl
