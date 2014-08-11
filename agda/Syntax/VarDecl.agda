open import Id.Var
open import Syntax.Type
module Syntax.VarDecl where

record VarDecl : Set where
  constructor _∶_
  field
    var : Var
    type : Type
