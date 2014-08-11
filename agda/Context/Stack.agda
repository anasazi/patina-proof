open import Common
open import Id.Life
open import Syntax.Stmt
module Context.Stack where

record Frame : Set where
  constructor _∶_
  field
    label : Life
    body : List Stmt

Stack = List Frame
