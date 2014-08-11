open import Common
open import Id.Func
open import Id.Life
open import Syntax.VarDecl
open import Syntax.Stmt

module Syntax.FuncDecl where

record FuncDecl : Set where
  constructor fun
  field
    name : Func
    params : List Life
    args : List VarDecl
    body : Block
