open import Common
open import Syntax.Path
open import Syntax.Expr
open import Syntax.Mode
open import Syntax.VarDecl
open import Id.Life
open import Id.Func
open import Id.Var
module Syntax.Stmt where

record Block : Set

data Stmt : Set where
  set : Path → Expr → Stmt
  over : Path → Expr → Stmt
  free : Path → Stmt
  drop : Path → Stmt
  call : Func → List Life → List Path → Stmt
  match : Path → Mode → Var → Block → Block → Stmt
  blk : Block → Stmt

record Block where
  constructor block
  field
    label : Life
    locals : List VarDecl
    body : List Stmt
