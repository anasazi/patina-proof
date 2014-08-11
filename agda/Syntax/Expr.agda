open import Common
open import Syntax.Path
open import Syntax.Mut
open import Syntax.Type
open import Id.Life
open import Id.Struct
module Syntax.Expr where

data Expr : Set where
  num : ℕ → Expr
  add : Path → Path → Expr
  use : Path → Expr
  new : Path → Expr
  & : Life → Mut → Path → Expr
  some : Path → Expr
  none : Type → Expr
  struct : Struct → List Life → List Path → Expr
