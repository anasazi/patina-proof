open import Common
open import Id.Var
module Syntax.Path where

data Path : Set where
  var : Var → Path
  * : Path → Path
  _∙_ : Path → ℕ → Path
