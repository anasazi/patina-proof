open import Id.Life
open import Syntax.Mut
module Syntax.Mode where

data Mode : Set where
  val : Mode
  ref : Life → Mut → Mode
