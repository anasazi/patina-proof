open import Common
open import Id.Life
open import Id.Struct
open import Syntax.Mut
module Syntax.Type where

data Type : Set where
  int : Type
  ~ : Type → Type
  & : Life → Mut → Type → Type
  opt : Type → Type
  struct : Struct → List Life → Type
