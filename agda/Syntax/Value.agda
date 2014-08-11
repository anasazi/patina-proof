open import Common
open import Id.Addr
module Syntax.Value where

data Value : Set where
  void : Value
  num : ℕ → Value
  ptr : Addr → Value
