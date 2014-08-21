module Mut where

-- Mutability qualifiers
data Mut : Set where
  imm : Mut -- Immutable
  mut : Mut -- Mutable
