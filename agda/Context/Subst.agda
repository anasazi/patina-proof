open import Common
open import Id.Life
module Context.Subst where

record ASubst : Set where
  constructor _↦_
  field
    from : Life
    to : Life

Subst = List ASubst
