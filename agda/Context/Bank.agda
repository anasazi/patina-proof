open import Common
open import Id.Life
open import Syntax.Mut
open import Syntax.Path
module Context.Bank where

record Loan : Set where
  constructor loan
  field
    duration : Life
    kind : Mut
    loanee : Path

Bank = List Loan
