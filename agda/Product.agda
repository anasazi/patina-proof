module Product where

record Σ_**_ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B fst
open Σ_**_ public

_×_ : Set → Set → Set
A × B = Σ A ** (λ _ → B)
