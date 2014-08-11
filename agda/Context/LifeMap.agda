open import Common
open import Id.Var
open import Id.Life
module Context.LifeMap where

record LifeMap : Set where
  constructor _∶_
  field
    var : Var
    life : Life

LMap = List (List LifeMap)
