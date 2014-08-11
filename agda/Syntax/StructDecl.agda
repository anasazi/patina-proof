open import Common
open import Id.Struct
open import Id.Life
open import Syntax.Variance
open import Syntax.Type
module Syntax.StructDecl where

record StructDecl : Set where
  constructor struct
  field
    name : Struct
    params : List (Vari × Life)
    fields : List Type
