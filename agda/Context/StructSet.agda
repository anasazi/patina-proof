open import Common
open import Syntax.StructDecl
module Context.StructSet where

StructSet = List StructDecl

open import Id.Struct
_⊢_≔_struct : StructSet → Struct → StructDecl → Set
D ⊢ s ≔ d struct = Any (_≡_ s ∘ StructDecl.name) D
