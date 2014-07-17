open import Empty
open import Unit
module Bool where

data Bool : Set where
  true : Bool
  false : Bool

{-# BUILTIN BOOL Bool #-}
{-# BUILTIN TRUE true #-}
{-# BUILTIN FALSE false #-}

_∨_ : Bool → Bool → Bool
true ∨ b = true
false ∨ true = true
false ∨ false = false

IsTrue : Bool → Set 
IsTrue true = ⊤
IsTrue false = ⊥
