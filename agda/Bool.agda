open import Empty
open import Unit
module Bool where

data Bool : Set where
  true : Bool
  false : Bool

IsTrue : Bool → Set 
IsTrue true = ⊤
IsTrue false = ⊥
