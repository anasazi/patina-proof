open import Util.Level
module Util.Sum where

infixr 2 _+_
data _+_ {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  inl : A → A + B
  inr : B → A + B
  
match : {A B C : Set} → (A → C) → (B → C) → A + B → C
match f g (inl x) = f x
match f g (inr x) = g x
