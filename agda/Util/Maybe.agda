module Util.Maybe where

data Maybe (A : Set) : Set where
  none : Maybe A
  just : A → Maybe A

mmap : ∀ {A B} → (A → B) → Maybe A → Maybe B
mmap f none = none
mmap f (just x) = just (f x)
