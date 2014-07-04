open import Empty
module Decidable where
  data Dec (P : Set) : Set where
    yes : P → Dec P
    no  : ¬ P → Dec P 
