module Empty where

data ⊥ : Set where

¬ : (A : Set) → Set
¬ A = A → ⊥
