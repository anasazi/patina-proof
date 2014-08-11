open import Id.Life
module Context.LifeRel where

data LifeRel : Set where
  ∅ : LifeRel
  _<:_ : Life → LifeRel → LifeRel
  _⊎_ : LifeRel → LifeRel → LifeRel
