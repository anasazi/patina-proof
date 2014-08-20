open import Common

module TVar where

record TVar : Set where
  constructor `
  field
    key : ℕ
