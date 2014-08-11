module Syntax.Variance where

-- variance
data Vari : Set where
  -- covariant
  cov : Vari
  -- contravariant
  con : Vari
  -- invariant
  inv : Vari
