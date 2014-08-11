module Util.Level where

open import Agda.Primitive public
  using (Level ; _⊔_)
  renaming (lzero to lZ ; lsuc to lS)

{-
postulate Level : Set
postulate lZ : Level
postulate lS : Level → Level
postulate _⊔_ : Level → Level → Level

{-# BUILTIN LEVEL Level #-}
{-# BUILTIN LEVELZERO lZ #-}
{-# BUILTIN LEVELSUC lS #-}
{-# BUILTIN LEVELMAX _⊔_ #-}

-}
