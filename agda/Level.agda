module Level where

postulate Level : Set
postulate lZ : Level
postulate lS : Level → Level
postulate _⊔_ : Level → Level → Level

{-# BUILTIN LEVEL Level #-}
{-# BUILTIN LEVELZERO lZ #-}
{-# BUILTIN LEVELSUC lS #-}
{-# BUILTIN LEVELMAX _⊔_ #-}
