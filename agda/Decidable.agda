open import Empty
open import Level
module Decidable where
  data Dec {a} (P : Set a) : Set a where
    yes : P → Dec P
    no  : ¬ P → Dec P 

  dec-match : ∀ {p r} {P : Set p} {R : Set r} → (P → R) → (¬ P → R) → Dec P → R
  dec-match y n (yes p) = (y p)
  dec-match y n (no ¬p) = (n ¬p)

  data IsYes {a} (P : Set a) : Dec P → Set a where
    isyes : ∀ {x} → IsYes P (yes x)

  Decidable : ∀ {a b} {A : Set a} (P : A → Set b) → Set (a ⊔ b)
  Decidable P = ∀ x → Dec (P x)
