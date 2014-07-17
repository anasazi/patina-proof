module Empty where

data ⊥ : Set where

¬ : ∀ {a} (A : Set a) → Set a
¬ A = A → ⊥

contrapositive : ∀ {p q} {P : Set p} {Q : Set q} → (P → Q) → (¬ Q → ¬ P)
contrapositive pq ¬q p = ¬q (pq p)

exfalso : ∀ {p} {P : Set p} → ⊥ → P
exfalso ()
