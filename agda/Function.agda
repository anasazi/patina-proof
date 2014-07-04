module Function where

infix 9 _∘_
_∘_ : {A : Set} {B : A → Set} {C : ∀ a → B a → Set}
      (f : ∀ {a} (b : B a) → C a b) (g : ∀ a → B a) → ∀ a → C a (g a)
(f ∘ g) x = f (g x)
