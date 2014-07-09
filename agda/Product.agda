module Product where

record Σ_**_ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B fst
open Σ_**_ public

_×_ : Set → Set → Set
A × B = Σ A ** (λ _ → B)

_***_ : {A₁ A₂ : Set} {B₁ : A₁ → Set} {B₂ : A₂ → Set}
        (f : A₁ → A₂) → (∀ {a} → B₁ a → B₂ (f a)) → Σ A₁ ** B₁ → Σ A₂ ** B₂
(f *** g) (x , y) = f x , g y
