open import Util.Level
module Util.Product where

record Σ {α β} (A : Set α) (B : A → Set β) : Set (α ⊔ β) where
  constructor _,_
  field
    fst : A
    snd : B fst
open Σ public

syntax Σ A (λ x → B) = Σ[ x ∈ A ] B

infixr 3 _×_
_×_ : ∀ {α β} → Set α → Set β → Set (α ⊔ β)
A × B = Σ A (λ _ → B)

_***_ : {A₁ A₂ : Set} {B₁ : A₁ → Set} {B₂ : A₂ → Set}
        (f : A₁ → A₂) → (∀ {a} → B₁ a → B₂ (f a)) → Σ A₁ B₁ → Σ A₂ B₂
(f *** g) (x , y) = f x , g y
