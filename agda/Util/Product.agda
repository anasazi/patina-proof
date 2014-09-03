open import Util.Level
open import Util.Function
module Util.Product where

record Σ_**_ {α β} (A : Set α) (B : A → Set β) : Set (α ⊔ β) where
  constructor _,_
  field
    fst : A
    snd : B fst
open Σ_**_ public

--syntax Σ A ** (λ x → B) = Σ[ x ∈ A ] B

infixr 3 _×_
_×_ : ∀ {α β} → Set α → Set β → Set (α ⊔ β)
A × B = Σ A ** (λ _ → B)

_***_ : {A₁ A₂ : Set} {B₁ : A₁ → Set} {B₂ : A₂ → Set}
        (f : A₁ → A₂) → (∀ {a} → B₁ a → B₂ (f a)) → Σ A₁ ** B₁ → Σ A₂ ** B₂
(f *** g) (x , y) = f x , g y

_***′_ : {A₁ A₂ B₁ B₂ : Set} → (A₁ → A₂) → (B₁ → B₂) → A₁ × B₁ → A₂ × B₂
(f ***′ g) (x , y) = f x , g y

_&&&_ : ∀ {α β γ} {A : Set α} {B : A → Set β} {C : ∀ {a} → B a → Set γ}
        → (f : (x : A) → B x) → ((x : A) → C (f x)) → ((x : A) → Σ (B x) ** C)
(f &&& g) x = f x , g x

_&&&′_ : {A B₁ B₂ : Set} (f : A → B₁) (g : A → B₂) → A → B₁ × B₂
(f &&&′ g) x = f x , g x

first : {A₁ A₂ B : Set} → (A₁ → A₂) → A₁ × B → A₂ × B
first f = f *** id

second : {A B₁ B₂ : Set} → (B₁ → B₂) → A × B₁ → A × B₂
second g = id *** g
