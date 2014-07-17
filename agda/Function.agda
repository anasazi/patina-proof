open import Level
module Function where

infixr 9 _∘_
_∘_ : {α β γ : Level} {A : Set α} {B : A → Set β} {C : ∀ a → B a → Set γ}
      (f : ∀ {a} (b : B a) → C a b) (g : ∀ a → B a) → ∀ a → C a (g a)
(f ∘ g) x = f (g x)

infixr 0 _$_
_$_ : {a b : Level} {A : Set a} {B : A → Set b}
      (f : (x : A) → B x) → (x : A) → B x
f $ x = f x

id : {α : Level} {A : Set α} → A → A
id a = a
