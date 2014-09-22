open import Common
module experiments.lamcalc2 where

data Type : Set where
  Unit : Type
  _⇒_ : Type → Type → Type

Cxt = Vec Type

data Term {#x} (Γ : Vec Type #x) : Type → Set where
  unit : Term Γ Unit
  var : (x : Fin #x) → Term Γ (Γ ! x)
  abs : ∀ τ₁ {τ₂} → (t : Term (τ₁ ∷ Γ) τ₂) → Term Γ (τ₁ ⇒ τ₂)
  app : ∀ {τ₁ τ₂} → (t₁ : Term Γ (τ₁ ⇒ τ₂)) → (t₂ : Term Γ τ₂) → Term Γ τ₂

data Value {#x} {Γ : Vec Type #x} : ∀ {τ} → Term Γ τ → Set where
  unit : Value unit
  abs : ∀ {τ₁ τ₂} {t : Term (τ₁ ∷ Γ) τ₂} → Value (abs τ₁ t)

[_]_ : ∀ {#x τ τ′} {Γ : Cxt #x} → Term [] ((τ′ ∷ Γ) ! max-el) → Term (τ′ ∷ Γ) τ → Term Γ τ
[ v ] unit = unit
[ v ] var x with x == max-el
[ v ] var .max-el | yes refl = {!!}
[ v ] var x | no neq = {!!}
[ v ] abs τ t = abs τ {!!}
[ v ] app t₁ t₂ = app ([ v ] t₁) ([ v ] t₂)

  {-
[_↦_]_ : ∀ {#x Γ Γ′ τ τ′}
       → (x : Fin #x)
       → (v : Term Γ′ τ′)
       → (t : Term (Γ ++ (τ′ ∷ Γ′)) τ)
       → Term (Γ ++ Γ′) τ
[ x ↦ v ] t = {!!}
-}

data _⟶_ : ∀ {τ} → Term [] τ → Term [] τ → Set where
  app-1 : ∀ {τ₁ τ₂} {t₁ t₁′ : Term [] (τ₁ ⇒ τ₂)} {t₂} → app t₁ t₂ ⟶ app t₁′ t₂
  app-2 : ∀ {τ₁ τ₂} {v : Term [] (τ₁ ⇒ τ₂)} {t t′} → Value v → app v t ⟶ app v t′
  app-abs : ∀ {τ₁ τ₂ t} {v : Term [] τ₂} → Value v → app (abs τ₁ t) v ⟶ {!!}
