open import Common
module experiments.mu-calc where

data Type : Set where
  _⇒_ : Type → Type → Type

data Term (#x : ℕ) : Set where
  var : Fin #x → Term #x
  abs : Type → Term (S #x) → Term #x
  app : Term (S #x) → Term #x → Term #x

data _⊢_∶_ {#x} (Γ : Vec Type #x) : Term #x → Type → Set where
  var : ∀ {x} → Γ ⊢ var x ∶ (Γ ! x)
  abs : ∀ {τ₁ τ₂ t} → (τ₁ ∷ Γ) ⊢ t ∶ τ₂ → Γ ⊢ abs τ₁ t ∶ (τ₁ ⇒ τ₂)
