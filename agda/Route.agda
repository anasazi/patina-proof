open import Common
open import Type
module Route where

data Route (#a : ℕ) : Set where
  alloc : Fin #a → Route #a
  * : Route #a → Route #a
  <_>_∙_ : (n : ℕ) → Route #a → Fin n → Route #a

data _⊢_∶_route {#a #ℓ} (σ : Vec (Type #ℓ) #a) : Route #a → Type #ℓ → Set where
  alloc : ∀ {α} → σ ⊢ alloc α ∶ σ ! α route
  *~ : ∀ {r τ} → σ ⊢ r ∶ ~ τ route → σ ⊢ * r ∶ τ route
  *& : ∀ {r ℓ μ τ} → σ ⊢ r ∶ & ℓ μ τ route → σ ⊢ * r ∶ τ route
--  ∙ : ∀ {n r f τs} → σ ⊢ r ∶ rec τs route → σ ⊢ < n > r ∙ f ∶ τs ! f route
  disc : ∀ {r τ} → σ ⊢ r ∶ opt τ route → σ ⊢ < 2 > r ∙ fin 0 ∶ int route
  pay : ∀ {r τ} → σ ⊢ r ∶ opt τ route → σ ⊢ < 2 > r ∙ fin 1 ∶ τ route

↑-alloc-r : ∀ {#a} → (d : ℕ) → ℕ → Route #a → Route (plus d #a)
↑-alloc-r d c (alloc α) with asℕ α <? c
↑-alloc-r d c (alloc α) | yes α<c = alloc (expand′ d α)
↑-alloc-r d c (alloc α) | no  α≥c = alloc (raise d α)
↑-alloc-r d c (* r) = * (↑-alloc-r d c r)
↑-alloc-r d c (< n > ρ ∙ f) = < n > ↑-alloc-r d c ρ ∙ f
