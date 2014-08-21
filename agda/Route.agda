open import Common
open import Type
module Route where

{-
Routes are a replacement for the addresses of the Redex Patina model.
They are very similar to Paths, but they can point into the internals of Options
(both the discriminant and the payload), which is necessary for operating on memory.

They are indexed by the number of allocations in the heap.
-}
data Route (#a : ℕ) : Set where
  -- A route to some allocation of memory in the heap
  alloc : Fin #a → Route #a
  -- A route that follows a route stored at the dereferenced route
  * : Route #a → Route #a
  -- A route that offsets from the wrapped route
  <_>_∙_ : (n : ℕ) → Route #a → Fin n → Route #a

{-
Typing for Routes. It is similar to typing for Paths.
However, note the additional constructors for the two components of Options.
-}
data _⊢_∶_route {#a #ℓ} (σ : Vec (Type #ℓ) #a) : Route #a → Type #ℓ → Set where
  alloc : ∀ {α} → σ ⊢ alloc α ∶ σ ! α route
  *~ : ∀ {r τ} → σ ⊢ r ∶ ~ τ route → σ ⊢ * r ∶ τ route
  *& : ∀ {r ℓ μ τ} → σ ⊢ r ∶ & ℓ μ τ route → σ ⊢ * r ∶ τ route
--  ∙ : ∀ {n r f τs} → σ ⊢ r ∶ rec τs route → σ ⊢ < n > r ∙ f ∶ τs ! f route
  disc : ∀ {r τ} → σ ⊢ r ∶ opt τ route → σ ⊢ < 2 > r ∙ fin 0 ∶ int route
  pay : ∀ {r τ} → σ ⊢ r ∶ opt τ route → σ ⊢ < 2 > r ∙ fin 1 ∶ τ route

-- Upshifting for the #a index
↑-alloc-r : ∀ {#a} → (d : ℕ) → ℕ → Route #a → Route (plus d #a)
↑-alloc-r d c (alloc α) with asℕ α <? c
↑-alloc-r d c (alloc α) | yes α<c = alloc (expand′ d α)
↑-alloc-r d c (alloc α) | no  α≥c = alloc (raise d α)
↑-alloc-r d c (* r) = * (↑-alloc-r d c r)
↑-alloc-r d c (< n > ρ ∙ f) = < n > ↑-alloc-r d c ρ ∙ f

-- Downshifting for the #a index
data ↓-#a-r {#a} : ℕ → Route (S #a) → Route #a → Set where
  alloc : ∀ {c a a′} → ↓c c a a′ → ↓-#a-r c (alloc a) (alloc a′)
  * : ∀ {c r r′} → ↓-#a-r c r r′ → ↓-#a-r c (* r) (* r′)
  ∙ : ∀ {c n r r′ f} → ↓-#a-r c r r′ → ↓-#a-r c (< n > r ∙ f) (< n > r′ ∙ f)
