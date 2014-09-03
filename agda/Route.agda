open import Common
open import Type
module Route where

{-
Routes are a replacement for the addresses of the Redex Patina model.
They are very similar to Paths, but they can point into the internals of Options
(both the discriminant and the payload), which is necessary for operating on memory.

They are indexed by the number of allocations in the heap.
-}
data Route (#x #a : ℕ) : Set where
  stack : Fin #x → Route #x #a
  heap : Fin #a → Route #x #a
  <_>_∙_ : (n : ℕ) → Route #x #a → Fin n → Route #x #a

-- upshifting and downshifting for the #x and #a indicies of Route
↑#x-r : ∀ {#x #a} → ℕ → Route #x #a → Route (S #x) #a
↑#x-r c (stack x) = stack (↑ c x)
↑#x-r c (heap a) = heap a
↑#x-r c (< n > r ∙ f) = < n > ↑#x-r c r ∙ f

data ↓#x-r {#x #a} : ℕ → Route (S #x) #a → Route #x #a → Set where
  stack : ∀ {c x x′} → ↓ c x x′ → ↓#x-r c (stack x) (stack x′)
  heap : ∀ {c a} → ↓#x-r c (heap a) (heap a)
 -- * : ∀ {c r r′} → ↓#x-r c r r′ → ↓#x-r c (* r) (* r′)
  ∙ : ∀ {c n r r′ f} → ↓#x-r c r r′ → ↓#x-r c (< n > r ∙ f) (< n > r′ ∙ f)

↑#a-r : ∀ {#x #a} → ℕ → Route #x #a → Route #x (S #a)
↑#a-r c (stack x) = stack x
↑#a-r c (heap a) = heap (↑ c a)
↑#a-r c (< n > r ∙ f) = < n > ↑#a-r c r ∙ f

data ↓#a-r {#x #a} : ℕ → Route #x (S #a) → Route #x #a → Set where
  stack : ∀ {c x} → ↓#a-r c (stack x) (stack x)
  heap : ∀ {c a a′} → ↓ c a a′ → ↓#a-r c (heap a) (heap a′)
  ∙ : ∀ {c n r r′ f} → ↓#a-r c r r′ → ↓#a-r c (< n > r ∙ f) (< n > r′ ∙ f)

{-
Typing for Routes. It is similar to typing for Paths.
However, note the additional constructors for the two components of Options.
-}
data _,_⊢_∶_route {#x #a #ℓ} (Γ : Cxt #ℓ #x)
                             (Σ : Cxt #ℓ #a) : Route #x #a → Type #ℓ → Set where
  stack : ∀ {x} → Γ , Σ ⊢ stack x ∶ Γ ! x route
  heap : ∀ {a} → Γ , Σ ⊢ heap a ∶ Σ ! a route
  disc : ∀ {r τ} → Γ , Σ ⊢ r ∶ opt τ route → Γ , Σ ⊢ < 2 > r ∙ fin 0 ∶ int route
  pay : ∀ {r τ} → Γ , Σ ⊢ r ∶ opt τ route → Γ , Σ ⊢ < 2 > r ∙ fin 1 ∶ τ route
