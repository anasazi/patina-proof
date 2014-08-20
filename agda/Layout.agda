open import Common
open import Route
open import Type
module Layout where

data Value (A : Set) : Set where
  void : Value A
  val : A → Value A

data Layout (#a : ℕ) : Set where
  int : Value ℕ → Layout #a
  ptr : Value (Route #a) → Layout #a
  rec : ∀ {n} → Vec (Layout #a) n → Layout #a

↑-alloc-ls : ∀ {#a n} → (d : ℕ) → ℕ → Vec (Layout #a) n → Vec (Layout (plus d #a)) n

↑-alloc-l : ∀ {#a} → (d : ℕ) → ℕ → Layout #a → Layout (plus d #a)
↑-alloc-l d c (int n) = int n
↑-alloc-l d c (ptr void) = ptr void
↑-alloc-l d c (ptr (val r)) = ptr (val (↑-alloc-r d c r))
↑-alloc-l d c (rec ls) = rec (↑-alloc-ls d c ls)

↑-alloc-ls d c [] = []
↑-alloc-ls d c (l ∷ ls) = ↑-alloc-l d c l ∷ ↑-alloc-ls d c ls

data layoutof {#a #ℓ} :  Type #ℓ → Layout #a → Set where
  int : layoutof int (int void) 
  ~ : ∀ {τ} → layoutof (~ τ) (ptr void)
  & : ∀ {ℓ μ τ} → layoutof (& ℓ μ τ) (ptr void)
  opt : ∀ {τ l} → layoutof τ l → layoutof (opt τ) (rec ([ int void ,, l ]))

Heap : ℕ → Set
Heap n = Vec (Layout n) n

data _⊢_⇒_ {#a} : Heap #a → Route #a → Layout #a → Set where
  alloc : ∀ {H α} → H ⊢ alloc α ⇒ (H ! α)
  * : ∀ {H r r′ l} → H ⊢ r ⇒ ptr (val r′) → H ⊢ r′ ⇒ l → H ⊢ * r ⇒ l
  ∙ : ∀ {H r n f ls} → H ⊢ r ⇒ rec ls → H ⊢ < n > r ∙ f ⇒ (ls ! f)

data _⊢_≔_⇒_ {#a} : Heap #a → Route #a → Layout #a → Heap #a → Set where
  alloc : ∀ {H α l} → H ⊢ alloc α ≔ l ⇒ set H α l
  * : ∀ {H r r′ l H′} → H ⊢ r ⇒ ptr (val r′) → H ⊢ r′ ≔ l ⇒ H′ → H ⊢ * r ≔ l ⇒ H′
  ∙ : ∀ {H r n f ls l H′}
    → H ⊢ r ⇒ rec ls
    → H ⊢ r ≔ rec (set ls f l) ⇒ H′
    → H ⊢ < n > r ∙ f ≔ l ⇒ H′

_⊢_to_⇒_ : ∀ {#a} → Heap #a → Route #a → Route #a → Heap #a → Set
H ⊢ src to dst ⇒ H′ = Σ[ l ∈ Layout _ ] H ⊢ src ⇒ l × H ⊢ dst ≔ l ⇒ H′

data _⊢_∶_layout {#a #ℓ} (σ : Vec (Type #ℓ) #a) : Layout #a → Type #ℓ → Set where
  int : ∀ {n} → σ ⊢ int n ∶ int layout
  ptr~ : ∀ {r τ} → σ ⊢ r ∶ τ route → σ ⊢ ptr (val r) ∶ ~ τ layout
  ⊥~ : ∀ {τ} → σ ⊢ ptr void ∶ ~ τ layout
  ptr& : ∀ {r ℓ μ τ} → σ ⊢ r ∶ τ route → σ ⊢ ptr (val r) ∶ & ℓ μ τ layout
  ⊥& : ∀ {ℓ μ τ} → σ ⊢ ptr void ∶ & ℓ μ τ layout
  opt : ∀ {τ d p} → σ ⊢ d ∶ int layout → σ ⊢ p ∶ τ layout
      → σ ⊢ rec ([ d ,, p ]) ∶ opt τ layout
--  rec : ∀ {n} {ls : Vec (Layout #a) n} {τs : Vec Type n}
--      → All (λ {(l , τ) → σ ⊢ l ∶ τ layout}) (zip ls τs)
--      → σ ⊢ rec ls ∶ rec τs layout
