open import Common
open import Route
open import Type
{-
The representation of heap in the Redex Patina model (a mapping from address to values)
does not work very well in the Agda Patina model. The Redex model requires computing
offsets from address, which poses difficult problems for Agda (namely proving that the offset
has not gone out of bounds).

Layouts are an alternative representation of heap memory for Patina.
They encode enough of the structure of memory to eliminate the address-offset problem.
Routes serve the purposes of addresses.
-}
module Layout where

-- A slot of memory that might store a value (i.e. a Maybe or Option)
data Value (A : Set) : Set where
  void : Value A
  val : A → Value A

-- Layouts are indexed by the number of allocations in the heap (b/c of Routes)
data Layout (#a : ℕ) : Set where
  -- A slot for an integer
  int : Value ℕ → Layout #a
  -- A slot for a pointer (represented as a Route)
  ptr : Value (Route #a) → Layout #a
  {- A contiguous list of layouts (i.e. a struct or an option).
     Note that the list itself is not a value (no overhead).
     Using a Vec makes it easy to check projections for correctness. -} 
  rec : ∀ {n} → Vec (Layout #a) n → Layout #a

-- Upshifting and downshifting
↑-alloc-ls : ∀ {#a n} → (d : ℕ) → ℕ → Vec (Layout #a) n → Vec (Layout (plus d #a)) n

↑-alloc-l : ∀ {#a} → (d : ℕ) → ℕ → Layout #a → Layout (plus d #a)
↑-alloc-l d c (int n) = int n
↑-alloc-l d c (ptr void) = ptr void
↑-alloc-l d c (ptr (val r)) = ptr (val (↑-alloc-r d c r))
↑-alloc-l d c (rec ls) = rec (↑-alloc-ls d c ls)

↑-alloc-ls d c [] = []
↑-alloc-ls d c (l ∷ ls) = ↑-alloc-l d c l ∷ ↑-alloc-ls d c ls

data ↓-#a-vr {#a} : ℕ → Value (Route (S #a)) → Value (Route #a) → Set where
  void : ∀ {c} → ↓-#a-vr c void void
  val : ∀ {c r r′} → ↓-#a-r c r r′ → ↓-#a-vr c (val r) (val r′)

data ↓-#a-ls {#a} : ∀ {n} → ℕ → Vec (Layout (S #a)) n → Vec (Layout #a) n → Set

data ↓-#a-l {#a} : ℕ → Layout (S #a) → Layout #a → Set where
  int : ∀ {c n} → ↓-#a-l c (int n) (int n)
  ptr : ∀ {c r r′} → ↓-#a-vr c r r′ → ↓-#a-l c (ptr r) (ptr r′)
  rec : ∀ {n c ls} {ls′ : Vec (Layout #a) n} → ↓-#a-ls c ls ls′ → ↓-#a-l c (rec ls) (rec ls′)

data ↓-#a-ls {#a} where
  [] : ∀ {c} → ↓-#a-ls c [] []
  _∷_ : ∀ {n c l ls l′} {ls′ : Vec (Layout #a) n}
      → ↓-#a-l c l l′
      → ↓-#a-ls c ls ls′
      → ↓-#a-ls c (l ∷ ls) (l′ ∷ ls′)

data layoutof {#a #ℓ} :  Type #ℓ → Layout #a → Set where
  int : layoutof int (int void) 
  ~ : ∀ {τ} → layoutof (~ τ) (ptr void)
  & : ∀ {ℓ μ τ} → layoutof (& ℓ μ τ) (ptr void)
  opt : ∀ {τ l} → layoutof τ l → layoutof (opt τ) (rec ([ int void ,, l ]))

-- A heap is simply a vector of layouts
Heap : ℕ → Set
Heap n = Vec (Layout n) n

-- Reading memory (given a heap and a route [address], produce a layout [value])
-- Note that this makes block reading very easy
data _⊢_⇒_ {#a} : Heap #a → Route #a → Layout #a → Set where
  alloc : ∀ {H α} → H ⊢ alloc α ⇒ (H ! α)
  * : ∀ {H r r′ l} → H ⊢ r ⇒ ptr (val r′) → H ⊢ r′ ⇒ l → H ⊢ * r ⇒ l
  ∙ : ∀ {H r n f ls} → H ⊢ r ⇒ rec ls → H ⊢ < n > r ∙ f ⇒ (ls ! f)

-- Writing memory (given a heap, a route [address], and a layout [value], produce a new heap)
-- Note that this makes block writing very easy
data _⊢_≔_⇒_ {#a} : Heap #a → Route #a → Layout #a → Heap #a → Set where
  alloc : ∀ {H α l} → H ⊢ alloc α ≔ l ⇒ set H α l
  * : ∀ {H r r′ l H′} → H ⊢ r ⇒ ptr (val r′) → H ⊢ r′ ≔ l ⇒ H′ → H ⊢ * r ≔ l ⇒ H′
  ∙ : ∀ {H r n f ls l H′}
    → H ⊢ r ⇒ rec ls
    → H ⊢ r ≔ rec (set ls f l) ⇒ H′
    → H ⊢ < n > r ∙ f ≔ l ⇒ H′

-- Memcopy (given a heap, a source route, and a destination route, produce a new heap)
-- Note that we do not need to specify the size. We copy the whole of whatever we point to.
_⊢_to_⇒_ : ∀ {#a} → Heap #a → Route #a → Route #a → Heap #a → Set
H ⊢ src to dst ⇒ H′ = Σ[ l ∈ Layout _ ] H ⊢ src ⇒ l × H ⊢ dst ≔ l ⇒ H′

-- Typing for layouts (i.e. typing for heap values)
-- A heap type would simply be a vector of types #a long
data _⊢_∶_layout {#a #ℓ} (σ : Vec (Type #ℓ) #a) : Layout #a → Type #ℓ → Set where
  -- Integer slots can only be integers
  int : ∀ {n} → σ ⊢ int n ∶ int layout
  -- A pointer slot can be either kind of pointer (~ or &)
  -- If it is initialized, then it points to whatever the type of the wrapped route is
  -- If it is uninitialized, then it can point to anything
  ptr~ : ∀ {r τ} → σ ⊢ r ∶ τ route → σ ⊢ ptr (val r) ∶ ~ τ layout
  ⊥~ : ∀ {τ} → σ ⊢ ptr void ∶ ~ τ layout
  ptr& : ∀ {r ℓ μ τ} → σ ⊢ r ∶ τ route → σ ⊢ ptr (val r) ∶ & ℓ μ τ layout
  ⊥& : ∀ {ℓ μ τ} → σ ⊢ ptr void ∶ & ℓ μ τ layout
  -- Options are represented as a int and a payload slot, so we just check the pieces
  opt : ∀ {τ d p} → σ ⊢ d ∶ int layout → σ ⊢ p ∶ τ layout
      → σ ⊢ rec ([ d ,, p ]) ∶ opt τ layout
--  rec : ∀ {n} {ls : Vec (Layout #a) n} {τs : Vec Type n}
--      → All (λ {(l , τ) → σ ⊢ l ∶ τ layout}) (zip ls τs)
--      → σ ⊢ rec ls ∶ rec τs layout
