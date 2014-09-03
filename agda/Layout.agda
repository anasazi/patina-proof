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

-- Layouts are indexed by the number of allocations in the heap (b/c of Routes)
data Layout (#x #a : ℕ) : Set where
  -- A slot for an integer
  int : Maybe ℕ → Layout #x #a
  -- A slot for a pointer (represented as a Route)
  ptr : Maybe (Route #x #a) → Layout #x #a
  {- A contiguous list of layouts (i.e. a struct or an option).
     Note that the list itself is not a value (no overhead).
     Using a Vec makes it easy to check projections for correctness. -} 
  rec : ∀ {n} → Vec (Layout #x #a) n → Layout #x #a

↑#x-l : ∀ {#x #a} → ℕ → Layout #x #a → Layout (S #x) #a
↑#x-l c (int n?) = int n?
↑#x-l c (ptr r?) = ptr (mmap (↑#x-r c) r?)
↑#x-l c (rec ls) = rec (↑#x-ls ls)
  where
  ↑#x-ls : ∀ {#x #a n} → Vec (Layout #x #a) n → Vec (Layout (S #x) #a) n
  ↑#x-ls [] = []
  ↑#x-ls (x ∷ xs) = ↑#x-l c x ∷ ↑#x-ls xs

data ↓#x-l {#x #a} : ℕ → Layout (S #x) #a → Layout #x #a → Set where
  int : ∀ {c n} → ↓#x-l c (int n) (int n)
  ptr : ∀ {c r r′} → mlift (↓#x-r c) r r′ → ↓#x-l c (ptr r) (ptr r′)
  rec : ∀ {n c ls ls′} → All2 (↓#x-l c) {n} ls ls′ → ↓#x-l c (rec ls) (rec ls′)

↑#a-l : ∀ {#x #a} → ℕ → Layout #x #a → Layout #x (S #a)
↑#a-l c (int n?) = int n?
↑#a-l c (ptr r?) = ptr (mmap (↑#a-r c) r?)
↑#a-l c (rec ls) = rec (↑#a-ls ls)
  where
  ↑#a-ls : ∀ {#x #a n} → Vec (Layout #x #a) n → Vec (Layout #x (S #a)) n
  ↑#a-ls [] = []
  ↑#a-ls (x ∷ xs) = ↑#a-l c x ∷ ↑#a-ls xs

data ↓#a-l {#x #a} : ℕ → Layout #x (S #a) → Layout #x #a → Set where
  int : ∀ {c n} → ↓#a-l c (int n) (int n)
  ptr : ∀ {c r r′} → mlift (↓#a-r c) r r′ → ↓#a-l c (ptr r) (ptr r′)
  rec : ∀ {n c ls ls′} → All2 (↓#a-l c) {n} ls ls′ → ↓#a-l c (rec ls) (rec ls′)

data void-layout {#x #a #ℓ} : Type #ℓ → Layout #x #a → Set where
  int : void-layout int (int none)
  ~⊥ : ∀ {τ} → void-layout (~ τ) (ptr none)
  &⊥ : ∀ {ℓ μ τ} → void-layout (& ℓ μ τ) (ptr none)
  opt : ∀ {τ l} → void-layout τ l → void-layout (opt τ) (rec ([ int none ,, l ]))

Stack : ℕ → ℕ → Set
Stack #x #a = Vec (Layout #x #a) #x
Heap : ℕ → ℕ → Set
Heap #x #a = Vec (Layout #x #a) #a
Mem : ℕ → ℕ → Set
Mem #x #a = Stack #x #a × Heap #x #a

-- Reading memory (given a heap and a route [address], produce a layout [value])
-- Note that this makes block reading very easy
data _⊢_⇒_ {#x #a} : Mem #x #a → Route #x #a → Layout #x #a → Set where
  stack : ∀ {S H x} → (S , H) ⊢ stack x ⇒ (S ! x)
  heap : ∀ {S H a} → (S , H) ⊢ heap a ⇒ (H ! a)
  ∙ : ∀ {M r n f ls} → M ⊢ r ⇒ rec ls → M ⊢ < n > r ∙ f ⇒ (ls ! f)

-- Writing memory (given a heap, a route [address], and a layout [value], produce a new heap)
-- Note that this makes block writing very easy
data _⊢_≔_⇒_ {#x #a} : Mem #x #a → Route #x #a → Layout #x #a → Mem #x #a → Set where
  stack : ∀ {S H x l} → (S , H) ⊢ stack x ≔ l ⇒ (set S x l , H)
  heap : ∀ {S H a l} → (S , H) ⊢ heap a ≔ l ⇒ (S , set H a l)
  ∙ : ∀ {M r n f ls l M′} → M ⊢ r ⇒ rec ls → M ⊢ r ≔ rec (set ls f l) ⇒ M′ → M ⊢ < n > r ∙ f ≔ l ⇒ M′

-- Moving read
data _⊢_∶_⇒_,_ {#x #a #ℓ} : Mem #x #a → Route #x #a → Type #ℓ → Layout #x #a → Mem #x #a → Set where
  copy : ∀ {M r τ l}
       → τ Copy
       → M ⊢ r ⇒ l
       → M ⊢ r ∶ τ ⇒ l , M
  move : ∀ {M r τ l l′ M′}
       → τ Affine
       → M ⊢ r ⇒ l
       → void-layout τ l′
       → M ⊢ r ≔ l′ ⇒ M′
       → M ⊢ r ∶ τ ⇒ l , M′

test-moving-read-1 : (([ int (just 1) ]) , [])
                   ⊢ stack fZ ∶ int {0} ⇒ int (just 1)
                   , (([ int (just 1) ]) , [])
test-moving-read-1 = copy int stack
test-moving-read-2 : (([ ptr (just (heap fZ)) ]) , ([ int none ]))
                   ⊢ stack fZ ∶ ~ {0} int ⇒ ptr (just (heap fZ))
                   , (([ ptr none ]) , ([ int none ]))
test-moving-read-2 = move ~Aff stack ~⊥ stack

{-
data _,_⊢_∶_rok {#x #a #ℓ} (Γ : Context #ℓ #x) (M : Mem #x #a) : Route #x #a → Type #ℓ → Set
data _,_⊢_∶_lok {#x #a #ℓ} (Γ : Context #ℓ #x) (M : Mem #x #a) : Layout #x #a → Type #ℓ → Set

data _,_⊢_∶_rok {#x #a #ℓ} (Γ : Context #ℓ #x) (M : Mem #x #a) where
  stack : ∀ {x} → Γ , M ⊢ stack x ∶ Γ ! x rok
  heap : ∀ {a τ} → Γ , M ⊢ snd M ! a ∶ τ lok → Γ , M ⊢ heap a ∶ τ rok
  disc : ∀ {r τ} → Γ , M ⊢ r ∶ opt τ rok → Γ , M ⊢ < 2 > r ∙ fin 0 ∶ int rok
  pay : ∀ {r τ} → Γ , M ⊢ r ∶ opt τ rok → Γ , M ⊢ < 2 > r ∙ fin 1 ∶ τ rok

data _,_⊢_∶_lok {#x #a #ℓ} (Γ : Context #ℓ #x) (M : Mem #x #a) where
  int : ∀ {n?} → Γ , M ⊢ int n? ∶ int lok
  ptr~ : ∀ {r τ}
       → Γ , M ⊢ r ∶ τ rok
       → Γ , M ⊢ ptr (just r) ∶ ~ τ lok
  ⊥~ : ∀ {τ} → Γ , M ⊢ ptr none ∶ ~ τ lok
  ptr& : ∀ {r ℓ μ τ}
       → Γ , M ⊢ r ∶ τ rok
       → Γ , M ⊢ ptr (just r) ∶ & ℓ μ τ lok
  ⊥& : ∀ {ℓ μ τ} → Γ , M ⊢ ptr none ∶ & ℓ μ τ lok
  opt : ∀ {τ d p}
      → Γ , M ⊢ d ∶ int lok
      → Γ , M ⊢ p ∶ τ lok
      → Γ , M ⊢ rec ([ d ,, p ]) ∶ opt τ lok

_⊢_mem-ok : ∀ {#x #a #ℓ} → Context #ℓ #x → Mem #x #a → Set
Γ ⊢ M mem-ok = All2 (λ l τ → Γ , M ⊢ l ∶ τ lok) (fst M) Γ
-}

-- Typing for layouts
data _,_⊢_∶_layout {#x #a #ℓ} (Γ : Cxt #ℓ #x)
                              (Σ : Cxt #ℓ #a) : Layout #x #a → Type #ℓ → Set where
  -- Integer slots can only be integers
  int : ∀ {n?} → Γ , Σ ⊢ int n? ∶ int layout
  -- A pointer slot can be either kind of pointer (~ or &)
  -- If it is initialized, then it points to whatever the type of the wrapped route is
  -- If it is uninitialized, then it can point to anything
  ptr~ : ∀ {r τ} → Γ , Σ ⊢ r ∶ τ route → Γ , Σ ⊢ ptr (just r) ∶ ~ τ layout
  ⊥~ : ∀ {τ} → Γ , Σ ⊢ ptr none ∶ ~ τ layout
  ptr& : ∀ {r ℓ μ τ} → Γ , Σ ⊢ r ∶ τ route → Γ , Σ ⊢ ptr (just r) ∶ & ℓ μ τ layout
  ⊥& : ∀ {ℓ μ τ} → Γ , Σ ⊢ ptr none ∶ & ℓ μ τ layout
  -- Options are represented as a int and a payload slot, so we just check the pieces
  opt : ∀ {τ d p} → Γ , Σ ⊢ d ∶ int layout → Γ , Σ ⊢ p ∶ τ layout
      → Γ , Σ ⊢ rec ([ d ,, p ]) ∶ opt τ layout

_,_⊢_mem : ∀ {#x #a #ℓ} → Cxt #ℓ #x → Cxt #ℓ #a → Mem #x #a → Set
Γ , Σ ⊢ St , H mem = All2 (λ l τ → Γ , Σ ⊢ l ∶ τ layout) St Γ
                   × All2 (λ l τ → Γ , Σ ⊢ l ∶ τ layout) H Σ

-- Reading preserves types
read-preservation : ∀ {#x #a #ℓ r l Γ Σ} {M : Mem #x #a} {τ : Type #ℓ}
                  → Γ , Σ ⊢ M mem
                  → Γ , Σ ⊢ r ∶ τ route
                  → M ⊢ r ⇒ l
                  → Γ , Σ ⊢ l ∶ τ layout
read-preservation (⊢S , ⊢H) (stack {x}) stack = ⊢S All2! x
read-preservation (⊢S , ⊢H) (heap {a}) heap = ⊢H All2! a
read-preservation ⊢M (disc r∶opt-τ) (∙ r⇒l) with read-preservation ⊢M r∶opt-τ r⇒l
... | opt ∙0∶int ∙1∶τ = ∙0∶int
read-preservation ⊢M (pay r∶opt-τ) (∙ r⇒l) with read-preservation ⊢M r∶opt-τ r⇒l
... | opt ∙0∶int ∙1∶τ = ∙1∶τ

-- Writing something of the same type as the route does not change the type of memory
write-preservation : ∀ {#x #a #ℓ r l Γ Σ} {M M′ : Mem #x #a} {τ : Type #ℓ}
                   → Γ , Σ ⊢ M mem
                   → Γ , Σ ⊢ r ∶ τ route
                   → Γ , Σ ⊢ l ∶ τ layout
                   → M ⊢ r ≔ l ⇒ M′
                   → Γ , Σ ⊢ M′ mem
write-preservation (⊢S , ⊢H) (stack {x}) l∶τ stack = All2set′ ⊢S x l∶τ , ⊢H
write-preservation (⊢S , ⊢H) (heap {a}) l∶τ heap = ⊢S , All2set′ ⊢H a l∶τ
write-preservation ⊢M (disc r∶opt-τ) l∶int (∙ r⇒ls r≔ls′) with read-preservation ⊢M r∶opt-τ r⇒ls
... | opt ∙0∶int ∙1∶τ = write-preservation ⊢M r∶opt-τ (opt l∶int ∙1∶τ) r≔ls′
write-preservation ⊢M (pay r∶opt-τ) l∶τ (∙ r⇒ls r≔ls′) with read-preservation ⊢M r∶opt-τ r⇒ls
... | opt ∙0:int ∙1:τ = write-preservation ⊢M r∶opt-τ (opt ∙0:int l∶τ) r≔ls′

data _⊢_init {#x #a} (M : Mem #x #a) : Layout #x #a → Set where
  int : ∀ {n} → M ⊢ int (just n) init
  ptr : ∀ {r l} → M ⊢ r ⇒ l → M ⊢ l init → M ⊢ ptr (just r) init
  rec : ∀ {n} {ls : Vec (Layout #x #a) n} → All (λ l → M ⊢ l init) ls → M ⊢ rec ls init

data _void {#x #a} : Layout #x #a → Set where
  int : int none void
  ptr : ptr none void
  rec : ∀ {n} {ls : Vec (Layout #x #a) n} → All _void ls → rec ls void

data _⊢_reaches_layout {#x #a} (M : Mem #x #a) : Layout #x #a → Fin #a → Set
data _⊢_reaches_route {#x #a} (M : Mem #x #a) : Route #x #a → Fin #a → Set

data _⊢_reaches_layout {#x #a} (M : Mem #x #a) where
  ptr : ∀ {r a} → M ⊢ r reaches a route → M ⊢ ptr (just r) reaches a layout
  rec : ∀ {n a} {ls : Vec _ n} → Any (λ l → M ⊢ l reaches a layout) ls → M ⊢ rec ls reaches a layout

data _⊢_reaches_route {#x #a} (M : Mem #x #a) where
  refl : ∀ {a} → M ⊢ heap a reaches a route
  stack : ∀ {x a} → M ⊢ fst M ! x reaches a layout → M ⊢ stack x reaches a route
  heap : ∀ {a′ a} → M ⊢ snd M ! a′ reaches a layout → M ⊢ heap a′ reaches a route
  ∙ : ∀ {n r f a} → M ⊢ r reaches a route → M ⊢ < n > r ∙ f reaches a route

_⊢_reachable : ∀ {#x #a} → Mem #x #a → Fin #a → Set
M ⊢ a reachable = Any (λ l → M ⊢ l reaches a layout) (fst M)

NoGarbage : ∀ {#a #x} → Mem #x #a → Set
NoGarbage {#a} M = All (λ a → M ⊢ a reachable) (range′ #a)

private
  M : Mem 4 4
  M = ([ int (just 1) ,, ptr (just (heap fZ))
      ,, int none ,, rec ([ int none ,, ptr (just (heap (fin 2))) ]) ])
    , ([ ptr (just (stack (fin 2))) ,, int (just 2) ,, ptr (just (heap (fin 1))) ,, int none ])

  M-0 : M ⊢ fin 0 reachable
  M-0 = S (Z (ptr refl))
  M-1 : M ⊢ fin 1 reachable
  M-1 = S (S (S (Z (rec (S (Z (ptr (heap (ptr refl)))))))))
  M-2 : M ⊢ fin 2 reachable
  M-2 = S (S (S (Z (rec (S (Z (ptr refl)))))))
  M-3 : ¬ (M ⊢ fin 3 reachable)
  M-3 (Z ())
  M-3 (S (Z (ptr (heap (ptr (stack ()))))))
  M-3 (S (S (Z ())))
  M-3 (S (S (S (Z (rec (Z ()))))))
  M-3 (S (S (S (Z (rec (S (Z (ptr (heap (ptr (heap ())))))))))))
  M-3 (S (S (S (Z (rec (S (S ())))))))
  M-3 (S (S (S (S ()))))

  M-NG : ¬ (NoGarbage M)
  M-NG (_ ∷ _ ∷ _ ∷ Z () ∷ [])
  M-NG (_ ∷ _ ∷ _ ∷ S (Z (ptr (heap (ptr (stack ()))))) ∷ [])
  M-NG (_ ∷ _ ∷ _ ∷ S (S (Z ())) ∷ [])
  M-NG (_ ∷ _ ∷ _ ∷ S (S (S (Z (rec (Z ()))))) ∷ [])
  M-NG (_ ∷ _ ∷ _ ∷ S (S (S (Z (rec (S (Z (ptr (heap (ptr (heap ())))))))))) ∷ [])
  M-NG (_ ∷ _ ∷ _ ∷ S (S (S (Z (rec (S (S ())))))) ∷ [])
  M-NG (_ ∷ _ ∷ _ ∷ S (S (S (S ()))) ∷ [])
  
  M′ : Mem 1 2
  M′ = ([ ptr (just (heap fZ)) ])
     , ([ ptr (just (heap (fin 1))) ,, int none ])

  M′-0 : M′ ⊢ fin 0 reachable
  M′-0 = Z (ptr refl)
  M′-1 : M′ ⊢ fin 1 reachable
  M′-1 = Z (ptr (heap (ptr refl)))

  M′-NG : NoGarbage M′
  M′-NG = Z (ptr refl) ∷ Z (ptr (heap (ptr refl))) ∷ []
