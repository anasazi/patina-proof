open import Common
open import Type
open import Path
open import Loan
open import Route
open import Layout
open import Mut
open import Life
{-
The Redex Patina model's list of deinitialized paths and list of loans in effect do not work
well with the Adga model. Both require proving something is not in the list, which is unwieldly
in Agda.

Shapes are a replacement that combines both sets of data into one structure.
A Shape is very similar to a Layout, but with initialization and loan information
instead of runtime data. The relationship between Shapes, Paths, Layouts, and Routes is:

    Path ---- points to a ---> Shape
     |                           |
     |                           |
  prefixes                   represents
     |                           |
     v                           v
   Route ---- points to a ---> Layout

Shapes have more structure to them than Layouts (differentiates pointers and options),
but only store initialization and loan data. What would be a Slot in a Layout is a Hole in a Shape.
Each step of a Shape contains a Bank, which represents the loan information for that path.
-}
module Shape where

data Shape (#x : ℕ) : Set where
  int : Maybe (Bank #x) → Shape #x
  ~ : Maybe (Bank #x × Shape #x) → Shape #x
  & : Maybe (Bank #x) → Shape #x
  opt : Maybe (Bank #x) → Shape #x

↑#x-δ : ∀ {#x} → ℕ → Shape #x → Shape (S #x)
↑#x-δ c (int b?) = int (mmap (↑-#x-b 1 c) b?)
↑#x-δ c (~ b×δ?) = ~ (f b×δ?)
  where
  f : ∀ {#x} → Maybe (Bank #x × Shape #x) → Maybe (Bank (S #x) × Shape (S #x))
  f none = none
  f (just (b , δ)) = just (↑-#x-b 1 c b , ↑#x-δ c δ)
↑#x-δ c (& b?) = & (mmap (↑-#x-b 1 c) b?)
↑#x-δ c (opt b?) = opt (mmap (↑-#x-b 1 c) b?)

data ↓#x-δ {#x} : ℕ → Shape (S #x) → Shape #x → Set where
  int : ∀ {c b? b′?} → mlift (↓1-#x-b c) b? b′? → ↓#x-δ c (int b?) (int b′?)
  ~⊥ : ∀ {c} → ↓#x-δ c (~ none) (~ none)
  ~ : ∀ {c δ b δ′ b′} → ↓1-#x-b c b b′ → ↓#x-δ c δ δ′ → ↓#x-δ c (~ (just (b , δ))) (~ (just (b′ , δ′)))
  & : ∀ {c b? b′?} → mlift (↓1-#x-b c) b? b′? → ↓#x-δ c (& b?) (& b′?)
  opt : ∀ {c b? b′?} → mlift (↓1-#x-b c) b? b′? → ↓#x-δ c (opt b?) (opt b′?)

State : ℕ → Set
State #x = Vec (Shape #x) #x

data _⊢_shape {#x} : Type #x → Shape #x → Set where
  int : ∀ {b?} → int ⊢ int b? shape
  ~ : ∀ {τ b δ} → τ ⊢ δ shape → ~ τ ⊢ ~ (just (b , δ)) shape
  ~⊥ : ∀ {τ} → ~ τ ⊢ ~ none shape
  & : ∀ {ℓ μ τ b?} → & ℓ μ τ ⊢ & b? shape
  opt : ∀ {τ b?} → opt τ ⊢ opt b? shape

_⊢_state : ∀ {#x} → Cxt #x → State #x → Set
Γ ⊢ Δ state = All2 (λ τ δ → τ ⊢ δ shape) Γ Δ

init-shape : ∀ {#ℓ} → Type #ℓ → Shape #ℓ
init-shape int = int (just (bank-def _))
init-shape (~ τ) = ~ (just (bank-def _ , init-shape τ))
init-shape (& ℓ μ τ) = & (just (bank-def _))
init-shape (opt τ) = opt (just (bank-def _))

init-well-typed : ∀ {#ℓ} → (τ : Type #ℓ) → τ ⊢ init-shape τ shape
init-well-typed int = int
init-well-typed (~ τ) = ~ (init-well-typed τ)
init-well-typed (& ℓ μ τ) = &
init-well-typed (opt τ) = opt

void-shape : ∀ {#ℓ} → Type #ℓ → Shape #ℓ
void-shape int = int none
void-shape (~ τ) = ~ none
void-shape (& ℓ μ τ) = & none
void-shape (opt τ) = opt none

data _⊢_∶_rep {#ℓ #x #a} (M : Mem #x #a) : Layout #x #a → Shape #ℓ → Set where
  int⊥ : M ⊢ int none ∶ int none rep
  int : ∀ {n b} → M ⊢ int (just n) ∶ int (just b) rep
  ~⊥ : M ⊢ ptr none ∶ ~ none rep
  ~ : ∀ {r δ b l} → M ⊢ r ⇒ l → M ⊢ l ∶ δ rep → M ⊢ ptr (just r) ∶ ~ (just (b , δ)) rep
  &⊥ : M ⊢ ptr none ∶ & none rep
  & : ∀ {r b l} → M ⊢ r ⇒ l → M ⊢ l init → M ⊢ ptr (just r) ∶ & (just b) rep
  opt⊥ : ∀ {l} → l void → M ⊢ rec ([ int none ,, l ]) ∶ opt none rep
  none : ∀ {b l} → M ⊢ l init → M ⊢ rec ([ int (just 0) ,, l ]) ∶ opt (just b) rep
  some : ∀ {b l} → M ⊢ l init → M ⊢ rec ([ int (just 1) ,, l ]) ∶ opt (just b) rep

_⊢_mem-state : ∀ {#x #a} → State #x → Mem #x #a → Set
Δ ⊢ M mem-state = All2 (λ δ l → M ⊢ l ∶ δ rep) Δ (fst M)

data _,_⊢_⇒_shape {#x} (Γ : Cxt #x) (Δ : State #x) : Path #x → Shape #x → Set where
  var : ∀ {x} → Γ , Δ ⊢ var x ⇒ Δ ! x shape
  *~ : ∀ {p δ b} → Γ , Δ ⊢ p ⇒ ~ (just (b , δ)) shape → Γ , Δ ⊢ * p ⇒ δ shape
  *& : ∀ {p b τ} → Γ , Δ ⊢ p ⇒ & (just b) shape → Γ ⊢ p ∶ τ path → Γ , Δ ⊢ * p ⇒ init-shape τ shape

data _,_⊢_≔_⇒_shape {#x} (Γ : Cxt #x) (Δ : State #x)
                    : Path #x → Shape #x → State #x → Set where
  var : ∀ {x δ} → Γ , Δ ⊢ var x ≔ δ ⇒ set Δ x δ shape
  * : ∀ {p δ δ′ Δ′}
    → Γ , Δ ⊢ p ⇒ ~ δ′ shape
    → Γ , Δ ⊢ p ≔ ~ (just (bank-def _ , δ)) ⇒ Δ′ shape
    → Γ , Δ ⊢ * p ≔ δ ⇒ Δ′ shape

record _,_⊢_⇒_init {#x} (Γ : Cxt #x) (Δ : State #x) (p : Path #x) (Δ′ : State #x) : Set where
  constructor init
  field
    {τ} : Type #x
    path : Γ ⊢ p ∶ τ path
    write : Γ , Δ ⊢ p ≔ init-shape τ ⇒ Δ′ shape

record _,_⊢_⇒_void {#x} (Γ : Cxt #x) (Δ : State #x) (p : Path #x) (Δ′ : State #x) : Set where
  constructor void
  field
    {τ} : Type #x
    path : Γ ⊢ p ∶ τ path
    write : Γ , Δ ⊢ p ≔ void-shape τ ⇒ Δ′ shape

data _borrow_for_⇒_ {#x} : Mut → Shape #x → Life #x → Shape #x → Set where
  int : ∀ {μ ℓ b} → μ borrow int (just b) for ℓ ⇒ int (just (make-loan b ℓ μ))
  ~ : ∀ {μ ℓ b δ} → μ borrow ~ (just (b , δ)) for ℓ ⇒ ~ (just (make-loan b ℓ μ , δ))
  & : ∀ {μ ℓ b} → μ borrow & (just b) for ℓ ⇒ & (just (make-loan b ℓ μ))
  opt : ∀ {μ ℓ b} → μ borrow opt (just b) for ℓ ⇒ opt (just (make-loan b ℓ μ))

record _,_⊢_borrow_for_⇒_ {#x} (Γ : Cxt #x) (Δ : State #x) (μ : Mut)
                          (p : Path #x) (ℓ : Life #x) (Δ′ : State #x) : Set where
  constructor borrow
  field
    {δ δ′} : Shape #x
    shallow : Γ , Δ ⊢ p ⇒ δ shape
    borrowed : μ borrow δ for ℓ ⇒ δ′
    write : Γ , Δ ⊢ p ≔ δ′ ⇒ Δ′ shape

data _Full {#x} : Shape #x → Set where
  int : ∀ {b} → int (just b) Full
  ~ : ∀ {δ b} → δ Full → ~ (just (b , δ)) Full
  & : ∀ {b} → & (just b) Full
  opt : ∀ {b} → opt (just b) Full

record _,_⊢_deep {#x} (Γ : Cxt #x) (Δ : State #x) (p : Path #x) : Set where
  constructor deep
  field
    {δ} : Shape #x
    shallow : Γ , Δ ⊢ p ⇒ δ shape
    full : δ Full

data _Empty {#x} : Shape #x → Set where
  int : int none Empty
  ~ : ~ none Empty
  & : & none Empty
  opt : opt none Empty

record _,_⊢_initable {#x} (Γ : Cxt #x) (Δ : State #x) (p : Path #x) : Set where
  constructor initable
  field
    {δ} : Shape #x
    shallow : Γ , Δ ⊢ p ⇒ δ shape
    empty : δ Empty

data _⊢_Dropped {#x} : Type #x → Shape #x → Set where
  int : ∀ {b?} → int ⊢ int b? Dropped
  ~-drop : ∀ {τ} → ~ τ ⊢ ~ none Dropped
  & : ∀ {ℓ μ τ b?} → & ℓ μ τ ⊢ & b? Dropped
  opt-¬drop : ∀ {τ} → τ ¬Drop → opt τ ⊢ opt none Dropped
  opt-drop : ∀ {τ b?} → τ Drop → opt τ ⊢ opt b? Dropped

record _,_⊢_dropped {#x} (Γ : Cxt #x) (Δ : State #x) (p : Path #x) : Set where
  constructor dropped
  field
    {δ} : Shape #x
    shallow : Γ , Δ ⊢ p ⇒ δ shape
    {τ} : Type #x
    path : Γ ⊢ p ∶ τ path
    cleaned : τ ⊢ δ Dropped

data read-unrestricted {#x} : Shape #x → Set where
  int : ∀ {b} → Readable b → read-unrestricted (int (just b))
  ~ : ∀ {b δ} → Readable b → read-unrestricted δ → read-unrestricted (~ (just (b , δ)))
  & : ∀ {b} → Readable b → read-unrestricted (& (just b))
  opt : ∀ {b} → Readable b → read-unrestricted (opt (just b))

record _,_⊢_read-unrestricted {#x} (Γ : Cxt #x) (Δ : State #x) (p : Path #x) : Set where
  constructor read-unres
  field
    {δ} : Shape #x
    shallow : Γ , Δ ⊢ p ⇒ δ shape
    unrestricted : read-unrestricted δ

data read-unencumbered {#x} : Shape #x → Set where
  int : ∀ {b} → NoMuts b → read-unencumbered (int (just b))
  ~ : ∀ {b δ} → NoMuts b → read-unencumbered (~ (just (b , δ)))
  & : ∀ {b} → NoMuts b → read-unencumbered (& (just b))
  opt : ∀ {b} → NoMuts b → read-unencumbered (opt (just b))

data _,_⊢_read-unencumbered {#x} (Γ : Cxt #x) (Δ : State #x) : Path #x → Set where
  var : ∀ {x} → read-unencumbered (Δ ! x) → Γ , Δ ⊢ var x read-unencumbered
  * : ∀ {p δ}
    → Γ , Δ ⊢ p read-unencumbered
    → Γ , Δ ⊢ * p ⇒ δ shape
    → read-unencumbered δ
    → Γ , Δ ⊢ * p read-unencumbered

private

  read-unencumbered-1 : ([ & (val fZ) mut int ,, int  ])
                      , [ & (just (bank ([ free ,, loan imm ]) free)) ,, int none ]
                      ⊢ var fZ read-unencumbered
  read-unencumbered-1 = var (& (nomuts (free ∷ imm ∷ []) free))
  read-unencumbered-2 : ¬ (([ & (val fZ) mut int ,, int ])
                      , [ & (just (bank ([ free ,, loan mut ]) free)) ,, int none ]
                      ⊢ var fZ read-unencumbered)
  read-unencumbered-2 (var (& (nomuts (free ∷ () ∷ []) free)))
  read-unencumbered-3 : ([ ~ int ])
                      , [ ~ (just (bank ([ loan imm ]) free , int (just (bank-def _)))) ]
                      ⊢ * (var fZ) read-unencumbered
  read-unencumbered-3 = * (var (~ (nomuts (imm ∷ []) free))) (*~ var) (int (nomuts (free ∷ []) free))

record _,_⊢_readable {#x} (Γ : Cxt #x) (Δ : State #x) (p : Path #x) : Set where
  constructor can-read
  field
    deep-init : Γ , Δ ⊢ p deep
    unrestricted : Γ , Δ ⊢ p read-unrestricted
    unencumbered : Γ , Δ ⊢ p read-unencumbered

data write-unrestricted {#x} : Shape #x → Set where    
  int : ∀ {b} → Unborrowed b → write-unrestricted (int (just b))
  ~ : ∀ {b δ} → Unborrowed b → write-unrestricted δ → write-unrestricted (~ (just (b , δ)))
  & : ∀ {b} → Unborrowed b → write-unrestricted (& (just b))
  opt : ∀ {b} → Unborrowed b → write-unrestricted (opt (just b))

record _,_⊢_write-unrestricted {#x} (Γ : Cxt #x) (Δ : State #x) (p : Path #x) : Set where
  constructor write-unres
  field
    {δ} : Shape #x
    shallow : Γ , Δ ⊢ p ⇒ δ shape
    unrestricted : write-unrestricted δ

data write-unencumbered {#x} : Shape #x → Set where
  int : ∀ {b} → Unborrowed b → write-unencumbered (int (just b))
  ~ : ∀ {b δ} → Unborrowed b → write-unencumbered (~ (just (b , δ)))
  & : ∀ {b} → Unborrowed b → write-unencumbered (& (just b))
  opt : ∀ {b} → Unborrowed b → write-unencumbered (opt (just b))

data _,_⊢_write-unencumbered {#x} (Γ : Cxt #x) (Δ : State #x) : Path #x → Set where
  var : ∀ {x} → write-unencumbered (Δ ! x) → Γ , Δ ⊢ var x write-unencumbered
  * : ∀ {p δ}
    → Γ , Δ ⊢ p write-unencumbered
    → Γ , Δ ⊢ * p ⇒ δ shape
    → write-unencumbered δ
    → Γ , Δ ⊢ * p write-unencumbered

record _,_⊢_writeable {#x} (Γ : Cxt #x) (Δ : State #x) (p : Path #x) : Set where
  constructor can-write
  field
    deep-init : Γ , Δ ⊢ p deep
    unrestricted : Γ , Δ ⊢ p write-unrestricted
    unencumbered : Γ , Δ ⊢ p write-unencumbered

record _,_⊢_movable {#x} (Γ : Cxt #x) (Δ : State #x) (p : Path #x) : Set where
  constructor can-move
  field
    owned : Γ ⊢ p owned
    writable : Γ , Δ ⊢ p writeable

data _,_⊢_∶_⇒_ {#x} : Cxt #x → State #x → Path #x → Type #x → State #x → Set where
  copy : ∀ {Γ Δ p τ}
       -- copyable type
       → Γ ⊢ p ∶ τ path
       → τ Copy
       -- can read path
       → Γ , Δ ⊢ p readable
       → Γ , Δ ⊢ p ∶ τ ⇒ Δ
  move : ∀ {Γ Δ p τ Δ′}
       -- noncopyable type
       → Γ ⊢ p ∶ τ path
       → τ Affine
       -- can move from path
       → Γ , Δ ⊢ p movable
       → Γ , Δ ⊢ p ⇒ Δ′ void
       → Γ , Δ ⊢ p ∶ τ ⇒ Δ′

use-to-path : ∀ {#x Δ Δ′ p τ} {Γ : Cxt #x}
            → Γ , Δ ⊢ p ∶ τ ⇒ Δ′
            → Γ ⊢ p ∶ τ path
use-to-path (copy p∶τ _ _) = p∶τ
use-to-path (move p∶τ _ _ _) = p∶τ

data _,_⊢_∶_⇒_many {#x} : ∀ {n} → Cxt #x → State #x → Vec (Path #x) n
                           → Vec (Type #x) n → State #x → Set where
  [] : ∀ {Γ Δ} → Γ , Δ ⊢ [] ∶ [] ⇒ Δ many
  _∷_ : ∀ {n Γ p ps τ Δ₀ Δ₁ Δ₂} {τs : Vec (Type #x) n}
      → Γ , Δ₀ ⊢ p ∶ τ ⇒ Δ₁
      → Γ , Δ₁ ⊢ ps ∶ τs ⇒ Δ₂ many
      → Γ , Δ₀ ⊢ p ∷ ps ∶ τ ∷ τs ⇒ Δ₂ many
