open import Common
open import Type
open import Loan
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

-- A hole that might store a value or be borrowed
data Hole (A : Set) (#ℓ : ℕ) : Set where
  -- Uninitialized
  void : Hole A #ℓ
  -- Initialized
  init : Bank #ℓ → A → Hole A #ℓ

-- up and downshift for Hole ⊤
↑-#ℓ-h⊤ : ∀ {#ℓ} → (d : ℕ) → ℕ → Hole ⊤ #ℓ → Hole ⊤ (plus d #ℓ)
↑-#ℓ-h⊤ d c void = void
↑-#ℓ-h⊤ d c (init B tt) = init (↑-#ℓ-b d c B) tt

data ↓1-#ℓ-h⊤ {#ℓ} : ℕ → Hole ⊤ (S #ℓ) → Hole ⊤ #ℓ → Set where
  void : ∀ {c} → ↓1-#ℓ-h⊤ c void void
  init : ∀ {c B B′} → ↓1-#ℓ-b c B B′ → ↓1-#ℓ-h⊤ c (init B tt) (init B′ tt)

-- up and down shift for Hole Type
↑-#ℓ-ht : ∀ {#ℓ} → (d : ℕ) → ℕ → Hole (Type #ℓ) #ℓ → Hole (Type (plus d #ℓ)) (plus d #ℓ)
↑-#ℓ-ht d c void = void
↑-#ℓ-ht d c (init B τ) = init (↑-#ℓ-b d c B) (↑-#ℓ-t d c τ)

data ↓-#ℓ-ht {#ℓ} : ℕ → Hole (Type (S #ℓ)) (S #ℓ) → Hole (Type #ℓ) #ℓ → Set where
  void : ∀ {c} → ↓-#ℓ-ht c void void
  init : ∀ {c B B′ τ τ′} → ↓1-#ℓ-b c B B′ → ↓1-#ℓ-t c τ τ′ → ↓-#ℓ-ht c (init B τ) (init B′ τ′)

-- Shapes are indexed by the lifetime relation b/c of their use of types
data Shape (#ℓ : ℕ) : Set where
  -- Integers have no internal structure, so we simply have a Hole ⊤
  int : Hole ⊤ #ℓ → Shape #ℓ
  -- Unique pointers may point to some other Shape
  ~ : Hole (Shape #ℓ) #ℓ → Shape #ℓ
  -- Borrowed references may point to some Type (which we know is initialized thanks to the borrow)
  & : Hole (Type #ℓ) #ℓ → Shape #ℓ
  -- Options effectively have no internal structure to paths, so we simply use Hole ⊤
  opt : Hole ⊤ #ℓ → Shape #ℓ
-- --  struct : ∀ {n} → Vec (Shape #x) n → Shape #x

-- up and downshift for Holes containing a Shape
↑-#ℓ-sh : ∀ {#ℓ} → (d : ℕ) → ℕ → Shape #ℓ → Shape (plus d #ℓ)

↑-#ℓ-hsh : ∀ {#ℓ} → (d : ℕ) → ℕ → Hole (Shape #ℓ) #ℓ → Hole (Shape (plus d #ℓ)) (plus d #ℓ)
↑-#ℓ-hsh d c void = void
↑-#ℓ-hsh d c (init B δ) = init (↑-#ℓ-b d c B) (↑-#ℓ-sh d c δ)

↑-#ℓ-sh d c (int h) = int (↑-#ℓ-h⊤ d c h)
↑-#ℓ-sh d c (~ h) = ~ (↑-#ℓ-hsh d c h)
↑-#ℓ-sh d c (& h) = & (↑-#ℓ-ht d c h)
↑-#ℓ-sh d c (opt h) = opt (↑-#ℓ-h⊤ d c h)

data ↓1-#ℓ-sh {#ℓ} : ℕ → Shape (S #ℓ) → Shape #ℓ → Set

data ↓1-#ℓ-hsh {#ℓ} : ℕ → Hole (Shape (S #ℓ)) (S #ℓ) → Hole (Shape #ℓ) #ℓ → Set where
  void : ∀ {c} → ↓1-#ℓ-hsh c void void
  init : ∀ {c B B′ δ δ′} → ↓1-#ℓ-b c B B′ → ↓1-#ℓ-sh c δ δ′ → ↓1-#ℓ-hsh c (init B δ) (init B′ δ′)

data ↓1-#ℓ-sh {#ℓ} where
  int : ∀ {c h h′} → ↓1-#ℓ-h⊤ c h h′ → ↓1-#ℓ-sh c (int h) (int h′)
  ~ : ∀ {c h h′} → ↓1-#ℓ-hsh c h h′ → ↓1-#ℓ-sh c (~ h) (~ h′)
  & : ∀ {c h h′} → ↓-#ℓ-ht c h h′ → ↓1-#ℓ-sh c (& h) (& h′)
  opt : ∀ {c h h′} → ↓1-#ℓ-h⊤ c h h′ → ↓1-#ℓ-sh c (opt h) (opt h′)

data ↓1-#ℓ-shs {#ℓ} : ∀ {n} → ℕ → Vec (Shape (S #ℓ)) n → Vec (Shape #ℓ) n → Set where
  [] : ∀ {c} → ↓1-#ℓ-shs c [] []
  _∷_ : ∀ {n c δ δ′ δs} {δs′ : Vec (Shape #ℓ) n}
      → ↓1-#ℓ-sh c δ δ′
      → ↓1-#ℓ-shs c δs δs′
      → ↓1-#ℓ-shs c (δ ∷ δs) (δ′ ∷ δs′) 

-- A fully initialized Shape for some Type
init-t : ∀ {#ℓ} → Type #ℓ → Shape #ℓ
init-t int = int (init (bank-def _) tt)
init-t (~ τ) = ~ (init (bank-def _) (init-t τ))
init-t (& ℓ μ τ) = & (init (bank-def _) τ)
init-t (opt τ) = opt (init (bank-def _) tt)

-- A fully uninitialized Shape for some Type
void-t : ∀ {#ℓ} → Type #ℓ → Shape #ℓ
void-t int = int void
void-t (~ τ) = ~ void
void-t (& ℓ μ τ) = & void
void-t (opt τ) = opt void

-- A judgment whether a Shape is the "dropped" form for some Type
data _⊢_Dropped {#ℓ} : Type #ℓ → Shape #ℓ → Set where
  -- ints can be initialized or not
  int : ∀ {h} → int ⊢ int h Dropped
  -- unique pointers must be uninitialized
  ~ : ∀ {τ} → ~ τ ⊢ ~ void Dropped
  -- borrowed pointers can be either
  & : ∀ {ℓ μ τ h} → & ℓ μ τ ⊢ & h Dropped
  -- options of ¬Drop types can be either
  opt-¬drop : ∀ {τ h} → τ ¬Drop → opt τ ⊢ opt h Dropped
  -- options of Drop types must be uninitialized
  opt-drop : ∀ {τ} → τ Drop → opt τ ⊢ opt void Dropped

-- Predicate for whether a Shape is fully initialized (i.e. usable)
data _Full {#ℓ} : Shape #ℓ → Set where
  int : ∀ {B} → int (init B tt) Full
  ~ : ∀ {B δ} → δ Full → ~ (init B δ) Full
  & : ∀ {B τ} → & (init B τ) Full
  opt : ∀ {B} → opt (init B tt) Full

-- Predicate for whether a Shape is fully uninitialized (i.e. assignable)
data _Empty {#ℓ} : Shape #ℓ → Set where
  int : int void Empty
  ~ : ~ void Empty
  -- TODO do we want to distinguish between &imm and &mut?
  & : & void Empty
  opt : opt void Empty
