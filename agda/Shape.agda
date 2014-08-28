open import Common
open import Type
open import Path
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

data Shape (#ℓ : ℕ) : Set where
  int : Maybe (Bank #ℓ) → Shape #ℓ
  ~ : Maybe (Bank #ℓ × Shape #ℓ) → Shape #ℓ
  & : Maybe (Bank #ℓ) → Shape #ℓ
  opt : Maybe (Bank #ℓ) → Shape #ℓ

↑#ℓ-δ : ∀ {#ℓ} → ℕ → Shape #ℓ → Shape (S #ℓ)
↑#ℓ-δ c (int b?) = int (mmap (↑-#ℓ-b 1 c) b?)
↑#ℓ-δ c (~ b×δ?) = ~ (f b×δ?)
  where
  f : ∀ {#ℓ} → Maybe (Bank #ℓ × Shape #ℓ) → Maybe (Bank (S #ℓ) × Shape (S #ℓ))
  f none = none
  f (just (b , δ)) = just (↑-#ℓ-b 1 c b , ↑#ℓ-δ c δ)
↑#ℓ-δ c (& b?) = & (mmap (↑-#ℓ-b 1 c) b?)
↑#ℓ-δ c (opt b?) = opt (mmap (↑-#ℓ-b 1 c) b?)

data ↓#ℓ-δ {#ℓ} : ℕ → Shape (S #ℓ) → Shape #ℓ → Set where
  int : ∀ {c b? b′?} → mlift (↓1-#ℓ-b c) b? b′? → ↓#ℓ-δ c (int b?) (int b′?)
  ~⊥ : ∀ {c} → ↓#ℓ-δ c (~ none) (~ none)
  ~ : ∀ {c δ b δ′ b′} → ↓1-#ℓ-b c b b′ → ↓#ℓ-δ c δ δ′ → ↓#ℓ-δ c (~ (just (b , δ))) (~ (just (b′ , δ′)))
  & : ∀ {c b? b′?} → mlift (↓1-#ℓ-b c) b? b′? → ↓#ℓ-δ c (& b?) (& b′?)
  opt : ∀ {c b? b′?} → mlift (↓1-#ℓ-b c) b? b′? → ↓#ℓ-δ c (opt b?) (opt b′?)

State : ℕ → ℕ → Set
State #ℓ #x = Vec (Shape #ℓ) #x

data _⊢_shape {#ℓ} : Type #ℓ → Shape #ℓ → Set where
  int : ∀ {b?} → int ⊢ int b? shape
  ~ : ∀ {τ b δ} → τ ⊢ δ shape → ~ τ ⊢ ~ (just (b , δ)) shape
  ~⊥ : ∀ {τ} → ~ τ ⊢ ~ none shape
  & : ∀ {ℓ μ τ b?} → & ℓ μ τ ⊢ & b? shape
  opt : ∀ {τ b?} → opt τ ⊢ opt b? shape

_⊢_state : ∀ {#ℓ #x} → Context #ℓ #x → State #ℓ #x → Set
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

data _,_⊢_⇒_shape {#ℓ #x} (Γ : Context #ℓ #x) (Δ : State #ℓ #x) : Path #x → Shape #ℓ → Set where
  var : ∀ {x} → Γ , Δ ⊢ var x ⇒ Δ ! x shape
  *~ : ∀ {p δ b} → Γ , Δ ⊢ p ⇒ ~ (just (b , δ)) shape → Γ , Δ ⊢ * p ⇒ δ shape
  *& : ∀ {p b τ} → Γ , Δ ⊢ p ⇒ & (just b) shape → Γ ⊢ p ∶ τ → Γ , Δ ⊢ * p ⇒ init-shape τ shape

data _,_⊢_≔_⇒_shape {#ℓ #x} (Γ : Context #ℓ #x) (Δ : State #ℓ #x)
                    : Path #x → Shape #ℓ → State #ℓ #x → Set where
  var : ∀ {x δ} → Γ , Δ ⊢ var x ≔ δ ⇒ set Δ x δ shape
  * : ∀ {p δ δ′ Δ′}
    → Γ , Δ ⊢ p ⇒ ~ δ′ shape
    → Γ , Δ ⊢ p ≔ ~ (just (bank-def _ , δ)) ⇒ Δ′ shape
    → Γ , Δ ⊢ * p ≔ δ ⇒ Δ′ shape

_,_⊢_⇒_init : ∀ {#x #ℓ} → Context #ℓ #x → State #ℓ #x → Path #x → State #ℓ #x → Set
Γ , Δ ⊢ p ⇒ Δ′ init = Σ[ τ ∈ Type _ ] Γ ⊢ p ∶ τ × Γ , Δ ⊢ p ≔ init-shape τ ⇒ Δ′ shape

_,_⊢_⇒_void : ∀ {#x #ℓ} → Context #ℓ #x → State #ℓ #x → Path #x → State #ℓ #x → Set 
Γ , Δ ⊢ p ⇒ Δ′ void = Σ[ τ ∈ Type _ ] Γ ⊢ p ∶ τ × Γ , Δ ⊢ p ≔ void-shape τ ⇒ Δ′ shape

data _Full {#ℓ} : Shape #ℓ → Set where
  int : ∀ {b} → int (just b) Full
  ~ : ∀ {δ b} → δ Full → ~ (just (b , δ)) Full
  & : ∀ {b} → & (just b) Full
  opt : ∀ {b} → opt (just b) Full

_,_⊢_deep : ∀ {#ℓ #x} → Context #ℓ #x → State #ℓ #x → Path #x → Set
Γ , Δ ⊢ p deep = Σ[ δ ∈ Shape _ ] Γ , Δ ⊢ p ⇒ δ shape × δ Full

data _Empty {#ℓ} : Shape #ℓ → Set where
  int : int none Empty
  ~ : ~ none Empty
  & : & none Empty
  opt : opt none Empty

_,_⊢_can-init : ∀ {#ℓ #x} → Context #ℓ #x → State #ℓ #x → Path #x → Set
Γ , Δ ⊢ p can-init = Σ[ δ ∈ Shape _ ] Γ , Δ ⊢ p ⇒ δ shape × δ Empty

data _⊢_Dropped {#ℓ} : Type #ℓ → Shape #ℓ → Set where
  int : ∀ {b?} → int ⊢ int b? Dropped
  ~ : ∀ {τ} → ~ τ ⊢ ~ none Dropped
  & : ∀ {ℓ μ τ b?} → & ℓ μ τ ⊢ & b? Dropped
  opt-¬drop : ∀ {τ} → τ ¬Drop → opt τ ⊢ opt none Dropped
  opt-drop : ∀ {τ b?} → τ Drop → opt τ ⊢ opt b? Dropped

_,_⊢_dropped : ∀ {#ℓ #x} → Context #ℓ #x → State #ℓ #x → Path #x → Set
Γ , Δ ⊢ p dropped = Σ[ δ ∈ Shape _ ] Γ , Δ ⊢ p ⇒ δ shape × (Σ[ τ ∈ Type _ ] Γ ⊢ p ∶ τ × τ ⊢ δ Dropped)

data _,_⊢_∶_⇒_ {#x #ℓ} : Context #ℓ #x → State #ℓ #x → Path #x → Type #ℓ → State #ℓ #x → Set where
  copy : ∀ {Γ Δ p τ}
       -- copyable type
       → Γ ⊢ p ∶ τ
       → τ Copy
       -- can read path
       → Γ , Δ ⊢ p deep
       -- TODO not restricted for reading
       → Γ , Δ ⊢ p ∶ τ ⇒ Δ
  move : ∀ {Γ Δ p τ Δ′}
       -- noncopyable type
       → Γ ⊢ p ∶ τ
       → τ Affine
       -- can move from path
       → Γ ⊢ p owned
       → Γ , Δ ⊢ p deep
       -- TODO not restricted for moves
       → Γ , Δ ⊢ p ⇒ Δ′ void
       → Γ , Δ ⊢ p ∶ τ ⇒ Δ′

data _,_⊢_∶_⇒_many {#x #ℓ} : ∀ {n} → Context #ℓ #x → State #ℓ #x → Vec (Path #x) n
                           → Vec (Type #ℓ) n → State #ℓ #x → Set where
  [] : ∀ {Γ Δ} → Γ , Δ ⊢ [] ∶ [] ⇒ Δ many
  _∷_ : ∀ {n Γ p ps τ Δ₀ Δ₁ Δ₂} {τs : Vec (Type #ℓ) n}
      → Γ , Δ₀ ⊢ p ∶ τ ⇒ Δ₁
      → Γ , Δ₁ ⊢ ps ∶ τs ⇒ Δ₂ many
      → Γ , Δ₀ ⊢ p ∷ ps ∶ τ ∷ τs ⇒ Δ₂ many

-- data _⊢_⇒_shape {#ℓ #x #a} : State #ℓ #x #a → Path #x → Shape #ℓ #x #a → Set where
--   var : ∀ {x Δ Ψ} → (Δ , Ψ) ⊢ var x ⇒ Δ ! x shape
--   *~ : ∀ {p a b Δ Ψ} → (Δ , Ψ) ⊢ p ⇒ ~ (just (a , b)) shape → (Δ , Ψ) ⊢ * p ⇒ Ψ ! a shape
--   *& : ∀ {p p′ b Φ δ}
--      → Φ ⊢ p ⇒ & (just (p′ , b)) shape
--      → Φ ⊢ p′ ⇒ δ shape
--      → Φ ⊢ * p ⇒ δ shape

-- data _⊢_≔_⇒_shape {#ℓ #x #a} : State #ℓ #x #a → Path #x → Shape #ℓ #x #a → State #ℓ #x #a → Set where
--   var : ∀ {x δ Δ Ψ} → (Δ , Ψ) ⊢ var x ≔ δ ⇒ set Δ x δ , Ψ shape
--   *~ : ∀ {p a b δ Δ Ψ}
--      → (Δ , Ψ) ⊢ p ⇒ ~ (just (a , b)) shape
--      → (Δ , Ψ) ⊢ * p ≔ δ ⇒ Δ , set Ψ a δ shape
--   *& : ∀ {p p′ b Φ δ Φ′}
--      → Φ ⊢ p ⇒ & (just (p′ , b)) shape
--      → Φ ⊢ p′ ≔ δ ⇒ Φ′ shape
--      → Φ ⊢ * p ≔ δ ⇒ Φ′ shape

-- -- Typing for shapes
-- data _⊢_∶_shape {#x #a #ℓ} : State #ℓ #x #a → Shape #ℓ #x #a → Type #ℓ → Set where
--   int : ∀ {b? Φ} → Φ ⊢ int b? ∶ int shape
--   ~ : ∀ {τ a b Δ Ψ} → (Δ , Ψ) ⊢ Ψ ! a ∶ τ shape → (Δ , Ψ) ⊢ ~ (just (a , b)) ∶ ~ τ shape
--   ~⊥ : ∀ {τ Φ} → Φ ⊢ ~ none ∶ ~ τ shape
--   & : ∀ {p b ℓ μ τ Φ δ}
--     → Φ ⊢ p ⇒ δ shape
--     → Φ ⊢ δ ∶ τ shape
--     → Φ ⊢ & (just (p , b)) ∶ & ℓ μ τ shape
--   &⊥ : ∀ {ℓ μ τ Φ} → Φ ⊢ & none ∶ & ℓ μ τ shape
--   opt : ∀ {τ b? Φ} → Φ ⊢ opt τ b? ∶ opt τ shape

-- data _⊢_Full {#x #a #ℓ} : State #ℓ #x #a → Shape #ℓ #x #a → Set where
--   int : ∀ {Φ b} → Φ ⊢ int (just b) Full
--   ~ : ∀ {a b Δ Ψ} → (Δ , Ψ) ⊢ Ψ ! a Full → (Δ , Ψ) ⊢ ~ (just (a , b)) Full
--   & : ∀ {p b δ Φ} → Φ ⊢ p ⇒ δ shape → Φ ⊢ δ Full → Φ ⊢ & (just (p , b)) Full
--   opt : ∀ {τ b Φ} → Φ ⊢ opt τ (just b) Full

-- _⊢_can-use : ∀ {#x #a #ℓ} → State #ℓ #x #a → Path #x → Set
-- Φ ⊢ p can-use = Σ[ δ ∈ Shape _ _ _ ] Φ ⊢ p ⇒ δ shape × Φ ⊢ δ Full

-- data _Empty {#x #a #ℓ} : Shape #ℓ #x #a → Set where
--   int : int none Empty
--   ~ : ~ none Empty
--   & : & none Empty
--   opt : ∀ {τ} → opt τ none Empty

-- _⊢_can-init : ∀ {#x #a #ℓ} → State #ℓ #x #a → Path #x → Set
-- Φ ⊢ p can-init = Σ[ δ ∈ Shape _ _ _ ] Φ ⊢ p ⇒ δ shape × δ Empty

-- _⊢_to_⇒_shape : ∀ {#ℓ #x #a} → State #ℓ #x #a → Path #x → Path #x → State #ℓ #x #a → Set
-- Φ ⊢ src to dst ⇒ Φ′ shape = Σ[ δ ∈ Shape _ _ _ ] Φ ⊢ src ⇒ δ shape × Φ ⊢ dst ≔ δ ⇒ Φ′ shape

-- data _Dropped {#ℓ #x #a} : Shape #ℓ #x #a → Set where
--   int : ∀ {b?} → int b? Dropped
--   ~ : ~ none Dropped
--   & : ∀ {p×b?} → & p×b? Dropped
--   opt-¬drop : ∀ {τ b?} → τ ¬Drop → opt τ b? Dropped
--   opt-drop : ∀ {τ} → τ Drop → opt τ none Dropped

-- _⊢_dropped : ∀ {#ℓ #x #a} → State #ℓ #x #a → Path #x → Set
-- Φ ⊢ p dropped = Σ[ δ ∈ Shape _ _ _ ] Φ ⊢ p ⇒ δ shape × δ Dropped

--   {-
-- data Shape (#ℓ : ℕ) : Set where
--   int : Maybe (Bank #ℓ) → Shape #ℓ
--   ~ : Maybe (Shape #ℓ × Bank #ℓ) → Shape #ℓ
--   & : Type #ℓ → Maybe (Bank #ℓ) → Shape #ℓ
--   opt : Maybe (Type #ℓ × Bank #ℓ) → Shape #ℓ

-- ↑#ℓ-δ : ∀ {#ℓ} → ℕ → Shape #ℓ → Shape (S #ℓ)
-- ↑#ℓ-δ c (int b?) = int (mmap (↑-#ℓ-b 1 c) b?)
-- ↑#ℓ-δ c (~ δ×b?) = ~ (mmap (↑#ℓ-δ c *** ↑-#ℓ-b 1 c) δ×b?)
-- ↑#ℓ-δ c (& τ×b?) = & (mmap (↑#ℓ-τ c *** ↑-#ℓ-b 1 c) τ×b?)
-- ↑#ℓ-δ c (opt τ×b?) = opt (mmap (↑#ℓ-τ c *** ↑-#ℓ-b 1 c) τ×b?)

-- State : ℕ → ℕ → ℕ → Set
-- State #ℓ #x #a = Vec (Shape #ℓ) #x × Vec (Shape #ℓ) #a
-- -}

-- -- -- A hole that might store a value or be borrowed
-- -- data Hole (A : Set) (#ℓ : ℕ) : Set where
-- --   -- Uninitialized
-- --   void : Hole A #ℓ
-- --   -- Initialized
-- --   init : Bank #ℓ → A → Hole A #ℓ

-- -- -- up and downshift for Hole ⊤
-- -- ↑-#ℓ-h⊤ : ∀ {#ℓ} → (d : ℕ) → ℕ → Hole ⊤ #ℓ → Hole ⊤ (plus d #ℓ)
-- -- ↑-#ℓ-h⊤ d c void = void
-- -- ↑-#ℓ-h⊤ d c (init B tt) = init (↑-#ℓ-b d c B) tt

-- -- data ↓1-#ℓ-h⊤ {#ℓ} : ℕ → Hole ⊤ (S #ℓ) → Hole ⊤ #ℓ → Set where
-- --   void : ∀ {c} → ↓1-#ℓ-h⊤ c void void
-- --   init : ∀ {c B B′} → ↓1-#ℓ-b c B B′ → ↓1-#ℓ-h⊤ c (init B tt) (init B′ tt)

-- -- -- up and down shift for Hole Type
-- -- ↑-#ℓ-ht : ∀ {#ℓ} → (d : ℕ) → ℕ → Hole (Type #ℓ) #ℓ → Hole (Type (plus d #ℓ)) (plus d #ℓ)
-- -- ↑-#ℓ-ht d c void = void
-- -- ↑-#ℓ-ht d c (init B τ) = init (↑-#ℓ-b d c B) (↑-#ℓ-t d c τ)

-- -- data ↓-#ℓ-ht {#ℓ} : ℕ → Hole (Type (S #ℓ)) (S #ℓ) → Hole (Type #ℓ) #ℓ → Set where
-- --   void : ∀ {c} → ↓-#ℓ-ht c void void
-- --   init : ∀ {c B B′ τ τ′} → ↓1-#ℓ-b c B B′ → ↓1-#ℓ-t c τ τ′ → ↓-#ℓ-ht c (init B τ) (init B′ τ′)

-- -- -- Shapes are indexed by the lifetime relation b/c of their use of types
-- -- data Shape (#ℓ : ℕ) : Set where
-- --   -- Integers have no internal structure, so we simply have a Hole ⊤
-- --   int : Hole ⊤ #ℓ → Shape #ℓ
-- --   -- Unique pointers may point to some other Shape
-- --   ~ : Hole (Shape #ℓ) #ℓ → Shape #ℓ
-- --   -- Borrowed references may point to some Type (which we know is initialized thanks to the borrow)
-- --   & : Hole (Type #ℓ) #ℓ → Shape #ℓ
-- --   -- Options effectively have no internal structure to paths, so we simply use Hole ⊤
-- --   -- TODO maybe we should add an always present Type field for the type of the payload
-- --   -- might be useful for checking layouts
-- --   opt : Hole ⊤ #ℓ → Shape #ℓ
-- -- -- --  struct : ∀ {n} → Vec (Shape #x) n → Shape #x

-- -- -- A state is a vector of shapes (variables -> shapes)
-- -- State : ℕ → ℕ → Set
-- -- State #ℓ #x = Vec (Shape #ℓ) #x

-- -- -- up and downshift for Holes containing a Shape
-- -- ↑-#ℓ-sh : ∀ {#ℓ} → (d : ℕ) → ℕ → Shape #ℓ → Shape (plus d #ℓ)

-- -- ↑-#ℓ-hsh : ∀ {#ℓ} → (d : ℕ) → ℕ → Hole (Shape #ℓ) #ℓ → Hole (Shape (plus d #ℓ)) (plus d #ℓ)
-- -- ↑-#ℓ-hsh d c void = void
-- -- ↑-#ℓ-hsh d c (init B δ) = init (↑-#ℓ-b d c B) (↑-#ℓ-sh d c δ)

-- -- ↑-#ℓ-sh d c (int h) = int (↑-#ℓ-h⊤ d c h)
-- -- ↑-#ℓ-sh d c (~ h) = ~ (↑-#ℓ-hsh d c h)
-- -- ↑-#ℓ-sh d c (& h) = & (↑-#ℓ-ht d c h)
-- -- ↑-#ℓ-sh d c (opt h) = opt (↑-#ℓ-h⊤ d c h)

-- -- data ↓1-#ℓ-sh {#ℓ} : ℕ → Shape (S #ℓ) → Shape #ℓ → Set

-- -- data ↓1-#ℓ-hsh {#ℓ} : ℕ → Hole (Shape (S #ℓ)) (S #ℓ) → Hole (Shape #ℓ) #ℓ → Set where
-- --   void : ∀ {c} → ↓1-#ℓ-hsh c void void
-- --   init : ∀ {c B B′ δ δ′} → ↓1-#ℓ-b c B B′ → ↓1-#ℓ-sh c δ δ′ → ↓1-#ℓ-hsh c (init B δ) (init B′ δ′)

-- -- data ↓1-#ℓ-sh {#ℓ} where
-- --   int : ∀ {c h h′} → ↓1-#ℓ-h⊤ c h h′ → ↓1-#ℓ-sh c (int h) (int h′)
-- --   ~ : ∀ {c h h′} → ↓1-#ℓ-hsh c h h′ → ↓1-#ℓ-sh c (~ h) (~ h′)
-- --   & : ∀ {c h h′} → ↓-#ℓ-ht c h h′ → ↓1-#ℓ-sh c (& h) (& h′)
-- --   opt : ∀ {c h h′} → ↓1-#ℓ-h⊤ c h h′ → ↓1-#ℓ-sh c (opt h) (opt h′)

-- -- data ↓1-#ℓ-shs {#ℓ} : ∀ {n} → ℕ → Vec (Shape (S #ℓ)) n → Vec (Shape #ℓ) n → Set where
-- --   [] : ∀ {c} → ↓1-#ℓ-shs c [] []
-- --   _∷_ : ∀ {n c δ δ′ δs} {δs′ : Vec (Shape #ℓ) n}
-- --       → ↓1-#ℓ-sh c δ δ′
-- --       → ↓1-#ℓ-shs c δs δs′
-- --       → ↓1-#ℓ-shs c (δ ∷ δs) (δ′ ∷ δs′) 

-- -- -- A fully initialized Shape for some Type
-- -- init-t : ∀ {#ℓ} → Type #ℓ → Shape #ℓ
-- -- init-t int = int (init (bank-def _) tt)
-- -- init-t (~ τ) = ~ (init (bank-def _) (init-t τ))
-- -- init-t (& ℓ μ τ) = & (init (bank-def _) τ)
-- -- init-t (opt τ) = opt (init (bank-def _) tt)

-- -- -- A fully uninitialized Shape for some Type
-- -- void-t : ∀ {#ℓ} → Type #ℓ → Shape #ℓ
-- -- void-t int = int void
-- -- void-t (~ τ) = ~ void
-- -- void-t (& ℓ μ τ) = & void
-- -- void-t (opt τ) = opt void

-- -- -- A judgment whether a Shape is the "dropped" form for some Type
-- -- data _⊢_Dropped {#ℓ} : Type #ℓ → Shape #ℓ → Set where
-- --   -- ints can be initialized or not
-- --   int : ∀ {h} → int ⊢ int h Dropped
-- --   -- unique pointers must be uninitialized
-- --   ~ : ∀ {τ} → ~ τ ⊢ ~ void Dropped
-- --   -- borrowed pointers can be either
-- --   & : ∀ {ℓ μ τ h} → & ℓ μ τ ⊢ & h Dropped
-- --   -- options of ¬Drop types can be either
-- --   opt-¬drop : ∀ {τ h} → τ ¬Drop → opt τ ⊢ opt h Dropped
-- --   -- options of Drop types must be uninitialized
-- --   opt-drop : ∀ {τ} → τ Drop → opt τ ⊢ opt void Dropped

-- -- -- Predicate for whether a Shape is fully initialized (i.e. usable)
-- -- data _Full {#ℓ} : Shape #ℓ → Set where
-- --   int : ∀ {B} → int (init B tt) Full
-- --   ~ : ∀ {B δ} → δ Full → ~ (init B δ) Full
-- --   & : ∀ {B τ} → & (init B τ) Full
-- --   opt : ∀ {B} → opt (init B tt) Full

-- -- -- Predicate for whether a Shape is fully uninitialized (i.e. assignable)
-- -- data _Empty {#ℓ} : Shape #ℓ → Set where
-- --   int : int void Empty
-- --   ~ : ~ void Empty
-- --   -- TODO do we want to distinguish between &imm and &mut?
-- --   & : & void Empty
-- --   opt : opt void Empty

-- -- -- Typing for shapes
-- -- data _⊢_shape {#ℓ} : Type #ℓ → Shape #ℓ → Set where
-- --   int : ∀ {h} → int ⊢ int h shape
-- --   ~ : ∀ {B τ δ} → τ ⊢ δ shape → ~ τ ⊢ ~ (init B δ) shape
-- --   ~⊥ : ∀ {τ} → ~ τ ⊢ ~ void shape
-- --   & : ∀ {B ℓ μ τ} → & ℓ μ τ ⊢ & (init B τ) shape
-- --   &⊥ : ∀ {ℓ μ τ} → & ℓ μ τ ⊢ & void shape
-- --   opt : ∀ {h τ} → opt τ ⊢ opt h shape

-- -- -- Typing for states
-- -- _⊢_state : ∀ {#ℓ #x} → Context #ℓ #x → State #ℓ #x → Set
-- -- Γ ⊢ Δ state = All2 (λ τ δ → τ ⊢ δ shape) Γ Δ

-- -- -- The initial shape is well typed
-- -- init-t-well-typed : ∀ {#ℓ} → (τ : Type #ℓ) → τ ⊢ init-t τ shape
-- -- init-t-well-typed int = int
-- -- init-t-well-typed (~ τ) = ~ (init-t-well-typed τ)
-- -- init-t-well-typed (& ℓ μ τ) = &
-- -- init-t-well-typed (opt τ) = opt
