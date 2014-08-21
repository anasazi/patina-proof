open import Common
open import Type
open import Loan
module Shape where

data Hole (A : Set) (#ℓ : ℕ) : Set where
  void : Hole A #ℓ
  init : Bank #ℓ → A → Hole A #ℓ

↑-#ℓ-h⊤ : ∀ {#ℓ} → (d : ℕ) → ℕ → Hole ⊤ #ℓ → Hole ⊤ (plus d #ℓ)
↑-#ℓ-h⊤ d c void = void
↑-#ℓ-h⊤ d c (init B tt) = init (↑-#ℓ-b d c B) tt

data ↓1-#ℓ-h⊤ {#ℓ} : ℕ → Hole ⊤ (S #ℓ) → Hole ⊤ #ℓ → Set where
  void : ∀ {c} → ↓1-#ℓ-h⊤ c void void
  init : ∀ {c B B′} → ↓1-#ℓ-b c B B′ → ↓1-#ℓ-h⊤ c (init B tt) (init B′ tt)

data Shape (#ℓ : ℕ) : Set where
  int : Hole ⊤ #ℓ → Shape #ℓ
  ~ : Hole (Shape #ℓ) #ℓ → Shape #ℓ
  & : Bank #ℓ → Type #ℓ → Shape #ℓ
  opt : Hole ⊤ #ℓ → Shape #ℓ
-- --  struct : ∀ {n} → Vec (Shape #x) n → Shape #x

↑-#ℓ-sh : ∀ {#ℓ} → (d : ℕ) → ℕ → Shape #ℓ → Shape (plus d #ℓ)

↑-#ℓ-hsh : ∀ {#ℓ} → (d : ℕ) → ℕ → Hole (Shape #ℓ) #ℓ → Hole (Shape (plus d #ℓ)) (plus d #ℓ)
↑-#ℓ-hsh d c void = void
↑-#ℓ-hsh d c (init B δ) = init (↑-#ℓ-b d c B) (↑-#ℓ-sh d c δ)

↑-#ℓ-sh d c (int h) = int (↑-#ℓ-h⊤ d c h)
↑-#ℓ-sh d c (~ h) = ~ (↑-#ℓ-hsh d c h)
-- ↑-#ℓ-sh d c (~ void) = ~ void
-- ↑-#ℓ-sh d c (~ (init δ)) = ~ (init (↑-#ℓ-sh d c δ))
↑-#ℓ-sh d c (& B τ) = & (↑-#ℓ-b d c B) (↑-#ℓ-t d c τ)
↑-#ℓ-sh d c (opt h) = opt (↑-#ℓ-h⊤ d c h)

data ↓1-#ℓ-sh {#ℓ} : ℕ → Shape (S #ℓ) → Shape #ℓ → Set

data ↓1-#ℓ-hsh {#ℓ} : ℕ → Hole (Shape (S #ℓ)) (S #ℓ) → Hole (Shape #ℓ) #ℓ → Set where
  void : ∀ {c} → ↓1-#ℓ-hsh c void void
  init : ∀ {c B B′ δ δ′} → ↓1-#ℓ-b c B B′ → ↓1-#ℓ-sh c δ δ′ → ↓1-#ℓ-hsh c (init B δ) (init B′ δ′)

data ↓1-#ℓ-sh {#ℓ} where
  int : ∀ {c h h′} → ↓1-#ℓ-h⊤ c h h′ → ↓1-#ℓ-sh c (int h) (int h′)
--   int : ∀ {c f} → ↓1-#ℓ-sh c (int f) (int f) 
  ~ : ∀ {c h h′} → ↓1-#ℓ-hsh c h h′ → ↓1-#ℓ-sh c (~ h) (~ h′)
--   ~ : ∀ {c δ δ′} → ↓1-#ℓ-sh c δ δ′ → ↓1-#ℓ-sh c (~ (init δ)) (~ (init δ′))
--   ~⊥ : ∀ {c} → ↓1-#ℓ-sh c (~ void) (~ void)
  & : ∀ {c B B′ τ τ′} → ↓1-#ℓ-b c B B′ → ↓1-#ℓ-t c τ τ′ → ↓1-#ℓ-sh c (& B τ) (& B′ τ′)
  opt : ∀ {c h h′} → ↓1-#ℓ-h⊤ c h h′ → ↓1-#ℓ-sh c (opt h) (opt h′)
--   opt : ∀ {c f} → ↓1-#ℓ-sh c (opt f) (opt f) 

data ↓1-#ℓ-shs {#ℓ} : ∀ {n} → ℕ → Vec (Shape (S #ℓ)) n → Vec (Shape #ℓ) n → Set where
  [] : ∀ {c} → ↓1-#ℓ-shs c [] []
  _∷_ : ∀ {n c δ δ′ δs} {δs′ : Vec (Shape #ℓ) n}
      → ↓1-#ℓ-sh c δ δ′
      → ↓1-#ℓ-shs c δs δs′
      → ↓1-#ℓ-shs c (δ ∷ δs) (δ′ ∷ δs′) 

init-t : ∀ {#ℓ} → Type #ℓ → Shape #ℓ
init-t int = int (init (bank-def _) tt)
init-t (~ τ) = ~ (init (bank-def _) (init-t τ))
init-t (& ℓ μ τ) = & (bank-def _) τ
init-t (opt τ) = opt (init (bank-def _) tt)

void-t : ∀ {#ℓ} → Type #ℓ → Shape #ℓ
void-t int = int void
void-t (~ τ) = ~ void
void-t (& ℓ μ τ) = & (bank-def _) τ
void-t (opt τ) = opt void

data _⊢_Dropped {#ℓ} : Type #ℓ → Shape #ℓ → Set where
  int : ∀ {B} → int ⊢ int (init B tt) Dropped
  ~ : ∀ {τ} → ~ τ ⊢ ~ void Dropped
  & : ∀ {B ℓ μ τ} → & ℓ μ τ ⊢ & B τ Dropped
  opt-copy : ∀ {B τ} → τ Copy → opt τ ⊢ opt (init B tt) Dropped
  opt-aff : ∀ {τ} → τ Affine → opt τ ⊢ opt void Dropped

-- dropped-t : ∀ {#ℓ} → Type #ℓ → Shape #ℓ
-- dropped-t int = int (init tt)
-- dropped-t (~ τ) = ~ void
-- dropped-t (& ℓ μ τ) = & τ
-- dropped-t (opt τ) with τ Drop?
-- dropped-t (opt τ) | inl τDrop = opt void
-- dropped-t (opt τ) | inr τ¬Drop = opt (init tt)

-- {-
-- dropped-copy-init : ∀ {#ℓ #Ł} (τ : Type #ℓ #Ł) → τ Copy → dropped-t τ ≡ init-t τ
-- dropped-copy-init .int int = refl
-- dropped-copy-init ._ &imm = refl
-- dropped-copy-init (opt τ) (opt copy) with τ Drop?
-- dropped-copy-init (opt τ) (opt copy) | inl drop = exfalso (drop×copy≡⊥ τ (drop , copy))
-- dropped-copy-init (opt τ) (opt copy) | inr ¬drop = refl

-- dropped-affine-void : ∀ {#ℓ #Ł} (τ : Type #ℓ #Ł) → τ Affine → dropped-t τ ≡ void-t τ
-- dropped-affine-void ._ ~Aff = refl
-- dropped-affine-void ._ &mut = refl
-- dropped-affine-void (opt τ) (opt aff) with τ Drop?
-- dropped-affine-void (opt τ) (opt aff) | inl drop = refl
-- dropped-affine-void (opt τ) (opt aff) | inr ¬drop = {!!}
-- -}

data _Full {#ℓ} : Shape #ℓ → Set where
  int : ∀ {B} → int (init B tt) Full
  ~ : ∀ {B δ} → δ Full → ~ (init B δ) Full
  & : ∀ {B τ} → & B τ Full
  opt : ∀ {B} → opt (init B tt) Full

data _Empty {#ℓ} : Shape #ℓ → Set where
  int : int void Empty
  ~ : ~ void Empty
  opt : opt void Empty


-- {-

-- data _⊢_∶_shape {#x} (Δ : Vec Shape #x) : Path #x → Shape → Set where
--   var : ∀ {x} → Δ ⊢ var x ∶ Δ ! x shape
-- --  *~ : ∀ {p δ} → Δ ⊢ p ∶ ~ (init δ) shape → Δ ⊢ * p ∶ δ shape
-- --  *& : ∀ {p τ} → Δ ⊢ p ∶ & τ shape → Δ ⊢ * p ∶ type->shape-init τ shape
-- --  ∙ : ∀ {n p f δs} → Δ ⊢ p ∶ struct δs shape → Δ ⊢ < n > p ∙ f ∶ δs ! f shape

-- {-
-- data _⊢_semi {#x} (Δ : Vec Shape #x) : Shape → Set where
--   int : Δ ⊢ int (init tt) semi
-- --  ~ : ∀ {δ} → Δ ⊢ ~ (init δ) semi
-- --  & : ∀ {τ} → Δ ⊢ & τ semi
--   opt : Δ ⊢ opt (init tt) semi
-- --  struct : ∀ {n} {δs : Vec (Shape #x) n} → Any (λ δ → Δ ⊢ δ semi) δs → Δ ⊢ struct δs semi

-- _⊢_shallow : ∀ {#x} → Vec Shape #x → Path #x → Set
-- Δ ⊢ p shallow = Σ[ δ ∈ Shape ] Δ ⊢ p ∶ δ shape × Δ ⊢ δ semi

-- test-shallow-1 : ([ int (init tt) ]) ⊢ var fZ shallow
-- test-shallow-1 = int (init tt) , (var , int)
-- test-shallow-2 : ¬ (([ int void ]) ⊢ var fZ shallow)
-- test-shallow-2 (.(int void) , (var , ()))
-- -}

-- data _Full : Shape → Set where
--   int : int (init tt) Full
-- --  ~ : ∀ {δ} → Δ ⊢ δ full → Δ ⊢ ~ (init δ) full
-- --  & : ∀ {τ} → Δ ⊢ & τ full
--   opt : opt (init tt) Full
-- --  struct : ∀ {n} {δs : Vec (Shape #x) n} → All (λ δ → Δ ⊢ δ full) δs → Δ ⊢ struct δs full

-- _⊢_deep : ∀ {#x} → Vec Shape #x → Path #x → Set
-- Δ ⊢ p deep = Σ[ δ ∈ Shape ] Δ ⊢ p ∶ δ shape × δ Full

-- test-deep-1 : ([ int (init tt) ]) ⊢ var fZ deep
-- test-deep-1 = int (init tt) , (var , int)
-- test-deep-2 : ¬ (([ int void ]) ⊢ var fZ deep)
-- test-deep-2 (.(int void) , (var , ()))

-- data _Empty  : Shape → Set where
--   int : int void Empty
-- --  ~ : Δ ⊢ ~ void empty
--   opt : opt void Empty
-- --  struct : ∀ {n} {δs : Vec (Shape #x) n} → All (λ δ → Δ ⊢ δ empty) δs → Δ ⊢ struct δs empty

-- _⊢_can-init : ∀ {#x} → Vec Shape #x → Path #x → Set
-- Δ ⊢ p can-init = Σ[ δ ∈ Shape ] Δ ⊢ p ∶ δ shape × δ Empty

-- record _,_⊢_access {#x} (Γ : Vec Type #x)
--                         (Δ : Vec Shape #x)
--                         (p : Path #x) : Set where
--   constructor can-access
--   field
--     deep-init : Δ ⊢ p deep
--     --unrestricted : {!!} -- TODO don't have loans yet
--     --unborrowed : {!!} -- TODO don't have loans yet

-- _,_⊢_read : ∀ {#x} → Vec Type #x → Vec Shape #x → Path #x → Set
-- Γ , Δ ⊢ p read = Γ , Δ ⊢ p access

-- data _,_⊢_∶_,_use {#x} : Vec Type #x
--                      → Vec Shape #x
--                      → Path #x
--                      → Type
--                      → Vec Shape #x
--                      → Set where
--   copy : ∀ {Γ Δ p τ}
--        → Γ ⊢ p ∶ τ
--        → τ Copy
--        → Γ , Δ ⊢ p read
--        → Γ , Δ ⊢ p ∶ τ , Δ use
--   -- TODO move

-- data _⊢_uninit {#x} (Δ : Vec Shape #x) : Path #x → Set where
--   var : ∀ {x} → (Δ ! x) Empty → Δ ⊢ var x uninit
-- --  * : ∀ {p} → Δ ⊢ p uninit → Δ ⊢ * p uninit
  
-- data _∣_,_⊢_dropped : ∀ #x → Vec Type #x → Vec Shape #x → Path #x → Set where
--   dropped-Δ : ∀ {#x Γ Δ p} → Δ ⊢ p uninit → #x ∣ Γ , Δ ⊢ p dropped
--   dropped-copy : ∀ {#x Γ Δ p τ} → Γ ⊢ p ∶ τ → ¬ (τ Drop) → #x ∣ Γ , Δ ⊢ p dropped

--   -}
