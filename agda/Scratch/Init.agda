open import Common
module Init where

data Type : Set where
  int : Type
  ~ : Type → Type
  & : Type → Type
  opt : Type → Type
  struct : ∀ {n} → Vec Type n → Type

data Path (#x : ℕ) : Set where
  var : Fin #x → Path #x
  * : Path #x → Path #x
  <_>_∙_ : (n : ℕ) → Path #x → Fin n → Path #x

data Flag (A : Set) : Set where
  void : Flag A
  init : A → Flag A

data Shape (#x : ℕ) : Set where
  int : Flag ⊤ → Shape #x
  ~ : Flag (Shape #x) → Shape #x
  & : Type → Shape #x
  opt : Flag ⊤ → Shape #x
  struct : ∀ {n} → Vec (Shape #x) n → Shape #x

type->shape-init-many : ∀ {#x n} → Vec Type n → Vec (Shape #x) n

type->shape-init : ∀ {#x} → Type → Shape #x
type->shape-init int = int (init tt)
type->shape-init (~ τ) = ~ (init (type->shape-init τ))
type->shape-init (& τ) = & τ
type->shape-init (opt τ) = opt (init tt)
type->shape-init (struct τs) = struct (type->shape-init-many τs)

type->shape-init-many [] = []
type->shape-init-many (τ ∷ τs) = type->shape-init τ ∷ type->shape-init-many τs

type->shape-void-many : ∀ {#x n} → Vec Type n → Vec (Shape #x) n

type->shape-void : ∀ {#x} → Type → Shape #x
type->shape-void int = int void
type->shape-void (~ τ) = ~ void
type->shape-void (& τ) = & τ
type->shape-void (opt τ) = opt void
type->shape-void (struct τs) = struct (type->shape-void-many τs)

type->shape-void-many [] = []
type->shape-void-many (τ ∷ τs) = type->shape-void τ ∷ type->shape-void-many τs

data _⊢_∶_shape {#x} (Δ : Vec (Shape #x) #x) : Path #x → Shape #x → Set where
  var : ∀ {x} → Δ ⊢ var x ∶ Δ ! x shape
  *~ : ∀ {p δ} → Δ ⊢ p ∶ ~ (init δ) shape → Δ ⊢ * p ∶ δ shape
  *& : ∀ {p τ} → Δ ⊢ p ∶ & τ shape → Δ ⊢ * p ∶ type->shape-init τ shape
  ∙ : ∀ {n p f δs} → Δ ⊢ p ∶ struct δs shape → Δ ⊢ < n > p ∙ f ∶ δs ! f shape

data _⊢_semi {#x} (Δ : Vec (Shape #x) #x) : Shape #x → Set where
  int : Δ ⊢ int (init tt) semi
  ~ : ∀ {δ} → Δ ⊢ ~ (init δ) semi
  & : ∀ {τ} → Δ ⊢ & τ semi
  opt : Δ ⊢ opt (init tt) semi
  struct : ∀ {n} {δs : Vec (Shape #x) n} → Any (λ δ → Δ ⊢ δ semi) δs → Δ ⊢ struct δs semi

_⊢_shallow : ∀ {#x} → Vec (Shape #x) #x → Path #x → Set
Δ ⊢ p shallow = Σ[ δ ∈ Shape _ ] Δ ⊢ p ∶ δ shape × Δ ⊢ δ semi

data _⊢_full {#x} (Δ : Vec (Shape #x) #x) : Shape #x → Set where
  int : Δ ⊢ int (init tt) full
  ~ : ∀ {δ} → Δ ⊢ δ full → Δ ⊢ ~ (init δ) full
  & : ∀ {τ} → Δ ⊢ & τ full
  opt : Δ ⊢ opt (init tt) full
  struct : ∀ {n} {δs : Vec (Shape #x) n} → All (λ δ → Δ ⊢ δ full) δs → Δ ⊢ struct δs full

_⊢_deep : ∀ {#x} → Vec (Shape #x) #x → Path #x → Set
Δ ⊢ p deep = Σ[ δ ∈ Shape _ ] Δ ⊢ p ∶ δ shape × Δ ⊢ δ full

data _⊢_empty {#x} (Δ : Vec (Shape #x) #x) : Shape #x → Set where
  int : Δ ⊢ int void empty
  ~ : Δ ⊢ ~ void empty
  opt : Δ ⊢ opt void empty
  struct : ∀ {n} {δs : Vec (Shape #x) n} → All (λ δ → Δ ⊢ δ empty) δs → Δ ⊢ struct δs empty

_⊢_uninit : ∀ {#x} → Vec (Shape #x) #x → Path #x → Set
Δ ⊢ p uninit = Σ[ δ ∈ Shape _ ] Δ ⊢ p ∶ δ shape × Δ ⊢ δ empty
