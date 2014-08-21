open import Common
open import Type
open import Layout
open import Route
open import Shape
open import Loan

module Path where

-- Paths are indexed by the number of variables in scope.
data Path (#x : ℕ) : Set where
  -- Variables are represented as elements of the finite set of #x elements (i.e. De Bruijn indicies)
  var : Fin #x → Path #x
  * : Path #x → Path #x

  {-
var-inj : ∀ {#x} {x₁ x₂ : Fin #x} → var x₁ ≡ var x₂ → x₁ ≡ x₂ 
var-inj refl = refl
path-*-inj : ∀ {#x} {p₁ p₂ : Path #x} → (the (Path #x) (* p₁)) ≡ * p₂ → p₁ ≡ p₂
path-*-inj refl = refl

_=path=_ : ∀ {#x} (p₁ p₂ : Path #x) → Dec (p₁ ≡ p₂)
var x₁ =path= var x₂ with x₁ == x₂
var x₁ =path= var .x₁ | yes refl = yes refl
var x₁ =path= var x₂ | no neq = no (neq ∘ var-inj)
var x₁ =path= * p₂ = no (λ ())
* p₁ =path= var x₂ = no (λ ())
* p₁ =path= * p₂ with p₁ =path= p₂
* p₁ =path= * .p₁ | yes refl = yes refl
* p₁ =path= * p₂ | no neq = no (neq ∘ path-*-inj)

EqPath : ∀ {#x} → Eq (Path #x)
EqPath = record { _==_ = _=path=_ }
-}

-- upshifting for the #x index of Paths
↑-var-p : ∀ {#x} → (amt : ℕ) → (cut : Fin #x) → Path #x → Path (plus amt #x)
↑-var-p d c (var x) with asℕ x <? asℕ c
↑-var-p d c (var x) | yes x<c = var (expand′ d x)
↑-var-p d c (var x) | no  x≥c = var (raise d x)
↑-var-p d c (* p) = * (↑-var-p d c p)

↑-var-p′ : ∀ {#x} → ℕ → Path #x → Path (S #x)
↑-var-p′ c (var x) with asℕ x <? c
↑-var-p′ c (var x) | yes x<c = var (expand′ 1 x)
↑-var-p′ c (var x) | no  x≥c = var (raise 1 x)
↑-var-p′ c (* p) = * (↑-var-p′ c p)

test-↑-1 : ↑-var-p′ {1} 0 (var fZ) ≡ var (fin 1)
test-↑-1 = refl
test-↑-2 : ↑-var-p′ {2} 1 (var fZ) ≡ var (fin 0)
test-↑-2 = refl

↑-var-p′′ : ∀ {#x} → (d : ℕ) → ℕ → Path #x → Path (plus #x d)
↑-var-p′′ d c (var x) with asℕ x <? c
↑-var-p′′ d c (var x) | yes x<c = var (expand d x)
↑-var-p′′ d c (var x) | no  x≥c = var (raise′ d x)
↑-var-p′′ d c (* p) = * (↑-var-p′′ d c p)

↑-var-p′′′ : ∀ {#x} → (d : ℕ) → ℕ → Path #x → Path (plus d #x)
↑-var-p′′′ {#x} d c p rewrite plus-comm d #x = ↑-var-p′′ d c p

-- Typing for Paths. Given a mapping from variables to types (i.e. a Vector of Types #x long).
data _⊢_∶_ {#x #ℓ} : Vec (Type #ℓ) #x → Path #x → Type #ℓ → Set where
  var : ∀ {Γ x} → Γ ⊢ var x ∶ (Γ ! x)
  *~ : ∀ {Γ p τ} → Γ ⊢ p ∶ ~ τ → Γ ⊢ * p ∶ τ
  *& : ∀ {Γ p ℓ μ τ} → Γ ⊢ p ∶ & ℓ μ τ → Γ ⊢ * p ∶ τ

test-lvtype-1 : ([ int {0} ,, int ]) ⊢ var (fin 0) ∶ int
test-lvtype-1 = var
test-lvtype-2 : ([ int {0} ,, int ]) ⊢ var (fin 1) ∶ int
test-lvtype-2 = var

-- Evaluation for Paths. Determines a Route into corresponding to the Path.
data _,_,_⊢_⟶_ {#x #a #ℓ} : Vec (Type #ℓ) #x
                        → Vec (Fin #a) #x
                        → Vec (Layout #a) #a
                        → Path #x
                        → Route #a
                        → Set where
  var : ∀ {T V H x} → T , V , H ⊢ var x ⟶ alloc (V ! x)
  * : ∀ {T V H p r} → T , V , H ⊢ p ⟶ r → T , V , H ⊢ * p ⟶ * r

test-lvaddr-1 : ([ int {0} ,, int ])
              , [ fin 1 ,, fin 0 ]
              , [ int (val 0) ,, int (val 1) ]
              ⊢ var (fin 1) ⟶ alloc (fin 0)
test-lvaddr-1 = var

-- Examining the Shape information for a Path. Requires the prefix of the path be shallowly initialized.
data _⊢_∶_shape {#x #ℓ} (Δ : Vec (Shape #ℓ) #x) : Path #x → Shape #ℓ → Set where
  var : ∀ {x} → Δ ⊢ var x ∶ Δ ! x shape
  *~ : ∀ {p B δ} → Δ ⊢ p ∶ ~ (init B δ) shape → Δ ⊢ * p ∶ δ shape
  *& : ∀ {p B τ} → Δ ⊢ p ∶ & (init B τ) shape → Δ ⊢ * p ∶ init-t τ shape

-- A Path is deeply initialized if it has a Full shape.
_⊢_deep : ∀ {#x #ℓ} → Vec (Shape #ℓ) #x → Path #x → Set
Δ ⊢ p deep = Σ[ δ ∈ Shape _ ] Δ ⊢ p ∶ δ shape × δ Full

test-deep-1 : ([ int {0} (init (bank-def _) tt) ]) ⊢ var fZ deep
test-deep-1 = int (init (bank [] free) tt) , (var , int)
test-deep-2 : ¬ (([ int {0} void ]) ⊢ var fZ deep)
test-deep-2 (.(int void) , (var , ()))

-- Setting the Shape information for a Path. Will initialize a prefix of the Path.
data _⊢_≔_⇒_shape {#x #ℓ} : Vec (Shape #ℓ) #x → Path #x → Shape #ℓ → Vec (Shape #ℓ) #x → Set where
  var : ∀ {Δ x δ} → Δ ⊢ var x ≔ δ ⇒ set Δ x δ shape
  * : ∀ {Δ p B δ δ′ Δ′}
    → Δ ⊢ p ∶ ~ δ′ shape
    → Δ ⊢ p ≔ ~ (init B δ) ⇒ Δ′ shape
    → Δ ⊢ * p ≔ δ ⇒ Δ′ shape
  -- We do not need a version that goes through & pointers because & shapes do not contain shapes

-- Initialize a Path (set it's Shape to be the fully initialized Shape for its Type)
_,_⊢_⇒_init : ∀ {#x #ℓ} → Vec (Type #ℓ) #x → Vec (Shape #ℓ) #x → Path #x → Vec (Shape #ℓ) #x → Set
Γ , Δ ⊢ p ⇒ Δ′ init = Σ[ τ ∈ Type _ ] Γ ⊢ p ∶ τ × (Δ ⊢ p ≔ init-t τ ⇒ Δ′ shape)

test-init-1 : ([ int {0} ])
            , [ int void ]
            ⊢ var fZ
            ⇒ [ int (init (bank-def _) tt) ] init
test-init-1 = int , (var , var)
test-init-2 : ([ ~ {0} int ])
            , [ ~ void ]
            ⊢ * (var fZ)
            ⇒ [ ~ (init (bank-def _) (int (init (bank-def _) tt))) ] init
test-init-2 = int , (*~ var , * var var)
test-init-3 : ([ ~ {0} int ])
            , [ ~ (init (bank-def _) (int void)) ]
            ⊢ * (var fZ)
            ⇒ [ ~ (init (bank-def _) (int (init (bank-def _) tt))) ] init
test-init-3 = int , (*~ var , * var var)

-- Deinitialize a Path (set it's Shape to be the fully uninitlaized Shape for its Type)
_,_⊢_⇒_deinit : ∀ {#x #ℓ} → Vec (Type #ℓ) #x → Vec (Shape #ℓ) #x → Path #x → Vec (Shape #ℓ) #x → Set
Γ , Δ ⊢ p ⇒ Δ′ deinit = Σ[ τ ∈ Type _ ] Γ ⊢ p ∶ τ × (Δ ⊢ p ≔ void-t τ ⇒ Δ′ shape)

test-deinit-1 : ([ int {0} ])
              , [ int (init (bank-def _) tt) ]
              ⊢ var fZ
              ⇒ [ int void ] deinit
test-deinit-1 = int , (var , var)
test-deinit-2 : ([ ~ {0} int ])
              , [ ~ (init (bank-def _) (int (init (bank-def _) tt))) ]
              ⊢ var fZ
              ⇒ [ ~ void ] deinit
test-deinit-2 = ~ int , (var , var)
test-deinit-3 : ([ ~ {0} int ])
              , [ ~ (init (bank-def _) (int (init (bank-def _) tt))) ]
              ⊢ * (var fZ)
              ⇒ [ ~ (init (bank-def _) (int void)) ] deinit
test-deinit-3 = int , (*~ var , * var var)

-- We can initialize a Path if the prefix of the path is initialized and the Shape of the Path is full uninitialized.
_⊢_can-init : ∀ {#x #ℓ} → Vec (Shape #ℓ) #x → Path #x → Set
Δ ⊢ p can-init = Σ[ δ ∈ Shape _ ] Δ ⊢ p ∶ δ shape × δ Empty

-- Judgment for accessing a Path
record _,_⊢_access {#x #ℓ} (Γ : Vec (Type #ℓ) #x)
                        (Δ : Vec (Shape #ℓ) #x)
                        (p : Path #x) : Set where
  constructor can-access
  field
    deep-init : Δ ⊢ p deep
    --unrestricted : {!!} -- TODO don't have loans yet
    --unborrowed : {!!} -- TODO don't have loans yet

-- Judgment for reading a Path
_,_⊢_read : ∀ {#x #ℓ} → Vec (Type #ℓ) #x → Vec (Shape #ℓ) #x → Path #x → Set
Γ , Δ ⊢ p read = Γ , Δ ⊢ p access

-- Judgment for writing a Path
_,_⊢_write : ∀ {#x #ℓ} → Vec (Type #ℓ) #x → Vec (Shape #ℓ) #x → Path #x → Set
Γ , Δ ⊢ p write = Γ , Δ ⊢ p access

-- Judgment for whether a Path owns itself
data _⊢_owned {#x #ℓ} (Γ : Vec (Type #ℓ) #x) : Path #x → Set where
  var : ∀ {x} → Γ ⊢ var x owned
  *~ : ∀ {p τ} → Γ ⊢ p ∶ ~ τ → Γ ⊢ * p owned

test-owned-1 : ([ ~ {0} int ]) ⊢ var fZ owned
test-owned-1 = var
test-owned-2 : ([ ~ {0} int ]) ⊢ * (var fZ) owned
test-owned-2 = *~ var

-- Judgment for moving a Path
_,_⊢_move : ∀ {#x #ℓ} → Vec (Type #ℓ) #x → Vec (Shape #ℓ) #x → Path #x → Set
Γ , Δ ⊢ p move = Γ ⊢ p owned × Γ , Δ ⊢ p write

-- Judgment for whether it is ok to use a Path
data _,_⊢_∶_,_use {#x #ℓ} : Vec (Type #ℓ) #x
                     → Vec (Shape #ℓ) #x
                     → Path #x
                     → Type #ℓ
                     → Vec (Shape #ℓ) #x
                     → Set where
  -- Copyable types do not change initialization state
  copy : ∀ {Γ Δ p τ}
       → Γ ⊢ p ∶ τ
       → τ Copy
       → Γ , Δ ⊢ p read
       → Γ , Δ ⊢ p ∶ τ , Δ use
  -- Affine types deinitialize themselves
  move : ∀ {Γ Δ p τ Δ′}
       → Γ ⊢ p ∶ τ
       → τ Affine
       → Γ , Δ ⊢ p move
       → Γ , Δ ⊢ p ⇒ Δ′ deinit
       → Γ , Δ ⊢ p ∶ τ , Δ′ use

-- Iterated use of Paths
data _,_⊢_∶_,_use-many {#x #ℓ} : ∀ {n} → Vec (Type #ℓ) #x → Vec (Shape #ℓ) #x
                            → Vec (Path #x) n → Vec (Type #ℓ) n → Vec (Shape #ℓ) #x → Set where
   [] : ∀ {Γ Δ} → Γ , Δ ⊢ [] ∶ [] , Δ use-many
   _∷_ : ∀ {Γ Δ₀ Δ₁ Δ₂ p τ n} {ps : Vec (Path #x) n} {τs : Vec (Type #ℓ) n}
       → Γ , Δ₀ ⊢ p ∶ τ , Δ₁ use
       → Γ , Δ₁ ⊢ ps ∶ τs , Δ₂ use-many
       → Γ , Δ₀ ⊢ p ∷ ps ∶ τ ∷ τs , Δ₂ use-many

-- Checking whether a Path is uninitialized
-- (potentially has an uninitialized prefix, which makes getting the Shape impossible)
data _⊢_uninit {#x #ℓ} (Δ : Vec (Shape #ℓ) #x) : Path #x → Set where
  var : ∀ {x} → (Δ ! x) Empty → Δ ⊢ var x uninit
  * : ∀ {p δ} → Δ ⊢ p ∶ δ shape → δ Empty → Δ ⊢ * p uninit
  *⊥ : ∀ {p} → Δ ⊢ p uninit → Δ ⊢ * p uninit
  
-- Checking whether a path has been dropped if it needs to be dropped.
data _∣_,_⊢_dropped {#ℓ} : ∀ #x → Vec (Type #ℓ) #x → Vec (Shape #ℓ) #x → Path #x → Set where
  dropped-Δ : ∀ {#x Γ Δ p} → Δ ⊢ p uninit → #x ∣ Γ , Δ ⊢ p dropped
  dropped-copy : ∀ {#x Γ Δ p τ} → Γ ⊢ p ∶ τ → τ ¬Drop → #x ∣ Γ , Δ ⊢ p dropped

{-
data _prefixof_ {#x} : Path #x → Path #x → Set where
  --var : ∀ {x₁ x₂} → x₁ ≡ x₂ → var x₁ prefixof var x₂
  var : ∀ {x} → var x prefixof var x

prefix-var-≡ : ∀ {#x} {x₁ x₂ : Fin #x} → var x₁ prefixof var x₂ → x₁ ≡ x₂
prefix-var-≡ var = refl

_prefixof?_ : ∀ {#x} (p₁ p₂ : Path #x) → Dec (p₁ prefixof p₂)
var x₁ prefixof? var x₂ with x₁ == x₂
var x₁ prefixof? var .x₁ | yes refl = yes var
var x₁ prefixof? var x₂ | no neq = no (neq ∘ prefix-var-≡)

data _∩_ {#x} : Path #x → Path #x → Set where
  var : ∀ {x₁ x₂} → x₁ ≡ x₂ → var x₁ ∩ var x₂
  -}

  {-
_⊢_shallow : ∀ {#x} → L.List (Path #x) → Path #x → Set
Δ ⊢ p shallow = L.All (¬ ∘ (λ p′ → p′ prefixof p)) Δ

test-shallow-1 : L.[] ⊢ var {1} fZ shallow
test-shallow-1 = L.[]
test-shallow-2 : ¬ ((L.[ var {1} fZ L.]) ⊢ var fZ shallow)
test-shallow-2 (pf L.∷ L.[]) = pf var
--test-shallow-2 (pf L.∷ L.[]) = pf (var refl)
-}

{-
_⊢_deep : ∀ {#x} → L.List (Path #x) → Path #x → Set
Δ ⊢ p deep = L.All (¬ ∘ _∩_ p) Δ

test-deep-1 : L.[] ⊢ var {1} fZ deep
test-deep-1 = L.[]
test-deep-2 : ¬ ((L.[ var {1} fZ L.]) ⊢ var fZ deep)
test-deep-2 (pf L.∷ L.[]) = pf (var refl)
-}

{-
data _,_⊢_can-init {#x} : Vec Type #x → L.List (Path #x) → Path #x → Set where
  var : ∀ {Γ Δ x} → var x L.∈ Δ → Γ , Δ ⊢ var x can-init

record _,_⊢_access {#x} (Γ : Vec Type #x)
                          (Δ : L.List (Path #x))
                          (p : Path #x) : Set where
  constructor can-access
  field
    deep-init : Δ ⊢ p deep
    --unrestricted : {!!} -- TODO don't have loans yet
    --unborrowed : {!!} -- TODO don't have loans yet

_,_⊢_read : ∀ {#x} → Vec Type #x → L.List (Path #x) → Path #x → Set
Γ , Δ ⊢ p read = Γ , Δ ⊢ p access

data _,_⊢_∶_,_use {#x} : Vec Type #x
                     → L.List (Path #x)
                     → Path #x
                     → Type
                     → L.List (Path #x)
                     → Set where
  copy : ∀ {Γ Δ p τ}
       → Γ ⊢ p ∶ τ
       → τ Copy
       → Γ , Δ ⊢ p read
       → Γ , Δ ⊢ p ∶ τ , Δ use
  -- TODO move
-}

{-
init-Δ : ∀ {#x} → L.List (Path #x) → Path #x → L.List (Path #x)
init-Δ L.[] p = L.[]
init-Δ (pΔ L.∷ Δ) p with p prefixof? pΔ
init-Δ (pΔ L.∷ Δ) p | yes H = init-Δ Δ p
init-Δ (pΔ L.∷ Δ) p | no ¬H = pΔ L.∷ init-Δ Δ p

test-init-Δ-1 : init-Δ L.[] (var {2} fZ) ≡ L.[]
test-init-Δ-1 = refl
test-init-Δ-2 : init-Δ (L.[ var fZ L.]) (var {2} fZ) ≡ L.[]
test-init-Δ-2 = refl
test-init-Δ-3 : init-Δ (L.[ var (fin 1) L.]) (var {2} fZ) ≡ (L.[ var (fin 1) L.])
test-init-Δ-3 = refl
test-init-Δ-4 : init-Δ (L.[ var (fin 1) L.,, var fZ L.]) (var {2} fZ) ≡ (L.[ var (fin 1) L.])
test-init-Δ-4 = refl

data _∣_,_⊢_dropped : ∀ #x → Vec Type #x → L.List (Path #x) → Path #x → Set where
  dropped-Δ : ∀ {#x Γ Δ p} → p L.∈ Δ → #x ∣ Γ , Δ ⊢ p dropped
  dropped-copy : ∀ {#x Γ Δ p τ} → Γ ⊢ p ∶ τ → ¬ (τ Drop) → #x ∣ Γ , Δ ⊢ p dropped
-}
