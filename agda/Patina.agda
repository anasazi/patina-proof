module Patina where

-- general stuff
open import Function
open import Empty
open import Unit
open import Sum
open import Product
open import Decidable
open import Equality
open import Nat
open import List
--open import Vec

-- patina stuff
open import Id
open import Life

data Var : Set where
  cov : Var -- covariant
  con : Var -- contravariant
  inv : Var -- invariant

data Mut : Set where
  mut : Mut
  imm : Mut

module Types where

  data Type : Set where
    int : Type
    ~ : Type → Type
    Option : Type → Type
    & : Life → Mut → Type → Type
    -- using structural structs instead of nominal ones
    -- easier than dealing with lookups everywhere
    -- may end up chaning the well-formed checks since the Redex model does those on the declarations
    struct : List (Var × Life) → List Type → Type 

  -- the function version of SizeOf had problems passing the termination checker
  -- so I did it relationally and proved that it is a total function

  data SizeOf : Type → ℕ → Set where
    int : SizeOf int 1
    ~ : ∀ {τ} → SizeOf (~ τ) 1
    & : ∀ {ℓ mq τ} → SizeOf (& ℓ mq τ) 1
    Option : ∀ {τ n} → SizeOf τ n → SizeOf (Option τ) (1 + n)
    struct[] : ∀ {ℓs} → SizeOf (struct ℓs []) 0
    struct∷ : ∀ {ℓs τ τs nτ nτs}
            → SizeOf τ nτ
            → SizeOf (struct ℓs τs) nτs
            → SizeOf (struct ℓs (τ ∷ τs)) (nτ + nτs)

  SizeOf-defined : ∀ τ → Σ ℕ ** (λ n → SizeOf τ n)
  SizeOf-defined int = 1 , int
  SizeOf-defined (~ τ) = 1 , ~
  SizeOf-defined (& ℓ mq τ) = 1 , &
  SizeOf-defined (Option τ) with SizeOf-defined τ
  ... | n , Hτ = (1 + n) , Option Hτ
  SizeOf-defined (struct ℓs []) = 0 , struct[]
  SizeOf-defined (struct ℓs (τ ∷ τs)) with SizeOf-defined τ | SizeOf-defined (struct ℓs τs)
  ... | nτ , Hτ | nτs , Hτs = (nτ + nτs) , struct∷ Hτ Hτs

  SizeOf-unique : ∀ {n1 n2} τ → SizeOf τ n1 → SizeOf τ n2 → n1 ≡ n2
  SizeOf-unique int int int = refl
  SizeOf-unique (~ τ) ~ ~ = refl
  SizeOf-unique (& ℓ mq τ) & & = refl
  SizeOf-unique (Option τ) (Option H1) (Option H2) = cong S (SizeOf-unique τ H1 H2)
  SizeOf-unique (struct ℓs []) struct[] struct[] = refl
  SizeOf-unique (struct ℓs (τ ∷ τs)) (struct∷ H11 H12) (struct∷ H21 H22)
    rewrite SizeOf-unique τ H11 H21 | SizeOf-unique (struct ℓs τs) H12 H22 = refl

  -- ty-is-pod
  data _isCopy : Type → Set where
    int : int isCopy
    &imm : ∀ {ℓ mq τ} → & ℓ mq τ isCopy
    Option : ∀ {τ} → τ isCopy → Option τ isCopy
    struct : ∀ {ℓs τs} → All _isCopy τs → struct ℓs τs isCopy

  -- ty-needs-drop
  data _needsDrop : Type → Set where
    ~ : ∀ {τ} → ~ τ needsDrop
    Option : ∀ {τ} → τ needsDrop → Option τ needsDrop
    struct : ∀ {ℓs τs} → Any _needsDrop τs → struct ℓs τs needsDrop

  -- no type is both Copy and requires Drop
  -- (i.e. things that must free heap memory cannot be aliased by implicit copying)
  no-Copy-and-needs-Drop : ∀ τ → ¬ (τ isCopy × τ needsDrop)
  no-Copy-and-needs-Drop .int (int , ())
  no-Copy-and-needs-Drop (& ℓ mq τ) (&imm , ())
  no-Copy-and-needs-Drop (Option τ) (Option Hc , Option Hd) = no-Copy-and-needs-Drop τ (Hc , Hd)
  no-Copy-and-needs-Drop (struct ℓs []) (struct [] , struct ())
  no-Copy-and-needs-Drop (struct ℓs (τ ∷ τs)) (struct (τc ∷ τsc) , struct (aZ τd))
    = no-Copy-and-needs-Drop τ (τc , τd)
  no-Copy-and-needs-Drop (struct ℓs (τ ∷ τs)) (struct (τc ∷ τsc) , struct (aS τsd))
    = no-Copy-and-needs-Drop (struct ℓs τs) (struct τsc , struct τsd)

open Types public

{-

---- types
data Mut : Set where
  mut : Mut
  imm : Mut

data Type : Set where
  int : Type
  ~ : Type → Type
  Option : Type → Type
  & : Life → Mut → Type → Type
  struct : Id → List Life → Type

---- declarations
Structs = List (Id × (List Life × List Type))

data _w/_isPOD : Type → Structs → Set where
  int : ∀ {srs} → int w/ srs isPOD
  &imm : ∀ {srs ℓ τ} → & ℓ imm τ w/ srs isPOD
  Option : ∀ {srs τ} → τ w/ srs isPOD → Option τ w/ srs isPOD
  struct : ∀ {s ℓs τs srs ℓs′}
         → GoesTo s (ℓs′ , τs) srs
         → All (λ τ → τ w/ srs isPOD) τs
         → struct s ℓs w/ srs isPOD

data _w/_needsDrop : Type → Structs → Set where
  ~ : ∀ {srs τ} → ~ τ w/ srs needsDrop
  Option : ∀ {srs τ} → τ w/ srs needsDrop → Option τ w/ srs needsDrop
  struct : ∀ {srs s ℓs τs ℓs′}
         → GoesTo s (ℓs′ , τs) srs
         → Any (λ τ → τ w/ srs needsDrop) τs
         → struct s ℓs w/ srs needsDrop

-- sizeof
sizeof : Structs → Type → ℕ
sizeof srs int = 1
sizeof srs (~ τ) = 1
sizeof srs (Option τ) = 1 + sizeof srs τ
sizeof srs (& ℓ mq τ) = 1
sizeof srs (struct s ℓs) = {!!}

data sizeof_w/_is_ : Type → Structs → ℕ → Set where
  int : ∀ {srs} → sizeof int w/ srs is 1
  ~ : ∀ {τ srs} → sizeof ~ τ w/ srs is 1
  & : ∀ {ℓ mq τ srs} → sizeof & ℓ mq τ w/ srs is 1
  Option : ∀ {τ n srs} → sizeof τ w/ srs is n → sizeof Option τ w/ srs is (1 + n)
  {-
  struct : ∀ {s srs ℓs τs ℓs′}
         → GoesTo s (ℓs′ , τs) srs
         → 
         -}

-- we'll use newtyped nats as our variables
Cxt = List (Id × Type)

---- paths (lv)
data Path : Set where
  var : Id → Path

id-var : {a b : Id} → var a ≡ var b → a ≡ b
id-var refl = refl

_=Path=_ : (a b : Path) → Dec (a ≡ b)
var a =Path= var b with a == b
... | yes p = yes (cong var p)
... | no  p = no (p ∘ id-var)

EqPath : Eq Path
EqPath = record { _==_ = _=Path=_ }

-- paths which are prefixes of some path (paths are prefixes of themselves)
prefix-paths : Path → List Path
prefix-paths (var x) =  [ var x ]

-- path is a prefix of another path
_<_ : Path → Path → Set
a < b = a ∈ prefix-paths b

-- paths intersect if one is a subpath of the other
_∩_ : Path → Path → Set
a ∩ b = (a < b) ∨ (b < a)

-- path typing (lvtype)
data _⊢_∶_ : Cxt → Path → Type → Set where
  var : ∀ {Γ p τ x} → (GoesTo x τ Γ) → Γ ⊢ p ∶ τ

------- expressions (rv)
data Expr : Set where
  num : ℕ → Expr -- technically should be ints, but nats are sufficient
  plus : Path → Path → Expr
  path : Path → Expr

---- expression typing

-- deinitialized paths
Deinit = List Path

-- a path is initialized, but some subpaths may not be
_⊢_ShallowInit : Deinit → Path → Set
Δ ⊢ p ShallowInit = ¬ (Any (λ p′ → p′ ∈ Δ) (prefix-paths p))

-- a path is recursively initialized
_⊢_DeepInit : Deinit → Path → Set
Δ ⊢ p DeepInit = ¬ (Any (λ p′ → p ∩ p′) Δ)

-- TODO
data can-access : Cxt → Deinit → Path → Set where

-- TODO can-read-from is just can-access considering only mutable loans
data can-read-from : Cxt → Deinit → Path → Set where

-- can-move-from is just a synonym of can-access
can-move-from = can-access

-- safe to use a path (use-lv-ok)
data _,_,_⊢_use∶_,_ : Structs → Cxt → Deinit → Path → Type → Deinit → Set where
  copy : ∀ {srs Γ Δ p τ}
       → Γ ⊢ p ∶ τ -- path is well typed
       → τ w/ srs isPOD -- it's type is implicitly copyable
       → can-read-from Γ Δ p -- and we can read from it
       → srs , Γ , Δ ⊢ p use∶ τ , Δ -- then safe to use by copying
  move : ∀ {srs Γ Δ p τ}
       → Γ ⊢ p ∶ τ -- path is well typed
       → ¬ (τ w/ srs isPOD) -- it's type is NOT implicitly copyable
       → can-move-from Γ Δ p -- and we can move from it
       → srs , Γ , Δ ⊢ p use∶ τ , (p ∪ Δ) -- then safe to use by moving (deinitializes the path)

-- TODO add other expression contexts
-- expression is safe (rv-ok)
data _,_,_⊢_∶_,_ : Structs → Cxt → Deinit → Expr → Type → Deinit → Set where
  num : ∀ {srs Γ Δ n}
      → srs , Γ , Δ ⊢ (num n) ∶ int , Δ -- always ok to use a number (changes no paths)
  plus : ∀ {srs Γ Δ p₁ p₂}
       → Γ ⊢ p₁ ∶ int -- if both of the arguments are integers
       → Γ ⊢ p₂ ∶ int
       → srs , Γ , Δ ⊢ (plus p₁ p₂) ∶ int , Δ -- then the result is an integer (changes no paths)
  path : ∀ {srs Γ Δ p τ Δ′}
       → srs , Γ , Δ ⊢ p use∶ τ , Δ′ -- if it is safe to use the path (and changes init)
       → srs , Γ , Δ ⊢ (path p) ∶ τ , Δ′ -- then we can use the path (and propagate init changes)

----- statements
data Stmt : Set where
  Assign : Path → Expr → Stmt

----- evaluation

-- Addr is a pair of ℕs
module Addrs where
  data Addr : Set where
    addr : ℕ → ℕ → Addr

  addr-base : Addr → ℕ
  addr-base (addr b _) = b

  addr-off : Addr → ℕ
  addr-off (addr _ o) = o

  inc : Addr → Addr
  inc (addr b o) = addr b (o + 1)

  addr-inj : ∀ {b₁ b₂ o₁ o₂} → addr b₁ o₁ ≡ addr b₂ o₂ → (b₁ ≡ b₂) × (o₁ ≡ o₂)
  addr-inj refl = refl , refl

  _=Addr=_ : (a₁ a₂ : Addr) → Dec (a₁ ≡ a₂)
  addr b₁ o₁ =Addr= addr b₂ o₂ with b₁ == b₂ | o₁ == o₂
  addr .b₂ .o₂ =Addr= addr b₂ o₂ | yes refl | yes refl = yes refl
  addr .b₂ o₁ =Addr= addr b₂ o₂ | yes refl | no oeq = no (oeq ∘ cong addr-off)
  addr b₁ o₁ =Addr= addr b₂ o₂ | no beq | oeq = no (beq ∘ cong addr-base)
  
  EqAddr : Eq Addr
  EqAddr = record { _==_ = _=Addr=_ }
open Addrs public

-- values that can go in the heap
data Value : Set where
  void : Value
  int : ℕ → Value
  ptr : Addr → Value

-- memory: maps address to values
Heap = List (Addr × Value)

data Memcopy : Heap → (dst src : Addr) → (size : ℕ) → Heap → Set where
  Z : ∀ {H α β} → Memcopy H α β 0 H
  S : ∀ {H₀ α β v H₁ H₂ n}
    → GoesTo β v H₀ -- β maps to v
    → Update α v H₀ H₁ -- set α to map to v
    → Memcopy H₁ (inc α) (inc β) n H₂ -- recurse
    → Memcopy H₀ α β (S n) H₂

-- map from variables to addresses
VMap = List (Id × Addr)
-- stack
Frame = Life × List Stmt
Stack = List Frame

-- path evalutation to an address (lvaddr)
data _,_,_⊢_⇒_ : Heap → VMap → Cxt → Path → Addr → Set where
  var : ∀ {H V Γ x α}
      → GoesTo x α V -- if the variable maps to an address
      → H , V , Γ ⊢ (var x) ⇒ α -- then that is the result

-- expression evalutes to a value and is stored at the provided address (rveval)
data rveval : Structs → Heap → VMap → Cxt → Addr → Expr → Heap → Set where
  num : ∀ {srs H V Γ α n H′}
      → Update α (int n) H H′ -- update the address in the heap with the int
      → rveval srs H V Γ α (num n) H′
  plus : ∀ {srs H V Γ α p₁ p₂ α₁ α₂ n₁ n₂ H′}
       → H , V , Γ ⊢ p₁ ⇒ α₁ -- evalutate the first argument to an address
       → H , V , Γ ⊢ p₂ ⇒ α₂ -- evalutate the second argument to an address
       → GoesTo α₁ (int n₁) H -- first address goes to an integer
       → GoesTo α₂ (int n₂) H -- and so does the second
       → Update α (int (n₁ + n₂)) H H′ -- update the heap with the sum of the two numbers
       → rveval srs H V Γ α (plus p₁ p₂) H′
       {-
  path : ∀ {srs H V Γ α p τ n β H′}
       → Γ ⊢ p ∶ τ -- path refers to a type τ (needed for dispatch)
       → sizeof τ w/ srs is n -- the type takes up n slots of memory
       → H , V , Γ ⊢ p ⇒ β -- the path refers to the address β
       → Memcopy H α β n H′ -- copy n slots from β to α
       → rveval srs H V Γ α (path p) H′
       -}

       -}
