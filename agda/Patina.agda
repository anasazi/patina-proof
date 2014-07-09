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
--open import List
open import Vec
open import Fin

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
    int : Type -- integers
    box : Type → Type -- unique pointers to heap memory
    ref : (ℓ : Life) → (mq : Mut) → Type → Type -- borrowed references
    opt : Type → Type -- option
    rec : ∀ {n1 n2} -- structs consist of ...
        → (vℓs : Vec (Var × Life) n1) -- a vector of variance / lifetime pairs
        → (τs : Vec Type n2) --- and a vector of types
        → Type 
    var : Id → Type -- type variables (for recursive types)
    μ : Id → Type → Type -- recursive types

  -- test structs from redex model
  srs-A : Type
  srs-A = rec [] ([ int ])
  srs-B : Life → Type
  srs-B l0 = rec ([ (cov , l0) ]) ([ int ,, int ])
  srs-C : Life → Type
  srs-C l0 = rec ([ (cov , l0) ]) ([ srs-A ,, srs-B l0 ])
  srs-D : Life → Type
  srs-D l0 = rec ([ (cov , l0) ]) ([ srs-C l0 ,, srs-A ,, srs-C l0 ,, srs-B l0 ])
  srs-E : Type
  srs-E = rec [] ([ box int ])
  -- making sure we can represent resursive structs
  srs-List : Type
  srs-List = μ (id 0) (rec [] ([ int ,, opt (box (var (id 0))) ]))

  -- types where all type variables are boxed (either by a box or a ref).
  -- in other words, types that have a finitely sized allocation
  data NoBareVar : Type → Set where
    int : NoBareVar int
    boxVar : ∀ {x} → NoBareVar (box (var x))
    box : ∀ {τ} → NoBareVar τ → NoBareVar (box τ)
    refVar : ∀ {ℓ mq x} → NoBareVar (ref ℓ mq (var x))
    ref : ∀ {ℓ mq τ} → NoBareVar τ → NoBareVar (ref ℓ mq τ)
    opt : ∀ {τ} → NoBareVar τ → NoBareVar (opt τ)
    rec : ∀ {n1 n2} {vℓs : Vec _ n1} {τs : Vec _ n2} → All NoBareVar τs → NoBareVar (rec vℓs τs)
    μ : ∀ {x τ} → NoBareVar τ → NoBareVar (μ x τ)

  nbv-A : NoBareVar srs-A
  nbv-A = rec (int ∷ [])
  nbv-B : ∀ {l0} → NoBareVar (srs-B l0)
  nbv-B = rec (int ∷ int ∷ [])
  nbv-C : ∀ {l0} → NoBareVar (srs-C l0)
  nbv-C = rec (rec (int ∷ []) ∷ rec (int ∷ int ∷ []) ∷ [])
  nbv-D : ∀ {l0} → NoBareVar (srs-D l0)
  nbv-D = rec
            (rec (rec (int ∷ []) ∷ rec (int ∷ int ∷ []) ∷ []) ∷
             rec (int ∷ []) ∷
             rec (rec (int ∷ []) ∷ rec (int ∷ int ∷ []) ∷ []) ∷
             rec (int ∷ int ∷ []) ∷ [])
  nbv-E : NoBareVar srs-E
  nbv-E = rec (box int ∷ [])
  -- making sure we can represent resursive structs
  nbv-List : NoBareVar srs-List
  nbv-List = μ (rec (int ∷ opt boxVar ∷ []))

  -- type with no bare variables have a size (a real function this time!)
  size-of : (τ : Type) → NoBareVar τ → ℕ
  size-of int pf = 1
  size-of (box τ) pf = 1
  size-of (ref ℓ mq τ) pf = 1
  size-of (opt τ) (opt pf) = 1 + size-of τ pf
  size-of (rec vℓs []) (rec []) = 0
  size-of (rec vℓs (τ ∷ τs)) (rec (pf ∷ pfs)) = size-of τ pf + size-of (rec vℓs τs) (rec pfs)
  size-of (var x) ()
  size-of (μ x τ) (μ pf) = size-of τ pf

  -- tests from redex model
  size-of-A : size-of srs-A nbv-A ≡ 1
  size-of-A = refl
  size-of-B : size-of (srs-B static) nbv-B ≡ 2
  size-of-B = refl
  size-of-C : size-of (srs-C static) nbv-C ≡ 3
  size-of-C = refl
  size-of-opt-C : size-of (opt (srs-C static)) (opt nbv-C) ≡ 4
  size-of-opt-C = refl
  -- making sure we can represent resursive structs
  size-of-List : size-of srs-List nbv-List ≡ 3
  size-of-List = refl

  -- ty-is-pod
  -- copyable types do not contain affine data and can be freely copied
  data _is-copy : Type → Set where
    int : int is-copy
    &imm : ∀ {ℓ τ} → ref ℓ imm τ is-copy
    opt : ∀ {τ} → τ is-copy → opt τ is-copy
    rec : ∀ {n1 n2} {vℓs : Vec _ n2} {τs : Vec _ n1} → All _is-copy τs → rec vℓs τs is-copy
    μ : ∀ {x τ} → τ is-copy → μ x τ is-copy

  -- tests from redex
  test-int-is-copy : int is-copy
  test-int-is-copy = int
  test-opt-int-is-copy : opt int is-copy
  test-opt-int-is-copy = opt int
  test-box-int-is-not-copy : ¬ (box int is-copy)
  test-box-int-is-not-copy ()
  test-opt-box-int-is-not-copy : ¬ (opt (box int) is-copy)
  test-opt-box-int-is-not-copy (opt ())
  test-ref-imm-int-is-copy : ref (life 0) imm int is-copy
  test-ref-imm-int-is-copy = &imm
  test-ref-mut-int-is-not-copy : ¬ (ref (life 0) mut int is-copy)
  test-ref-mut-int-is-not-copy ()
  test-srs-A-is-copy : srs-A is-copy
  test-srs-A-is-copy = rec (int ∷ [])
  test-srs-E-is-not-copy : ¬ (srs-E is-copy)
  test-srs-E-is-not-copy (rec (() ∷ x))

  -- ty-needs-drop
  -- types that own heap memory and need to free it (a subset of the affine types)
  data _needs-drop : Type → Set where
    box : ∀ {τ} → box τ needs-drop
    opt : ∀ {τ} → τ needs-drop → opt τ needs-drop
    rec : ∀ {n1 n2} {vℓs : Vec _ n1} {τs : Vec _ n2} → Any _needs-drop τs → rec vℓs τs needs-drop
    μ : ∀ {x τ} → τ needs-drop → μ x τ needs-drop

  -- tests from redex
  test-int-no-needs-drop : ¬ (int needs-drop)
  test-int-no-needs-drop ()
  test-opt-int-no-needs-drop : ¬ (opt int needs-drop)
  test-opt-int-no-needs-drop (opt ())
  test-box-int-needs-drop : box int needs-drop
  test-box-int-needs-drop = box
  test-opt-box-int-needs-drop : opt (box int) needs-drop
  test-opt-box-int-needs-drop = opt box
  test-ref-imm-int-no-needs-drop : ¬ (ref (life 0) imm int needs-drop)
  test-ref-imm-int-no-needs-drop ()
  test-ref-mut-int-no-needs-drop : ¬ (ref (life 0) mut int needs-drop)
  test-ref-mut-int-no-needs-drop ()
  test-srs-A-no-needs-drop : ¬ (srs-A needs-drop)
  test-srs-A-no-needs-drop (rec (Z ()))
  test-srs-A-no-needs-drop (rec (S ()))
  test-srs-E-needs-drop : srs-E needs-drop
  test-srs-E-needs-drop = rec (Z box)

  -- no type is both Copy and also requires Drop
  -- (i.e. things that must free heap memory cannot be aliased by implicit copying)
  -- (i.e. the set of non-affine types is disjoint from a subset of the affine types)
  copy-drop : ∀ τ → ¬ (τ is-copy × τ needs-drop)
  copy-drop int (_ , ())
  copy-drop (box _) (() , _)
  copy-drop (ref _ _ _) (_ , ())
  copy-drop (opt τ) (opt Cτ , opt Dτ) = copy-drop τ (Cτ , Dτ)
  copy-drop (rec _ []) (rec [] , rec ())
  copy-drop (rec _ (τ ∷ _)) (rec (Cτ ∷ _) , rec (Z Dτ)) = copy-drop τ (Cτ , Dτ)
  copy-drop (rec ℓ (_ ∷ τs)) (rec (_ ∷ Cτs) , rec (S Dτs)) = copy-drop (rec ℓ τs) (rec Cτs , rec Dτs)
  copy-drop (var _) (() , _)
  copy-drop (μ _ τ) (μ Cτ , μ Dτ) = copy-drop τ (Cτ , Dτ)

  Cxt = Vec Type

  -- the test context from the redex file
  test-Γ : Cxt 12
  test-Γ = [  int -- i
           ,, box int -- p
           -- redex contexts are lists of lists
           -- in the redex model, there's a list boundary here
           ,, srs-A -- a
           ,, srs-B static -- b
           ,, srs-C static -- c
           ,, ref (life 13 {- b1 in redex -}) imm int -- q
           ,, box int -- r
           ,, opt (box int) -- s
           -- vec int 3 -- ints3
           ,, int -- i0
           ,, int -- i1
           ,, int -- i2
           ,, int -- i3
           -- ref (life 13) imm (vec int 3) -- ints3p
           -- ref (life 13) imm (vec int erased) -- intsp
           ]

open Types public  

module Paths where

  data Path : Set where
    var : ∀ {n} → Fin n → Path -- variables (index into the context)
    deref : Path → Path -- dereferences
    -- field projection (index into the vector of types in a record)
    proj : ∀ {n} → Fin n → Path → Path

  -- lvtype
  -- typing judgment for paths
  data _⊢_∶_ {n} : Cxt n → Path → Type → Set where
    var : ∀ {Γ} {i : Fin n} → Γ ⊢ var i ∶ (Γ ! i)
    box : ∀ {Γ p τ} → Γ ⊢ p ∶ box τ → Γ ⊢ deref p ∶ τ
    ref : ∀ {Γ p τ ℓ mq} → Γ ⊢ p ∶ ref ℓ mq τ → Γ ⊢ deref p ∶ τ
    proj : ∀ {n1 n2 Γ p} {i : Fin n2} {vℓs : Vec _ n1} {τs : Vec _ n2}
         → Γ ⊢ p ∶ rec vℓs τs
         → Γ ⊢ proj i p ∶ (τs ! i)

  test-path-type-deref-p : test-Γ ⊢ deref (var (fin 1)) ∶ int
  test-path-type-deref-p = box var
  test-path-type-proj-1-c : test-Γ ⊢ proj (fin 1) (var (fin 4)) ∶ srs-B static
  test-path-type-proj-1-c = proj var

  -- prefix-paths
  prefix-paths : Path → Σ ℕ ** Vec Path
  prefix-paths (var x) = 1 , ([ var x ])
  prefix-paths (deref p) = (S *** _∷_ (deref p)) (prefix-paths p)
  prefix-paths (proj f p) = (S *** _∷_ (proj f p)) (prefix-paths p)


  test-prefix-paths-var : prefix-paths (var {1} (fin 0)) ≡ 1 , ([ var (fin 0) ])
  test-prefix-paths-var = refl
  -- test from redex
  test-prefix-paths : prefix-paths (deref (proj {2} (fin 1) (var {1} (fin 0)))) ≡
                      3 , ([ (deref (proj {2} (fin 1) (var {1} (fin 0))))
                          ,, (proj {2} (fin 1) (var {1} (fin 0)))
                          ,, var {1} (fin 0)
                          ])
  test-prefix-paths = refl

open Paths public

--   data Type : Set where
--     int : Type
--     ~ : Type → Type
--     Option : Type → Type
--     & : Life → Mut → Type → Type
--     -- using structural structs instead of nominal ones
--     -- easier than dealing with lookups everywhere
--     -- may end up chaning the well-formed checks since the Redex model does those on the declarations
--     struct : List (Var × Life) → List Type → Type 

--   -- the function version of SizeOf had problems passing the termination checker
--   -- so I did it relationally and proved that it is a total function

--   data SizeOf : Type → ℕ → Set where
--     int : SizeOf int 1
--     ~ : ∀ {τ} → SizeOf (~ τ) 1
--     & : ∀ {ℓ mq τ} → SizeOf (& ℓ mq τ) 1
--     Option : ∀ {τ n} → SizeOf τ n → SizeOf (Option τ) (1 + n)
--     struct[] : ∀ {ℓs} → SizeOf (struct ℓs []) 0
--     struct∷ : ∀ {ℓs τ τs nτ nτs}
--             → SizeOf τ nτ
--             → SizeOf (struct ℓs τs) nτs
--             → SizeOf (struct ℓs (τ ∷ τs)) (nτ + nτs)

--   SizeOf-defined : ∀ τ → Σ ℕ ** (λ n → SizeOf τ n)
--   SizeOf-defined int = 1 , int
--   SizeOf-defined (~ τ) = 1 , ~
--   SizeOf-defined (& ℓ mq τ) = 1 , &
--   SizeOf-defined (Option τ) with SizeOf-defined τ
--   ... | n , Hτ = (1 + n) , Option Hτ
--   SizeOf-defined (struct ℓs []) = 0 , struct[]
--   SizeOf-defined (struct ℓs (τ ∷ τs)) with SizeOf-defined τ | SizeOf-defined (struct ℓs τs)
--   ... | nτ , Hτ | nτs , Hτs = (nτ + nτs) , struct∷ Hτ Hτs

--   SizeOf-unique : ∀ {n1 n2} τ → SizeOf τ n1 → SizeOf τ n2 → n1 ≡ n2
--   SizeOf-unique int int int = refl
--   SizeOf-unique (~ τ) ~ ~ = refl
--   SizeOf-unique (& ℓ mq τ) & & = refl
--   SizeOf-unique (Option τ) (Option H1) (Option H2) = cong S (SizeOf-unique τ H1 H2)
--   SizeOf-unique (struct ℓs []) struct[] struct[] = refl
--   SizeOf-unique (struct ℓs (τ ∷ τs)) (struct∷ H11 H12) (struct∷ H21 H22)
--     rewrite SizeOf-unique τ H11 H21 | SizeOf-unique (struct ℓs τs) H12 H22 = refl

--   -- ty-is-pod
--   data _isCopy : Type → Set where
--     int : int isCopy
--     &imm : ∀ {ℓ mq τ} → & ℓ mq τ isCopy
--     Option : ∀ {τ} → τ isCopy → Option τ isCopy
--     struct : ∀ {ℓs τs} → All _isCopy τs → struct ℓs τs isCopy

--   -- ty-needs-drop
--   data _needsDrop : Type → Set where
--     ~ : ∀ {τ} → ~ τ needsDrop
--     Option : ∀ {τ} → τ needsDrop → Option τ needsDrop
--     struct : ∀ {ℓs τs} → Any _needsDrop τs → struct ℓs τs needsDrop

--   -- no type is both Copy and requires Drop
--   -- (i.e. things that must free heap memory cannot be aliased by implicit copying)
--   no-Copy-and-needs-Drop : ∀ τ → ¬ (τ isCopy × τ needsDrop)
--   no-Copy-and-needs-Drop .int (int , ())
--   no-Copy-and-needs-Drop (& ℓ mq τ) (&imm , ())
--   no-Copy-and-needs-Drop (Option τ) (Option Hc , Option Hd) = no-Copy-and-needs-Drop τ (Hc , Hd)
--   no-Copy-and-needs-Drop (struct ℓs []) (struct [] , struct ())
--   no-Copy-and-needs-Drop (struct ℓs (τ ∷ τs)) (struct (τc ∷ τsc) , struct (aZ τd))
--     = no-Copy-and-needs-Drop τ (τc , τd)
--   no-Copy-and-needs-Drop (struct ℓs (τ ∷ τs)) (struct (τc ∷ τsc) , struct (aS τsd))
--     = no-Copy-and-needs-Drop (struct ℓs τs) (struct τsc , struct τsd)

-- open Types public

-- {-

-- ---- types
-- data Mut : Set where
--   mut : Mut
--   imm : Mut

-- data Type : Set where
--   int : Type
--   ~ : Type → Type
--   Option : Type → Type
--   & : Life → Mut → Type → Type
--   struct : Id → List Life → Type

-- ---- declarations
-- Structs = List (Id × (List Life × List Type))

-- data _w/_isPOD : Type → Structs → Set where
--   int : ∀ {srs} → int w/ srs isPOD
--   &imm : ∀ {srs ℓ τ} → & ℓ imm τ w/ srs isPOD
--   Option : ∀ {srs τ} → τ w/ srs isPOD → Option τ w/ srs isPOD
--   struct : ∀ {s ℓs τs srs ℓs′}
--          → GoesTo s (ℓs′ , τs) srs
--          → All (λ τ → τ w/ srs isPOD) τs
--          → struct s ℓs w/ srs isPOD

-- data _w/_needsDrop : Type → Structs → Set where
--   ~ : ∀ {srs τ} → ~ τ w/ srs needsDrop
--   Option : ∀ {srs τ} → τ w/ srs needsDrop → Option τ w/ srs needsDrop
--   struct : ∀ {srs s ℓs τs ℓs′}
--          → GoesTo s (ℓs′ , τs) srs
--          → Any (λ τ → τ w/ srs needsDrop) τs
--          → struct s ℓs w/ srs needsDrop

-- -- sizeof
-- sizeof : Structs → Type → ℕ
-- sizeof srs int = 1
-- sizeof srs (~ τ) = 1
-- sizeof srs (Option τ) = 1 + sizeof srs τ
-- sizeof srs (& ℓ mq τ) = 1
-- sizeof srs (struct s ℓs) = {!!}

-- data sizeof_w/_is_ : Type → Structs → ℕ → Set where
--   int : ∀ {srs} → sizeof int w/ srs is 1
--   ~ : ∀ {τ srs} → sizeof ~ τ w/ srs is 1
--   & : ∀ {ℓ mq τ srs} → sizeof & ℓ mq τ w/ srs is 1
--   Option : ∀ {τ n srs} → sizeof τ w/ srs is n → sizeof Option τ w/ srs is (1 + n)
--   {-
--   struct : ∀ {s srs ℓs τs ℓs′}
--          → GoesTo s (ℓs′ , τs) srs
--          → 
--          -}

-- -- we'll use newtyped nats as our variables
-- Cxt = List (Id × Type)

-- ---- paths (lv)
-- data Path : Set where
--   var : Id → Path

-- id-var : {a b : Id} → var a ≡ var b → a ≡ b
-- id-var refl = refl

-- _=Path=_ : (a b : Path) → Dec (a ≡ b)
-- var a =Path= var b with a == b
-- ... | yes p = yes (cong var p)
-- ... | no  p = no (p ∘ id-var)

-- EqPath : Eq Path
-- EqPath = record { _==_ = _=Path=_ }

-- -- paths which are prefixes of some path (paths are prefixes of themselves)
-- prefix-paths : Path → List Path
-- prefix-paths (var x) =  [ var x ]

-- -- path is a prefix of another path
-- _<_ : Path → Path → Set
-- a < b = a ∈ prefix-paths b

-- -- paths intersect if one is a subpath of the other
-- _∩_ : Path → Path → Set
-- a ∩ b = (a < b) ∨ (b < a)

-- -- path typing (lvtype)
-- data _⊢_∶_ : Cxt → Path → Type → Set where
--   var : ∀ {Γ p τ x} → (GoesTo x τ Γ) → Γ ⊢ p ∶ τ

-- ------- expressions (rv)
-- data Expr : Set where
--   num : ℕ → Expr -- technically should be ints, but nats are sufficient
--   plus : Path → Path → Expr
--   path : Path → Expr

-- ---- expression typing

-- -- deinitialized paths
-- Deinit = List Path

-- -- a path is initialized, but some subpaths may not be
-- _⊢_ShallowInit : Deinit → Path → Set
-- Δ ⊢ p ShallowInit = ¬ (Any (λ p′ → p′ ∈ Δ) (prefix-paths p))

-- -- a path is recursively initialized
-- _⊢_DeepInit : Deinit → Path → Set
-- Δ ⊢ p DeepInit = ¬ (Any (λ p′ → p ∩ p′) Δ)

-- -- TODO
-- data can-access : Cxt → Deinit → Path → Set where

-- -- TODO can-read-from is just can-access considering only mutable loans
-- data can-read-from : Cxt → Deinit → Path → Set where

-- -- can-move-from is just a synonym of can-access
-- can-move-from = can-access

-- -- safe to use a path (use-lv-ok)
-- data _,_,_⊢_use∶_,_ : Structs → Cxt → Deinit → Path → Type → Deinit → Set where
--   copy : ∀ {srs Γ Δ p τ}
--        → Γ ⊢ p ∶ τ -- path is well typed
--        → τ w/ srs isPOD -- it's type is implicitly copyable
--        → can-read-from Γ Δ p -- and we can read from it
--        → srs , Γ , Δ ⊢ p use∶ τ , Δ -- then safe to use by copying
--   move : ∀ {srs Γ Δ p τ}
--        → Γ ⊢ p ∶ τ -- path is well typed
--        → ¬ (τ w/ srs isPOD) -- it's type is NOT implicitly copyable
--        → can-move-from Γ Δ p -- and we can move from it
--        → srs , Γ , Δ ⊢ p use∶ τ , (p ∪ Δ) -- then safe to use by moving (deinitializes the path)

-- -- TODO add other expression contexts
-- -- expression is safe (rv-ok)
-- data _,_,_⊢_∶_,_ : Structs → Cxt → Deinit → Expr → Type → Deinit → Set where
--   num : ∀ {srs Γ Δ n}
--       → srs , Γ , Δ ⊢ (num n) ∶ int , Δ -- always ok to use a number (changes no paths)
--   plus : ∀ {srs Γ Δ p₁ p₂}
--        → Γ ⊢ p₁ ∶ int -- if both of the arguments are integers
--        → Γ ⊢ p₂ ∶ int
--        → srs , Γ , Δ ⊢ (plus p₁ p₂) ∶ int , Δ -- then the result is an integer (changes no paths)
--   path : ∀ {srs Γ Δ p τ Δ′}
--        → srs , Γ , Δ ⊢ p use∶ τ , Δ′ -- if it is safe to use the path (and changes init)
--        → srs , Γ , Δ ⊢ (path p) ∶ τ , Δ′ -- then we can use the path (and propagate init changes)

-- ----- statements
-- data Stmt : Set where
--   Assign : Path → Expr → Stmt

-- ----- evaluation

-- -- Addr is a pair of ℕs
-- module Addrs where
--   data Addr : Set where
--     addr : ℕ → ℕ → Addr

--   addr-base : Addr → ℕ
--   addr-base (addr b _) = b

--   addr-off : Addr → ℕ
--   addr-off (addr _ o) = o

--   inc : Addr → Addr
--   inc (addr b o) = addr b (o + 1)

--   addr-inj : ∀ {b₁ b₂ o₁ o₂} → addr b₁ o₁ ≡ addr b₂ o₂ → (b₁ ≡ b₂) × (o₁ ≡ o₂)
--   addr-inj refl = refl , refl

--   _=Addr=_ : (a₁ a₂ : Addr) → Dec (a₁ ≡ a₂)
--   addr b₁ o₁ =Addr= addr b₂ o₂ with b₁ == b₂ | o₁ == o₂
--   addr .b₂ .o₂ =Addr= addr b₂ o₂ | yes refl | yes refl = yes refl
--   addr .b₂ o₁ =Addr= addr b₂ o₂ | yes refl | no oeq = no (oeq ∘ cong addr-off)
--   addr b₁ o₁ =Addr= addr b₂ o₂ | no beq | oeq = no (beq ∘ cong addr-base)
  
--   EqAddr : Eq Addr
--   EqAddr = record { _==_ = _=Addr=_ }
-- open Addrs public

-- -- values that can go in the heap
-- data Value : Set where
--   void : Value
--   int : ℕ → Value
--   ptr : Addr → Value

-- -- memory: maps address to values
-- Heap = List (Addr × Value)

-- data Memcopy : Heap → (dst src : Addr) → (size : ℕ) → Heap → Set where
--   Z : ∀ {H α β} → Memcopy H α β 0 H
--   S : ∀ {H₀ α β v H₁ H₂ n}
--     → GoesTo β v H₀ -- β maps to v
--     → Update α v H₀ H₁ -- set α to map to v
--     → Memcopy H₁ (inc α) (inc β) n H₂ -- recurse
--     → Memcopy H₀ α β (S n) H₂

-- -- map from variables to addresses
-- VMap = List (Id × Addr)
-- -- stack
-- Frame = Life × List Stmt
-- Stack = List Frame

-- -- path evalutation to an address (lvaddr)
-- data _,_,_⊢_⇒_ : Heap → VMap → Cxt → Path → Addr → Set where
--   var : ∀ {H V Γ x α}
--       → GoesTo x α V -- if the variable maps to an address
--       → H , V , Γ ⊢ (var x) ⇒ α -- then that is the result

-- -- expression evalutes to a value and is stored at the provided address (rveval)
-- data rveval : Structs → Heap → VMap → Cxt → Addr → Expr → Heap → Set where
--   num : ∀ {srs H V Γ α n H′}
--       → Update α (int n) H H′ -- update the address in the heap with the int
--       → rveval srs H V Γ α (num n) H′
--   plus : ∀ {srs H V Γ α p₁ p₂ α₁ α₂ n₁ n₂ H′}
--        → H , V , Γ ⊢ p₁ ⇒ α₁ -- evalutate the first argument to an address
--        → H , V , Γ ⊢ p₂ ⇒ α₂ -- evalutate the second argument to an address
--        → GoesTo α₁ (int n₁) H -- first address goes to an integer
--        → GoesTo α₂ (int n₂) H -- and so does the second
--        → Update α (int (n₁ + n₂)) H H′ -- update the heap with the sum of the two numbers
--        → rveval srs H V Γ α (plus p₁ p₂) H′
--        {-
--   path : ∀ {srs H V Γ α p τ n β H′}
--        → Γ ⊢ p ∶ τ -- path refers to a type τ (needed for dispatch)
--        → sizeof τ w/ srs is n -- the type takes up n slots of memory
--        → H , V , Γ ⊢ p ⇒ β -- the path refers to the address β
--        → Memcopy H α β n H′ -- copy n slots from β to α
--        → rveval srs H V Γ α (path p) H′
--        -}

--        -}
