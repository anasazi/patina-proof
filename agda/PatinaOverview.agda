open import Equality
open import List
open import Function {- _∘_ and _$_ are dependent versions of Haskell's (.) and ($) -}
open import Nat
open import Decidable
open import Product
open import Sum
open import Empty
open import Unit

open import Bool
module PatinaOverview {Life : Set} {{EqLife : Eq Life}} where

-- the lifetime relation (an irreflexive, transitive relation)
-- currently Patina cannot describe relationships between lifetime parameters.
-- this has the effect of creating some number of top level lifetimes (the parameters + 'static) that are all unrelated
-- all other lifetimes come from blocks, which are sublifetimes of every preceding lifetime.
-- thus, the lifetime relation usually looks like 'a <: 'b <: (top 'l0 & top 'l1 & top 'static).
-- if we ever add relationships between lifetime parameters, then we will need to revisit this representation.
data LifeRel : Set where
  top : Life → LifeRel -- a top level lifetime (no superlifetimes)
  _<:_ : Life → LifeRel → LifeRel -- a sublifetime relationship between a lifetime and a set of lifetimes
  _&_ : LifeRel → LifeRel → LifeRel -- union of two disjoint lifetime relations

-- just a simple example
module LifeRelEx where
  private 
    {- b <: a <: {l0 l1} -}  
    postulate
      ex-b : Life
      ex-a : Life
      ex-l0 : Life
      ex-l1 : Life
    ex-Λ : LifeRel
    ex-Λ = ex-b <: (ex-a <: (top ex-l0 & top ex-l1))
  
 -- is a lifetime defined by the relation?
data defines : Life → LifeRel → Set where
  -- top level lifetimes define only themselves
  top : ∀ {ℓ ℓ′} → ℓ ≡ ℓ′ → defines ℓ (top ℓ′)
  -- sublife relations define the lifetime argument
  sub-def : ∀ {ℓ ℓ′ Λ} → ℓ ≡ ℓ′ → defines ℓ (ℓ′ <: Λ) 
  -- a lifetime defined by a relation is still defined when a new lifetime is added
  sub-con : ∀ {ℓ ℓ′ Λ} → defines ℓ Λ → defines ℓ (ℓ′ <: Λ) 
  -- a lifetime is defined by a union if it is defined by either half
  and : ∀ {ℓ Λ₁ Λ₂} → defines ℓ Λ₁ + defines ℓ Λ₂ → defines ℓ (Λ₁ & Λ₂)
  
-- decision procedure for lifetime defintion
defines? : (ℓ : Life) → (Λ : LifeRel) → Dec (defines ℓ Λ)
-- top defines itself and nothing else
defines? ℓ (top ℓ′) with ℓ == ℓ′
... | yes eq = yes (top eq)
... | no ¬eq = no (λ {(top eq) → ¬eq eq})
defines? ℓ (ℓ′ <: Λ) with ℓ == ℓ′
-- sub defines its lifetime argument
... | yes eq = yes (sub-def eq)
-- and otherwise inherits the definitions of its relation argument
... | no ¬eq with defines? ℓ Λ
... | yes ih = yes (sub-con ih)
... | no ¬ih = no (λ {(sub-def eq) → ¬eq eq ; (sub-con ih) → ¬ih ih})
-- union defines anything defined in either argument
defines? ℓ (Λ1 & Λ2) with defines? ℓ Λ1 | defines? ℓ Λ2
defines? ℓ (Λ1 & Λ2) | yes ih1 | ih2? = yes (and (inl ih1))
defines? ℓ (Λ1 & Λ2) | no ¬ih1 | yes ih2 = yes (and (inr ih2))
defines? ℓ (Λ1 & Λ2) | no ¬ih1 | no ¬ih2 = no (λ { (and (inl ih1)) → ¬ih1 ih1 
                                                 ; (and (inr ih2)) → ¬ih2 ih2})

-- we can't define something undefined by adding something else to the relation
¬def-cons : ∀ {ℓ ℓ′ Λ} → ¬ (ℓ ≡ ℓ′) → ¬ (defines ℓ Λ) → ¬ (defines ℓ (ℓ′ <: Λ))
¬def-cons ¬eq ¬def (sub-def eq) = ¬eq eq
¬def-cons ¬eq ¬def (sub-con def) = ¬def def
  
-- sublife judgment
data sublife : LifeRel → Life → Life → Set where
  -- a new lifetime is a sublifetime of anything already defined in the relation
  rel : ∀ {ℓ ℓ₁ ℓ₂ Λ} → ℓ ≡ ℓ₁ → defines ℓ₂ Λ → sublife (ℓ <: Λ) ℓ₁ ℓ₂
  -- sublife is preserved by adding other things to the relation
  sub : ∀ {ℓ ℓ₁ ℓ₂ Λ} → sublife Λ ℓ₁ ℓ₂ → sublife (ℓ <: Λ) ℓ₁ ℓ₂
  -- if either part of a union proves a sublife relationship, then the union does too
  and : ∀ {ℓ₁ ℓ₂ Λ₁ Λ₂} → sublife Λ₁ ℓ₁ ℓ₂ + sublife Λ₂ ℓ₁ ℓ₂ → sublife (Λ₁ & Λ₂) ℓ₁ ℓ₂
  
-- sublife implies defined for both arguments
sub=>def-1 : ∀ {ℓ1 ℓ2 Λ} → sublife Λ ℓ1 ℓ2 → defines ℓ1 Λ
sub=>def-1 (rel refl def2) = sub-def refl
sub=>def-1 (sub pf) = sub-con (sub=>def-1 pf)
sub=>def-1 (and (inl pf)) = and (inl (sub=>def-1 pf))
sub=>def-1 (and (inr pf)) = and (inr (sub=>def-1 pf))

sub=>def-2 : ∀ {ℓ1 ℓ2 Λ} → sublife Λ ℓ1 ℓ2 → defines ℓ2 Λ
sub=>def-2 (rel eq def2) = sub-con def2
sub=>def-2 (sub pf) = sub-con (sub=>def-2 pf)
sub=>def-2 (and (inl pf)) = and (inl (sub=>def-2 pf))
sub=>def-2 (and (inr pf)) = and (inr (sub=>def-2 pf))

-- the second lifetime of a sublife judgment must already be defined
cons=>def : ∀ {ℓ ℓ′ Λ} → sublife (ℓ′ <: Λ) ℓ′ ℓ → defines ℓ Λ
cons=>def (rel eq def) = def
cons=>def (sub pf) = sub=>def-2 pf
  
-- sublife decision procedure
sublife? : (Λ : LifeRel) (ℓ1 ℓ2 : Life) → Dec (sublife Λ ℓ1 ℓ2)
-- first we need to check whether ℓ1 is defined by Λ
sublife? Λ ℓ1 ℓ2 with defines? ℓ1 Λ 
-- if it is, then we can examine how it is defined
-- if the relation is *only* ℓ1, then ¬ (ℓ1 <: ℓ2) due to irreflexivity
sublife? (top ℓ1) .ℓ1 ℓ2 | yes (top refl) = no (λ ()) 
-- if ℓ1 is cons onto some other relation, 
-- we need to examine if ℓ2 is defined by the rest
sublife? (ℓ1 <: Λ) .ℓ1 ℓ2 | yes (sub-def refl) with defines? ℓ2 Λ
-- if so, then ℓ1 <: ℓ2
... | yes ℓ2-def = yes (rel refl ℓ2-def)
-- otherwise they can't be (since ℓ2 doesn't exist)
... | no ¬ℓ2-def = no (¬ℓ2-def ∘ cons=>def)
-- if some other lifetime is consed onto the relation defining ℓ1, 
-- we need to inductively find a sublife proof
sublife? (ℓ <: Λ) ℓ1 ℓ2 | yes (sub-con def1) with sublife? Λ ℓ1 ℓ2
-- if we do find one, then we can prove a sublife relationship
... | yes ih = yes (sub ih)
-- if we don't, then there is no relationship in a well-formed relation (i.e. ¬ (ℓ ≡ ℓ1))
-- but there might be in a non-well-formed relation (i.e. ℓ ≡ ℓ1), so we need to examine that equality
-- (the non-well-formedness comes from duplicate definitions of ℓ1 which allows ℓ1 <: ℓ1)
... | no ¬ih with ℓ == ℓ1
-- if they aren't equal (i.e. well-formed) then there is no relation
... | no ¬eq = no (λ {(rel eq def2) → ¬eq eq ; (sub ih) → ¬ih ih})
-- if they are equal (i.e. not well-formed) we need to check if ℓ2 is defined
sublife? (ℓ1 <: Λ) .ℓ1 ℓ2 | yes (sub-con def1) | no ¬ih | yes refl with defines? ℓ2 Λ
-- if it is, then ℓ1 is related to ℓ2 (this shouldn't ever be an issue if we use well-formed relations)
sublife? (ℓ1 <: Λ) .ℓ1 ℓ2 | yes (sub-con def1) | no ¬ih | yes refl | yes def2 = yes (rel refl def2)
-- if not, then there's no relation
sublife? (ℓ1 <: Λ) .ℓ1 ℓ2 | yes (sub-con def1) | no ¬ih | yes refl | no ¬def2 = no (¬def2 ∘ cons=>def)
-- if ℓ1 is defined by a union of relations, we need to induct into both sides of the union
sublife? (Λ1 & Λ2) ℓ1 ℓ2 | yes (and def1) with sublife? Λ1 ℓ1 ℓ2 | sublife? Λ2 ℓ1 ℓ2
-- if the first half proves it, then we can prove it
... | yes ih1 | ih2? = yes (and (inl ih1))
-- same with the second half
... | no ¬ih1 | yes ih2 = yes (and (inr ih2))
-- if neither side can prove it, then we cannot either
... | no ¬ih1 | no ¬ih2 = no (λ {(and pf) → match ¬ih1 ¬ih2 pf})
-- if the first lifetime isn't defined by the relation, then it definitely isn't related
sublife? Λ ℓ1 ℓ2 | no ¬def1 = no (contrapositive sub=>def-1 ¬def1)

-- lifetime relation well-formedness
data LifeRelWellFormed : LifeRel → Set where
  -- top level relations are always well-formed
  top : ∀ {ℓ} → LifeRelWellFormed (top ℓ)
  -- adding a new lifetime to a well-formed relation is ok if the lifetime isn't already defined
  sub : ∀ {ℓ Λ} → LifeRelWellFormed Λ → ¬ (defines ℓ Λ) → LifeRelWellFormed (ℓ <: Λ)
  -- a union of well-formed relations is well-formed if the two halves define disjoint sets
  and : ∀ {Λ₁ Λ₂} 
      → LifeRelWellFormed Λ₁ 
      → LifeRelWellFormed Λ₂ 
      → (∀ ℓ → ¬ (defines ℓ Λ₁ × defines ℓ Λ₂)) -- both define disjoint sets -
      → LifeRelWellFormed (Λ₁ & Λ₂)
      
-- sublife is irreflexive in a well-formed relation
Λwf-irreflexive : ∀ {Λ ℓ} → LifeRelWellFormed Λ → ¬ (sublife Λ ℓ ℓ)
---- case analysis on the proof of a sublife relationship
-- if the sublife proof is direct proof, then there's only one case for the well-formed proof
-- the sublife proof tells us that Λ defines ℓ, but the well-formed proof tells us the opposite, contradiction
Λwf-irreflexive (sub wf ¬def) (rel refl def) = ¬def def
-- if the sublife proof is an indirect proof, then there's only one case for the well-formed proof
-- we can prove this case by induction
Λwf-irreflexive (sub wf ¬def) (sub pf) = Λwf-irreflexive wf pf
-- there are two cases for the union (each side) and as before only one option for the well-formed proof
-- in the first case, we can induct on the first subrelation
Λwf-irreflexive (and wf1 wf2 ¬def) (and (inl pf)) = Λwf-irreflexive wf1 pf
-- in the second case, we can induct on the second subrelation
Λwf-irreflexive (and wf1 wf2 ¬def) (and (inr pf)) = Λwf-irreflexive wf2 pf

-- sublife is transitive in a well-formed relation
Λwf-transitive : ∀ {Λ ℓ1 ℓ2 ℓ3} → LifeRelWellFormed Λ → sublife Λ ℓ1 ℓ2 → sublife Λ ℓ2 ℓ3 → sublife Λ ℓ1 ℓ3
---- case analysis on the two sublife proofs
-- if both sublife proofs are direct proofs, then we can construct a direct proof
Λwf-transitive wf (rel ℓ≡ℓ1 ℓ2-def) (rel ℓ≡ℓ2 ℓ3-def) = rel ℓ≡ℓ1 ℓ3-def
-- if the first is a direct proof and the second an indirect proof,
-- then we can construct a direct proof by exploiting the indirect proof for a proof of definition
Λwf-transitive wf (rel ℓ≡ℓ1 ℓ2-def) (sub 2<:3) = rel ℓ≡ℓ1 (sub=>def-2 2<:3)
-- if the first is an indirect proof and the second is a direct proof, then we have a contradiction.
-- the first proof requires that Λ defines ℓ2, but the second requires that it doesn't defined ℓ2
-- we can extract the proof of not-defined from the well-formed proof
Λwf-transitive (sub wf ¬ℓ-def) (sub 1<:2) (rel refl ℓ3-def) = exfalso (¬ℓ-def (sub=>def-2 1<:2))
-- if both proofs are indirect proofs, then we can just induct
Λwf-transitive (sub wf ¬ℓ-def) (sub 1<:2) (sub 2<:3) = sub (Λwf-transitive wf 1<:2 2<:3)
--- if both proofs are union proofs, then we need to consider which halves of the unions are used
-- if both come from the same side, then we can just induct
Λwf-transitive (and wf1 wf2 ¬ℓ-def) (and (inl 1<:2)) (and (inl 2<:3)) = and (inl (Λwf-transitive wf1 1<:2 2<:3))
Λwf-transitive (and wf1 wf2 ¬ℓ-def) (and (inr 1<:2)) (and (inr 2<:3)) = and (inr (Λwf-transitive wf2 1<:2 2<:3))
-- if they come from different sides, then we have a contradiction (ℓ2 is defined in both)
Λwf-transitive (and wf1 wf2 ¬ℓ-def) (and (inl 1<:2)) (and (inr 2<:3)) = exfalso (¬ℓ-def _ (sub=>def-2 1<:2 , sub=>def-1 2<:3))
Λwf-transitive (and wf1 wf2 ¬ℓ-def) (and (inr 1<:2)) (and (inl 2<:3)) = exfalso (¬ℓ-def _ (sub=>def-1 2<:3 , sub=>def-2 1<:2))
         
-- Mutability qualifiers
data Mut : Set where
  imm : Mut
  mut : Mut

-- types are parameterized by the lifetimes in scope (can't use undefined lifetimes)
-- structs are rendered as structural types here
data Type (Λ : LifeRel) : Set where
-- type well-formedness mostly involves making sure structs are well formed
data _⊢_wf-type : (Λ : LifeRel) → Type Λ → Set where

-- Context mapping variables to types (we will be using de Bruijn indicies for variables)
Context : LifeRel → Set
Context = List ∘ List ∘ Type
-- contexts are well-formed if all their types are well-formed
_⊢_wf-cxt : (Λ : LifeRel) → Context Λ → Set
Λ ⊢ Γ wf-cxt = All (All (λ t → Λ ⊢ t wf-type)) Γ

-- Addresses are references to slots of memory
module Address where
  -- the implementation of addresses
  data Addr : Set where
  
  -- offset for addresses
  offset : Addr → ℕ → Addr
  offset α n = {!!}
  
  -- fresh address generation (address guaranteed to not be in the provided list)
  fresh : List Addr → Addr
  fresh αs = {!!}
  
  -- decidable equality for addresses
  private
    _=Addr=_ : (x y : Addr) → Dec (x ≡ y)
    x =Addr= y = {!!}
  
  -- implement the Eq typeclass with this equality (allows us to use _==_)
  EqAddr : Eq Addr
  EqAddr = record { _==_ = _=Addr=_ }
open Address public

-- Values are things that can occupy a slot of memory
module Values where
  -- the implementation of values
  data Value : Set where
    void : Value -- what occupies an allocated, but uninitialized slot
    
  -- decidable equality for values
  private
    _=Value=_ : (x y : Value) → Dec (x ≡ y)
    x =Value= y = {!!}
    
  -- implement the Eq type class
  EqValue : Eq Value
  EqValue = record { _==_ = _=Value=_ }
open Values public

-- Heap is a mapping from address to values
Heap = List (Addr × Value)
-- the set of allocated addresses
allocated-addresses : Heap → List Addr
allocated-addresses = map fst
-- judgment for heap lookup
data _[_]≡_ : Heap → Addr → Value → Set where
-- typing for heap values
data heap-type : (Λ : LifeRel) → Heap → Addr → Type Λ → Set where
-- we need a few more things for heap well-formedness

-- Mapping from variables to addresses in the heap (using de Bruijn again)
Locs = List ∘ List $ Addr
-- location map well-formedness has two parts:
_,_,_⊢_wf-locs : (Λ : LifeRel) → Context Λ → Heap → Locs → Set
Λ , Γ , H ⊢ V wf-locs = length Γ ≡ length V -- same domain (length) as context
                      × (flatten V ⊆ allocated-addresses H) -- all mapped to address are in the heap

-- The paths (or lvalues) in Patina
data Path (Λ : LifeRel) (Γ : Context Λ) : Set where
-- typechecking for paths
data _,_⊢_∶_ : (Λ : LifeRel) → (Γ : Context Λ) → Path Λ Γ → Type Λ → Set where
-- paths evalutate to an address in the heap
data _,_,_⊢_⟶_ : (Λ : LifeRel) → (Γ : Context Λ) → Locs → Path Λ Γ → Addr → Set where

-- The set of shallowly deinitialized paths
Deinit : (Λ : LifeRel) → Context Λ → Set
Deinit Λ Γ = List $ Path Λ Γ
-- deinit set equivalence across contexts
data deinit-equiv : (Λ : LifeRel) → (Γ : Context Λ) → Deinit Λ Γ → (Γ′ : Context Λ) → Deinit Λ Γ′ → Set where

-- Heap well-formedness depends on what's in the deinit set
_,_,_,_⊢_wf-heap : (Λ : LifeRel) → (Γ : Context Λ) → Locs → Deinit Λ Γ → Heap → Set
Λ , Γ , V , Δ ⊢ H wf-heap = (∀ p α → p ∈ Δ -- every path considered deinitialized...
                                   → Λ , Γ , V ⊢ p ⟶ α -- evalutates to an address AND
                                   × H [ α ]≡ void) -- the address maps to a heap slot containing void
                          -- also
                          × (∀ p t α v → ¬ (p ∈ Δ) -- every path considered NOT deinitialized...
                                       → Λ , Γ ⊢ p ∶ t -- if it type checks to some type `t`
                                       → Λ , Γ , V ⊢ p ⟶ α  -- then it evalutes to an address AND
                                       × (H [ α ]≡ v × ¬ (v ≡ void)) -- the address maps to a value that is NOT void AND
                                       × heap-type Λ H α t) -- the address contains a value that could be of type `t`

-- The lifetimes of variables
Lifes = List ∘ List $ Life

-- A loan is a record of borrowing a path with a particular mutability for a specific lifetime
Loan : (Λ : LifeRel) → Context Λ → Set
Loan Λ Γ = Life × Mut × Path Λ Γ

-- The bank is the set of loans in effect
Bank : (Λ : LifeRel) → Context Λ → Set
Bank Λ Γ = List $ Loan Λ Γ
-- bank set equivalence across contexts
data bank-equiv : (Λ : LifeRel) → (Γ : Context Λ) → Bank Λ Γ → (Γ′ : Context Λ) → Bank Λ Γ′ → Set where

-- The statements in Patina 
-- parameterized by the lifetime relation and the context so it is impossible to use nonexistant ones
-- theoretically the lifetimes should be erasable
data Stmt (Λ : LifeRel) (Γ : Context Λ) : Set where

-- Typing for statements produces an output bank and deinit list
data _,_,_,_,_⊢_⟶_,_ : (Λ : LifeRel) (Γ : Context Λ) → Lifes → Bank Λ Γ → Deinit Λ Γ → Stmt Λ Γ → Bank Λ Γ → Deinit Λ Γ → Set where

-- A stack frame is a lifetime paired with a list of statements
Frame : (Λ : LifeRel) → Context Λ → Set
Frame Λ Γ = Life × List (Stmt Λ Γ)
-- frame typing consists of simply iterated statement typing
data frame-type : (Λ : LifeRel) (Γ : Context Λ) → Lifes → Bank Λ Γ → Deinit Λ Γ → Frame Λ Γ → Bank Λ Γ → Deinit Λ Γ → Set where
-- A stack is just a list of stack frames
Stack : (Λ : LifeRel) → Context Λ → Set
Stack Λ Γ = List $ Frame Λ Γ
-- similarly, stack typing is just iterated frame typing
data stack-type : (Λ : LifeRel) (Γ : Context Λ) → Lifes → Bank Λ Γ → Deinit Λ Γ → Stack Λ Γ → Bank Λ Γ → Deinit Λ Γ → Set where

-- Function declarations (must be closed so they don't need to be parameterized)
data FuncDecl : Set where
-- Typing for function declarations mostly involves checking the bodies
data ⊢_ok-fn : FuncDecl → Set where

-- A program is a list of functions (since structs are not nominal in this version)
Program = List FuncDecl
-- Typing for programs just means all the functions are ok
⊢_ok-prgm = All ⊢_ok-fn

-- A machine configuration is simply a 5-tuple of program, heap, locations, context, and stack
Config : (Λ : LifeRel) → Set
Config Λ = Program × Heap × Locs × (Σ[ Γ ∈ Context Λ ] Stack Λ Γ)
-- get the context out of the config
config-Γ : {Λ : LifeRel} → Config Λ → Context Λ
config-Γ C = fst (snd (snd (snd C)))
-- predicate for the finish configuration (heap is empty [no leaked memory] and stack is empty [no more commands])
finished : {Λ : LifeRel} → Config Λ → Set
finished (_ , (H , (_ , (_ , St)))) = H ≡ [] × St ≡ []
-- config typing is simply combining all the typing and well-formed conditions
config-type : (Λ : LifeRel) → (C : Config Λ) → Lifes → Deinit Λ (config-Γ C) → Bank Λ (config-Γ C) → Deinit Λ (config-Γ C) → Bank Λ (config-Γ C) → Set
config-type Λ (P , (H , (V , (Γ , St)))) L Δ B Δ′ B′ = ⊢ P ok-prgm -- program is ok
                                                     × Λ , Γ , V , Δ ⊢ H wf-heap -- heap is ok
                                                     × Λ , Γ , H ⊢ V wf-locs -- addr map is ok
                                                     × Λ ⊢ Γ wf-cxt -- context is ok
                                                     × stack-type Λ Γ L B Δ St B′ Δ′ -- stack type checks

-- evalutation is defined on configurations
{- ⟶ = \--> -}
data _⊢_⟶_⊢_ : (Λ : LifeRel) → Config Λ → (Λ′ : LifeRel) → Config Λ′ → Set where

-- given typing and evalutation for configurations, our soundness conditions are:

progress : ∀ {Λ L} {C : Config Λ} {Δ Δ′ : Deinit Λ (config-Γ C)} {B B′ : Bank Λ (config-Γ C)} 
         → config-type Λ C L Δ B Δ′ B′ -- if the configuration typechecks, then either...
         → finished C -- it is the finish configuration OR
         + Σ (Config Λ) (λ C′ → Λ ⊢ C ⟶ Λ ⊢ C′) -- there exists some new configuration we can step to
progress = {!!}

preservation : ∀ {Λ L} {C C′ : Config Λ} {Δ Δ′ : Deinit Λ (config-Γ C)} {B B′ : Bank Λ (config-Γ C)} 
             → config-type Λ C L Δ B Δ′ B′ -- if C typechecks with outputs Δ′ and B′ ...
             → Λ ⊢ C ⟶ Λ ⊢ C′ -- and C steps to C′
             → Σ (Deinit Λ (config-Γ C′) × Bank Λ (config-Γ C′) × Deinit Λ (config-Γ C′) × Bank Λ (config-Γ C′)) -- then there exists Δ′′, B′′, Δ′′′, and B′′′ such that
                 (λ {(Δ′′ , (B′′ , (Δ′′′ , B′′′))) → config-type Λ C′ L Δ′′ B′′ Δ′′′ B′′′ -- C′ typecheckes with the *′′ as inputs and the *′′′ as outputs
                                                   × deinit-equiv Λ (config-Γ C) Δ′ (config-Γ C′) Δ′′′ -- and Δ′ is equivalent to Δ‌′′′
                                                   × bank-equiv Λ (config-Γ C) B′ (config-Γ C′) B′′′ }) -- and B′ is equivalent to B′′′
preservation = {!!}
