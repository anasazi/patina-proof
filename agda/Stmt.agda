open import Common
open import Mut
open import Life
open import Type
open import Path
open import Expr
open import Route
open import Layout
open import Shape
open import Loan

module Stmt where

{-
Statements are indexed by:
- number of functions
- number of free variables
- the lifetime relation
-}
data Stmt : (#f #x #ℓ : ℕ) → Set

-- Functions are indexed by the number of functions (allows recursive calls)
-- TODO handle lifetime variables
record Func (#f : ℕ) : Set where
  constructor fn
  field
    {#args} : ℕ -- implicit number of arguments
    -- The arguments do not have the surrounding lifetime relation in scope
    args : Vec (Type 1) #args
    -- The body has the arguments in scope
    body : Stmt #f #args 1
open Func

data Stmt where
  -- Do nothing
  skip : ∀ {#f #x #ℓ} → Stmt #f #x #ℓ
  -- Sequence two statements with the *same* indicies
  _seq_ : ∀ {#f #x #ℓ} → Stmt #f #x #ℓ → Stmt #f #x #ℓ → Stmt #f #x #ℓ
  -- Create a new variable of the provided type and a Stmt where it is in scope
  push : ∀ {#f #x #ℓ} → Type #ℓ → Stmt #f (S #x) #ℓ → Stmt #f #x #ℓ
  -- Pop a stack variable once the wrapped statement finishes
  pop : ∀ {#f #x #ℓ} → Stmt #f (S #x) #ℓ → Stmt #f (S #x) #ℓ
  -- Create a new concrete lifetime value and a Stmt where it is in scope
  region : ∀ {#f #x #ℓ} → Stmt #f #x (S #ℓ) → Stmt #f #x #ℓ
  -- Pop a concrete lifetime value once the wrapped statement finishes
  unregion : ∀ {#f #x #ℓ} → Stmt #f #x (S #ℓ) → Stmt #f #x (S #ℓ)
  -- Assignment
  _⇐_ : ∀ {#f #x #ℓ} → Path #x → Expr #x #ℓ → Stmt #f #x #ℓ
  -- Free heap memory
  free : ∀ {#f #x #ℓ} → Path #x → Stmt #f #x #ℓ
  -- Call a function
  call : ∀ {#f #x #ℓ n} → Fin #f → Vec (Path #x) n → Stmt #f #x #ℓ
  -- Match by value (the Some block has an extra variable and lifetime in scope)
  matchbyval : ∀ {#f #x #ℓ} → Path #x → Stmt #f (S #x) (S #ℓ) → Stmt #f #x #ℓ → Stmt #f #x #ℓ

-- Upshifting for the #x and #ℓ indicies of Stmt
↑-var-s : ∀ {#f #x #ℓ} → (d : ℕ) → ℕ → Stmt #f #x #ℓ → Stmt #f (plus #x d) #ℓ
↑-var-s d c skip = skip
↑-var-s d c (s₁ seq s₂) = ↑-var-s d c s₁ seq ↑-var-s d c s₂
↑-var-s d c (push τ s) = push τ (↑-var-s d (S c) s)
↑-var-s d c (pop s) = pop (↑-var-s d c s)
↑-var-s d c (region s) = region (↑-var-s d c s)
↑-var-s d c (unregion s) = unregion (↑-var-s d c s)
↑-var-s d c (p ⇐ e) = ↑-var-p′′ d c p ⇐ ↑-var-e′ d c e
↑-var-s d c (free p) = free (↑-var-p′′ d c p)
↑-var-s d c (call f ps) = call f (map (↑-var-p′′ d c) ps)
↑-var-s d c (matchbyval p sₛ sₙ) = matchbyval (↑-var-p′′ d c p)
                                              (↑-var-s d (S c) sₛ)
                                              (↑-var-s d c sₙ)

↑-var-s′ : ∀ {#x #f #ℓ} → (d : ℕ) → ℕ → Stmt #f #x #ℓ → Stmt #f (plus d #x) #ℓ
↑-var-s′ {#x} d c s rewrite plus-comm d #x = ↑-var-s d c s

↑-#ℓ-s : ∀ {#f #x #ℓ} → (d : ℕ) → ℕ → Stmt #f #x #ℓ → Stmt #f #x (plus #ℓ d)
↑-#ℓ-s d c skip = skip
↑-#ℓ-s d c (s₁ seq s₂) = ↑-#ℓ-s d c s₁ seq ↑-#ℓ-s d c s₂
↑-#ℓ-s d c (push τ s) = push (↑-#ℓ-t′ d c τ) (↑-#ℓ-s d c s)
↑-#ℓ-s d c (pop s) = pop (↑-#ℓ-s d c s)
↑-#ℓ-s d c (region s) = region (↑-#ℓ-s d (S c) s)
↑-#ℓ-s d c (unregion s) = unregion (↑-#ℓ-s d c s)
↑-#ℓ-s d c (p ⇐ e) = p ⇐ ↑-#ℓ-e d c e
↑-#ℓ-s d c (free p) = free p
↑-#ℓ-s d c (call f ps) = call f ps
↑-#ℓ-s d c (matchbyval p sₛ sₙ) = matchbyval p (↑-#ℓ-s d (S c) sₛ) (↑-#ℓ-s d c sₙ)

↑-#ℓ-s′ : ∀ {#f #x #ℓ} → (d : ℕ) → ℕ → Stmt #f #x #ℓ → Stmt #f #x (plus d #ℓ)
↑-#ℓ-s′ {_} {_} {#ℓ} d c s rewrite plus-comm d #ℓ = ↑-#ℓ-s d c s

{-
↑-#Ł-s : ∀ {#f #x #ℓ #Ł} → (d : ℕ) → ℕ → Stmt #f #x #ℓ #Ł → Stmt #f #x #ℓ (plus #Ł d)
↑-#Ł-s d c skip = skip
↑-#Ł-s d c (s₁ seq s₂) = ↑-#Ł-s d c s₁ seq ↑-#Ł-s d c s₂
↑-#Ł-s d c (s₁ pop s₂) = ↑-#Ł-s d c s₁ pop ↑-#Ł-s d c s₂
↑-#Ł-s d c (s₁ endregion s₂) = ↑-#Ł-s d c s₁ endregion ↑-#Ł-s d c s₂
↑-#Ł-s d c (push τ s) = push (↑-#Ł-t′ d c τ) (↑-#Ł-s d c s)
↑-#Ł-s d c (region s) = region (↑-#Ł-s d c s)
↑-#Ł-s d c (p ⇐ e) = p ⇐ ↑-#Ł-e d c e
↑-#Ł-s d c (free p) = free p
↑-#Ł-s d c (call f ps) = call f ps
↑-#Ł-s d c (matchbyval p sₛ sₙ) = matchbyval p (↑-#Ł-s d c sₛ) (↑-#Ł-s d c sₙ)

↑-#Ł-s′ : ∀ {#f #x #ℓ #Ł} → (d : ℕ) → ℕ → Stmt #f #x #ℓ #Ł → Stmt #f #x #ℓ (plus d #Ł)
↑-#Ł-s′ {_} {_} {_} {#Ł} d c s rewrite plus-comm d #Ł = ↑-#Ł-s d c s
-}

{-
Converting a function body into a statement
Basically, we wrap the body in push statements for the arguments and then one region statement for the block lifetime
-}
conv-helper : ∀ {n #x #f #ℓ} → Vec (Type #ℓ) n → Vec (Path #x) n → Stmt #f (plus n #x) #ℓ → Stmt #f #x #ℓ
conv-helper [] [] s = s
conv-helper {S n} (τ ∷ τs) (p ∷ ps) s = conv-helper τs ps (push τ ((var fZ ⇐ use (↑-var-p′′′ (S n) 0 p)) seq s))

test-conv-helper-1 : conv-helper {_} {_} {0} ([ int {0} ]) ([ var {10} (fin 5) ]) skip
            ≡ push int ((var fZ ⇐ use (var (fin 6))) seq skip)
test-conv-helper-1 = refl
test-conv-helper-2 : conv-helper {_} {_} {0} ([ int {0} ,, ~ int ]) ([ var {10} (fin 5) ,, var (fin 3) ]) (free (var (fin 1)))
            ≡ push (~ int) ((var fZ ⇐ use (var (fin 4))) seq push int ((var fZ ⇐ use (var (fin 7))) seq free (var (fin 1))))
test-conv-helper-2 = refl

-- TODO fix lifetime parameters
conv : ∀ {n #x #f} #ℓ → Vec (Type 1) n → Vec (Path #x) n → Stmt #f n 1 → Stmt #f #x #ℓ
conv {n} {#x} {_} #ℓ τs ps s = region (conv-helper (rev (map (↑-#ℓ-t′ #ℓ 1) τs)) (rev ps) (↑-#ℓ-s #ℓ 1 (↑-var-s #x n s)))
--conv : ∀ {n #x #f} #ℓ #Ł → Vec (Type 1 0) n → Vec (Path #x) n → Stmt #f n 1 0 → Stmt #f #x #ℓ #Ł
--conv {n} {#x} {_} #ℓ #Ł τs ps s = region (conv-helper (rev (map (↑-#ℓ-t′ #ℓ 1 ∘ ↑-#Ł-t′ #Ł 0) τs)) (rev ps) (↑-#Ł-s #Ł 0 (↑-#ℓ-s #ℓ 1 (↑-var-s #x n s))))

test-conv-1 : conv {_} {_} {0} 1 ([ ~ int ,, int ]) ([ var {10} (fin 3) ,, var (fin 5) ]) (free (var (fin 1)))
            ≡ region (push (~ int) ((var fZ ⇐ use (var (fin 4))) seq push int ((var fZ ⇐ use (var (fin 7))) seq free (var (fin 1)))))
test-conv-1 = refl
test-conv-2 : conv {_} {_} {0} 1 ([ & (val (fin 0)) imm int ]) ([ var {10} (fin 3) ]) skip
            ≡ region (push (& (val (fin 0)) imm int) ((var fZ ⇐ use (var (fin 4))) seq skip))
test-conv-2 = refl

-- Typing for statements.
data stok {#f} (F : Vec (Func #f) #f) : (#x #ℓ : ℕ) → Vec (Type #ℓ) #x → Vec (Shape #ℓ) #x
                                      → Stmt #f #x #ℓ → Vec (Shape #ℓ) #x → Set

-- Typing for functions.
record fnok {#f} (F : Vec (Func #f) #f) (func : Func #f) : Set where
  constructor fn
  field
    {Δ} : Vec (Shape 1) _
    -- The body is a well-typed statement when the arguments are in scope (initialized)
    body-ok : stok F _ 1
                   (rev (args func))
                   (rev (map init-t (args func)))
                   (body func)
                   Δ
    -- The body cleans up after itself (freeing any heap memory it was responsible for)
    cleans-up : All (λ x → fst x ⊢ snd x Dropped) (zip (rev (args func)) Δ)

data stok {#f} (F : Vec (Func #f) #f) where
  -- Skip changes nothing
  skip : ∀ {#x #ℓ Γ Δ} → stok F #x #ℓ Γ Δ skip Δ
  -- Seq threads Shape data through the statements
  _seq_ : ∀ {#x #ℓ Γ Δ₀ Δ₁ Δ₂ s₁ s₂}
        → stok F #x #ℓ Γ Δ₀ s₁ Δ₁
        → stok F #x #ℓ Γ Δ₁ s₂ Δ₂
        → stok F #x #ℓ Γ Δ₀ (s₁ seq s₂) Δ₂ 
  -- Push ensures that the wrapped statement
  push : ∀ {#x #ℓ Γ Δ τ s δ′ Δ′}
       -- is well typed when the context is extended
       → stok F (S #x) #ℓ (τ ∷ Γ) (void-t τ ∷ Δ) s (δ′ ∷ Δ′)
       -- cleans up after itself if necessary
       → τ ⊢ δ′ Dropped
       → stok F #x #ℓ Γ Δ (push τ s) Δ′
  -- Pop is just a flag to the evalutator
  pop : ∀ {#x #ℓ Γ Δ s Δ′}
         → stok F (S #x) #ℓ Γ Δ s Δ′
         → stok F (S #x) #ℓ Γ Δ (pop s) Δ′
  -- Region ensures that the wrapped statement
  region : ∀ {#x #ℓ Γ Δ s Δ′ ↓Δ′}
         -- is well typed when the lifetime relation is extended
         → stok F #x (S #ℓ) (map (↑-#ℓ-t 1 0) Γ) (map (↑-#ℓ-sh 1 0) Δ) s Δ′
         -- provides output Shape data that can be downshifted
         → ↓1-#ℓ-shs 0 Δ′ ↓Δ′
         → stok F #x #ℓ Γ Δ (region s) ↓Δ′
  -- Unregion is just a flag tot he evalutator
  unregion : ∀ {#x #ℓ Γ Δ₀ s Δ₁}
           → stok F #x (S #ℓ) Γ Δ₀ s Δ₁
           → stok F #x (S #ℓ) Γ Δ₀ (unregion s) Δ₁
  -- Assignment is ok if
  ⇐ok : ∀ {#x #ℓ Γ Δ₀ p e τᵣ τₗ Δ₁ Δ₂}
      -- the RHS is well typed
      → Γ , Δ₀ ⊢ e ∶ τᵣ , Δ₁ expr
      -- the LHS can be initialized once we've used the RHS
      → Δ₁ ⊢ p can-init
      -- the LHS is well typed
      → Γ ⊢ p ∶ τₗ
      -- the RHS is a subtype of the LHS
      → τᵣ <: τₗ
      -- the LHS can be marked initialized in the output
      → Γ , Δ₁ ⊢ p ⇒ Δ₂ init
      → stok F #x #ℓ Γ Δ₀ (p ⇐ e) Δ₂
  -- Free is ok if
  free : ∀ {#x #ℓ Γ Δ₀ p τ δ Δ₁}
       -- The argument is a unique pointer
       → Γ ⊢ p ∶ ~ τ
       -- With cleaned up contents
       → Δ₀ ⊢ * p ∶ δ shape
       → τ ⊢ δ Dropped
       -- So we mark it as deinitialized in the output
       → Γ , Δ₀ ⊢ p ⇒ Δ₁ deinit
       → stok F #x #ℓ Γ Δ₀ (free p) Δ₁
  -- Calling a function is ok if
  call : ∀ {#x #ℓ Γ Δ₀ Δ₁ f τs} {ps : Vec (Path #x) (#args (F ! f))}
       -- the function is well formed
       → fnok F (F ! f)
       -- we can safely use the arguments
       → Γ , Δ₀ ⊢ ps ∶ τs , Δ₁ use-many
       -- and formal parameter types are subtypes of the argument types
       → All (λ { (f , p) → f <: p })
             (zip (map (↑-#ℓ-t′ #ℓ 0) (args (F ! f)))
                  (map (↑-#ℓ-t 1 0) τs))
       → stok F #x #ℓ Γ Δ₀ (call f ps) Δ₁
  -- Matching by value is ok if
  matchbyval : ∀ {#x #ℓ Γ Δ₀ p sₛ sₙ τ Δ₁ Δ₂} -- δ}
             -- path safe to use (and is an option)
             → Γ , Δ₀ ⊢ p ∶ opt τ , Δ₁ use
             ---- arms of match are ok
             -- Some:
             -- there is a shape
             → (δ : Shape #ℓ)
             -- that's cleaned up
             → τ ⊢ δ Dropped
             -- which can be left over after evalutating the block
             → stok F (S #x) (S #ℓ)
                    (map (↑-#ℓ-t 1 0) (τ ∷ Γ))
                    (map (↑-#ℓ-sh 1 0) ((init-t τ) ∷ Δ₁))
                    sₛ
                    (map (↑-#ℓ-sh 1 0) (δ ∷ Δ₂))
             -- None:
             -- the body is ok
             → stok F #x #ℓ Γ Δ₁ sₙ Δ₂
             ---- the arms are consistent
             -- note that we required the none arm and the some arm to share Δ₂
             -- so they have the same init/loan info
             → stok F #x #ℓ Γ Δ₀ (matchbyval p sₛ sₙ) Δ₂

test-stok-1 : stok [] 0 0 [] [] (push int skip) []
test-stok-1 = push skip int
test-stok-2 : stok [] 0 0 [] [] (push int (var fZ ⇐ int 1)) []
test-stok-2 = push (⇐ok int (int void , (var , int)) var int (int , (var , var))) int
test-stok-3 : stok [] 3 0 ([ opt int ,, int ,, int ])
              ([ opt (init (bank-def _) tt) ,, int (init (bank-def _) tt) ,, int void ])
              (matchbyval (var fZ)
                (var (fin 3) ⇐ add (var (fin 0)) (var (fin 2)))
                (var (fin 2) ⇐ int 0))
              ([ opt (init (bank-def _) tt) ,, int (init (bank-def _) tt) ,, int (init (bank-def _) tt) ])
test-stok-3 = matchbyval (copy var (opt int) (can-access (_ , (var , opt))))
                         (int (init (bank [] free) tt))
                         int
                         (⇐ok (add (copy var int (can-access (_ , (var , int))))
                                   (copy var int (can-access (_ , (var , int)))))
                              (int void , (var , int)) var int (int , (var , var)))
                         (⇐ok int (int void , (var , int)) var int (int , (var , var)))
test-stok-4 : stok [] 1 0 ([ ~ int ]) ([ ~ (init (bank-def _) (int (init (bank-def _) tt))) ])
              (free (var fZ)) ([ ~ void ])
test-stok-4 = free var (*~ var) int (~ int , (var , var))
test-stok-5 : ¬ (stok [] 1 0 ([ ~ (~ int) ]) ([ ~ (init (bank-def _) (~ (init (bank-def _) (int (init (bank-def _) tt))))) ])
                (pop skip) ([ ~ void ]))
test-stok-5 (pop ())
test-stok-6 : stok [] 1 0 ([ ~ (~ int) ]) ([ ~ void ]) (pop skip) ([ ~ void ])
test-stok-6 = pop skip
test-stok-7 : stok ([ fn ([ int ,, int ]) skip ])
                   2 0 
                   ([ int ,, int ])
                   ([ int (init (bank-def _) tt) ,, int (init (bank-def _) tt) ])
                   (call fZ ([ var (fin 0) ,, var (fin 1) ]))
                   ([ int (init (bank-def _) tt) ,, int (init (bank-def _) tt) ])
test-stok-7 = call (fn skip (int ∷ int ∷ []))
                   (copy var int (can-access ((int (init (bank [] free) tt)) , (var , int)))
                  ∷ copy var int (can-access ((int (init (bank [] free) tt)) , (var , int)))
                  ∷ [])
                   (int ∷ int ∷ [])
test-stok-8 : stok [] 1 3
              ([ & (val (fin 1)) imm (& (val (fin 2)) imm int) ])
              ([ & (init (bank-def _) (& (val (fin 2)) imm int)) ])
              (unregion skip)
              ([ & (init (bank-def _) (& (val (fin 2)) imm int)) ])
test-stok-8 = unregion skip

test-fnok-1 : fnok [] (fn ([ ~ int ,, ~ int ]) (free (var fZ) seq free (var (fin 1))))
test-fnok-1 = fn (free var (*~ var) int (~ int , (var , var)) seq
                  free var (*~ var) int (~ int , (var , var)))
                 (~ ∷ ~ ∷ [])
test-fnok-2 : ¬ (fnok [] (fn ([ ~ int ]) skip))
test-fnok-2 (fn skip (() ∷ []))

-- Statement evalutation can change the number of variables, allocations, or the lifetime relation
data stev {#f} (F : Vec (Func #f) #f) : (#x₁ #a₁ #ℓ₁ : ℕ) → Vec (Type #ℓ₁) #x₁ → Vec (Fin #a₁) #x₁
               → Vec (Layout #a₁) #a₁ → Stmt #f #x₁ #ℓ₁ 
               → (#x₂ #a₂ #ℓ₂ : ℕ) → Vec (Type #ℓ₂) #x₂ → Vec (Fin #a₂) #x₂
               → Vec (Layout #a₂) #a₂ → Stmt #f #x₂ #ℓ₂ → Set where
  -- if the LHS of a seq finishes, then proceed to the RHS
  skipseq : ∀ {#x #a #ℓ T V H s} → stev F #x #a #ℓ T V H (skip seq s) #x #a #ℓ T V H s
  -- if the LHS of a seq can step, then step it
  stepseq : ∀ {#x #ℓ #a₁ T V₁ H₁ s₁ #a₂ V₂ H₂ s₁′ s₂}
          → stev F #x #a₁ #ℓ T V₁ H₁ s₁ #x #a₂ #ℓ T V₂ H₂ s₁′
          → stev F #x #a₁ #ℓ T V₁ H₁ (s₁ seq s₂) #x #a₂ #ℓ T V₂ H₂ (s₁′ seq s₂)
  -- to push a new stack variable
  push : ∀ {#x #a #ℓ T V H τ s l}
       -- determine an uninitialized layout
       → layoutof τ l
       → stev F #x #a #ℓ T V H (push τ s)
         -- extend the context with the type
         (S #x) (S #a) #ℓ (τ ∷ T)
         -- map the new variable to the new allocation
         (fZ ∷ map (raise 1) V)
         -- which is just the empty layout we created
         (l ∷ (map (↑-alloc-l 1 0) H))
         -- change the push to a pop
         (pop s)
  -- if the statement in a pop is finished
  pop-skip : ∀ {#x #a #ℓ τ T α V ↓V l H ↓H}
              -- downshift the map
              → ↓xs 0 V ↓V
              -- and the heap
              → ↓-#a-ls 0 H ↓H
              → stev F (S #x) (S #a) #ℓ (τ ∷ T) (α ∷ V) (l ∷ H) (pop skip) #x #a #ℓ T ↓V ↓H skip
  -- if the statement in a pop can step, then step it
  pop-step : ∀ {#x #a #ℓ T V H s #a′ V′ H′ s′}
              → stev F (S #x) #a #ℓ T V H s (S #x) #a′ #ℓ T V′ H′ s′
              → stev F (S #x) #a #ℓ T V H (pop s) (S #x) #a′ #ℓ T V′ H′ (pop s′)
  -- to push a new region, just upshift the type context
  region : ∀ {#x #a #ℓ T V H s}
         → stev F #x #a #ℓ T V H (region s) #x #a (S #ℓ) (map (↑-#ℓ-t 1 0) T) V H (unregion s)
  -- if the statement in a unregion is down, then downshift the context
  unregion-skip : ∀ {#x #a #ℓ T V H ↓T}
                → ↓1-#ℓ-ts 0 T ↓T
                → stev F #x #a (S #ℓ) T V H (unregion skip) #x #a #ℓ ↓T V H skip
  -- if the statement in an unregion can step, then step it
  unregion-step : ∀ {#x #a #ℓ T V H s #a′ V′ H′ s′}
                → stev F #x #a (S #ℓ) T V H s #x #a′ (S #ℓ) T V′ H′ s′
                → stev F #x #a (S #ℓ) T V H (unregion s) #x #a′ (S #ℓ) T V′ H′ (unregion s′)
  -- assign an expression to a path by
  ⇐ev : ∀ {#x #a #ℓ T V Hᵢ Hₒ p e α}
      -- finding where the path points to
      → T , V , Hᵢ ⊢ p ⟶ α
      -- and using it as the destination for evaluating the expression
      → #a ∣ T , V , Hᵢ ⊢ α ← e ⟶ #a ∣ Hₒ
      → stev F #x #a #ℓ T V Hᵢ (p ⇐ e) #x #a #ℓ T V Hₒ skip
  -- similar, but the new expression increments the allocation count, so we need to shift some things
  ⇐ev-new : ∀ {#x #a #ℓ T V Hᵢ Hₒ p e α}
          → T , V , Hᵢ ⊢ p ⟶ α
          → #a ∣ T , V , Hᵢ ⊢ α ← e ⟶ S #a ∣ Hₒ
          → stev F #x #a #ℓ T V Hᵢ (p ⇐ e) #x (S #a) #ℓ T (map (raise 1) V) Hₒ skip
  -- free heap memory by
  free : ∀ {#x #a #ℓ T V H p α α′ H′ H′′}
       -- finding where the path goes
       → T , map (↑-fin 1 (asℕ α′)) V , H ⊢ p ⟶ α
       -- finding which allocation it points to
       → H ⊢ α ⇒ ptr (val (alloc α′))
       -- set it to void
       → H ⊢ α ≔ ptr void ⇒ H′
       -- remove the pointed-to allocation from the heap
       → remove-elem H′ α′ (map (↑-alloc-l 1 (asℕ α′)) H′′)
       → stev F #x (S #a) #ℓ T (map (↑-fin 1 (asℕ α′)) V) H (free p) #x #a #ℓ T V H′′ skip
  -- call a function by replacing the call with the expanded body
  call : ∀ {#x #a #ℓ T V H f} {ps : Vec (Path #x) (#args (F ! f))}
       → stev F #x #a #ℓ T V H (call f ps)
                #x #a #ℓ T V H (conv #ℓ (args (F ! f)) ps (body (F ! f)))
  -- match on a none by value by
  matchnonebyval : ∀ {#x #a #ℓ T V H p sₛ sₙ α l}
                 -- finding out where the path goes
                 → T , V , H ⊢ p ⟶ α
                 -- ensuring a none occupies p
                 → H ⊢ α ⇒ rec ([ int (val 0) ,, l ])
                 -- and then going to the none statement
                 → stev F #x #a #ℓ T V H (matchbyval p sₛ sₙ) #x #a #ℓ T V H sₙ
  -- match on a some by value by
  matchsomebyval : ∀ {#x #a #ℓ T V H p sₛ sₙ α l τ}
                 -- ensuring the path points to an option
                 → T ⊢ p ∶ opt τ
                 -- finding out where it points
                 → T , V , H ⊢ p ⟶ α
                 -- ensuring a some occupies that spot
                 → H ⊢ α ⇒ rec ([ int (val 1) ,, l ])
                 -- pushing the contents onto the stack and executing the some statement
                 → stev F #x #a #ℓ T V H (matchbyval p sₛ sₙ)
                          (S #x) (S #a) (S #ℓ)
                          (map (↑-#ℓ-t 1 0) (τ ∷ T))
                          (fZ ∷ map (raise 1) V)
                          (map (↑-alloc-l 1 0) (l ∷ H))
                          (unregion (pop sₛ))

test-stev-1 : stev [] 0 0 0 [] [] [] (push int skip)
                   1 1 0 ([ int ]) ([ fZ ]) ([ int void ]) (pop skip)
test-stev-1 = push int
test-stev-2 : stev [] 1 1 0 ([ int ]) ([ fZ ]) ([ int void ]) (pop skip)
                   0 0 0 [] [] [] skip 
test-stev-2 = pop-skip [] []
test-stev-3 : stev [] 1 1 0 ([ int ]) ([ fZ ]) ([ int void ]) (var fZ ⇐ int 1)
                   1 1 0 ([ int ]) ([ fZ ]) ([ int (val 1) ]) skip
test-stev-3 = ⇐ev var (int alloc)
test-stev-4 : stev [] 1 1 0 ([ int ]) ([ fZ ]) ([ int (val 1) ]) (pop skip)
                   0 0 0 [] [] [] skip 
test-stev-4 = pop-skip [] []
test-stev-5 : stev [] 3 3 0
              ([ opt int ,, int ,, int ])
              ([ fin 0 ,, fin 1 ,, fin 2 ])
              ([ rec ([ int (val 0) ,, int void ]) ,, int (val 1) ,, int void ])
              (matchbyval (var fZ)
                          (var (fin 3) ⇐ add (var (fin 0)) (var (fin 2)))
                          (var (fin 2) ⇐ int 0))
              3 3 0
              ([ opt int ,, int ,, int ])
              ([ fin 0 ,, fin 1 ,, fin 2 ])
              ([ rec ([ int (val 0) ,, int void ]) ,, int (val 1) ,, int void ])
              (var (fin 2) ⇐ int 0)
test-stev-5 = matchnonebyval var alloc
test-stev-6 : stev [] 3 3 0
              ([ opt int ,, int ,, int ])
              ([ fin 0 ,, fin 1 ,, fin 2 ])
              ([ rec ([ int (val 1) ,, int (val 1) ]) ,, int (val 1) ,, int void ])
              (matchbyval (var fZ)
                          (var (fin 3) ⇐ add (var (fin 0)) (var (fin 2)))
                          (var (fin 2) ⇐ int 0))
              4 4 1
              ([ int ,, opt int ,, int ,, int ])
              ([ fin 0 ,, fin 1 ,, fin 2 ,, fin 3 ])
              ([ int (val 1) ,, rec ([ int (val 1) ,, int (val 1) ]) ,, int (val 1) ,, int void ])
              (unregion (pop (var (fin 3) ⇐ add (var (fin 0)) (var (fin 2)))))
test-stev-6 = matchsomebyval var var alloc
test-stev-7 : stev [] 2 2 0
                   ([ ~ int ,, int ])
                   ([ fin 0 ,, fin 1 ])
                   ([ ptr void ,, int (val 1) ])
                   (var fZ ⇐ new (var (fin 1)))
                   2 3 0
                   ([ ~ int ,, int ])
                   ([ fin 1 ,, fin 2 ])
                   ([ int (val 1) ,, ptr (val (alloc fZ)) ,, int (val 1) ])
                   skip
test-stev-7 = ⇐ev-new var (new var int var (int (val 1) , (alloc , alloc)) alloc)
test-stev-8 : stev [] 1 5 0
                   ([ ~ (~ (~ (~ int))) ])
                   ([ fZ ])
                   ([ ptr (val (alloc (fin 3)))
                   ,, ptr (val (alloc (fin 4)))
                   ,, int (val 1)
                   ,, ptr (val (alloc (fin 1)))
                   ,, ptr (val (alloc (fin 2))) ])
                   (free (* (* (* (var fZ)))))
                   1 4 0
                   ([ ~ (~ (~ (~ int))) ])
                   ([ fZ ])
                   ([ ptr (val (alloc (fin 2)))
                   ,, ptr (val (alloc (fin 3)))
                   ,, ptr (val (alloc (fin 1)))
                   ,, ptr void ])
                   skip
test-stev-8 = free (* (* (* var)))
                   (* (* (* alloc alloc) alloc) alloc)
                   (* (* (* alloc alloc) alloc) alloc)
                   (re-S (re-S re-Z))
test-stev-9 : stev ([ fn ([ int ,, int ]) skip ])
                   2 2 0
                   ([ int ,, int ])
                   ([ fin 0 ,, fin 1 ])
                   ([ int (val 1) ,, int (val 2) ])
                   (call (fin 0) ([ var (fin 0) ,, var (fin 1) ]))
                   2 2 0
                   ([ int ,, int ])
                   ([ fin 0 ,, fin 1 ])
                   ([ int (val 1) ,, int (val 2) ])
                   (region
                     (push int ((var fZ ⇐ use (var (fin 1))) seq
                      push int ((var fZ ⇐ use (var (fin 3))) seq
                      skip))))
test-stev-9 = call
