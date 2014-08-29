open import Common
open import Type
open import Path
open import Route
open import Layout
open import Shape
open import Loan

module Expr where

data Expr (#x #ℓ : ℕ) : Set where
  int : ℕ → Expr #x #ℓ
  add : Path #x → Path #x → Expr #x #ℓ
  use : Path #x → Expr #x #ℓ
  new : Path #x → Expr #x #ℓ
  some : Path #x → Expr #x #ℓ
  none : Type #ℓ → Expr #x #ℓ

↑#x-e : ∀ {#x #ℓ} → ℕ → Expr #x #ℓ → Expr (S #x) #ℓ
↑#x-e c (int n) = int n
↑#x-e c (add p₁ p₂) = add (↑#x-p c p₁) (↑#x-p c p₂)
↑#x-e c (use p) = use (↑#x-p c p)
↑#x-e c (new p) = new (↑#x-p c p)
↑#x-e c (some p) = some (↑#x-p c p)
↑#x-e c (none τ) = none τ

↑#ℓ-e : ∀ {#x #ℓ} → ℕ → Expr #x #ℓ → Expr #x (S #ℓ)
↑#ℓ-e c (int n) = int n
↑#ℓ-e c (add p₁ p₂) = add p₁ p₂
↑#ℓ-e c (use p) = use p
↑#ℓ-e c (new p) = new p
↑#ℓ-e c (some p) = some p
↑#ℓ-e c (none τ) = none (↑#ℓ-τ c τ)

data _,_⊢_∶_,_ {#x #ℓ} (Γ : Context #ℓ #x) : State #ℓ #x → Expr #x #ℓ
               → Type #ℓ → State #ℓ #x → Set where
  int : ∀ {n Δ} → Γ , Δ ⊢ int n ∶ int , Δ
  add : ∀ {p₁ p₂ Δ} → Γ , Δ ⊢ p₁ ∶ int ⇒ Δ → Γ , Δ ⊢ p₂ ∶ int ⇒ Δ → Γ , Δ ⊢ add p₁ p₂ ∶ int , Δ
  use : ∀ {Δᵢ p τ Δₒ} → Γ , Δᵢ ⊢ p ∶ τ ⇒ Δₒ → Γ , Δᵢ ⊢ use p ∶ τ , Δₒ
  new : ∀ {Δᵢ p τ Δₒ} → Γ , Δᵢ ⊢ p ∶ τ ⇒ Δₒ → Γ , Δᵢ ⊢ new p ∶ ~ τ , Δₒ
  some : ∀ {Δᵢ p τ Δₒ} → Γ , Δᵢ ⊢ p ∶ τ ⇒ Δₒ → Γ , Δᵢ ⊢ some p ∶ opt τ , Δₒ
  none : ∀ {Δ τ} → {- TODO wellformed check on τ -} Γ , Δ ⊢ none τ ∶ opt τ , Δ

data _,_⊢_⟶_ {#x #ℓ #a} (Γ : Context #ℓ #x) (M : Mem #x #a) : Expr #x #ℓ
              → (Layout #x #a × Mem #x #a) + (Layout #x (S #a) × Mem #x (S #a)) → Set where
  int : ∀ {n} → Γ , M ⊢ int n ⟶ inl (int (just n) , M)
  add : ∀ {p₁ p₂ r₁ r₂ n₁ n₂ n}
      → ⊢ p₁ ⟶ r₁
      → ⊢ p₂ ⟶ r₂
      → M ⊢ r₁ ⇒ int (just n₁)
      → M ⊢ r₂ ⇒ int (just n₂)
      → n ≡ plus n₁ n₂
      → Γ , M ⊢ add p₁ p₂ ⟶ inl (int (just n) , M)
  use : ∀ {p τ r l M′}
      → Γ ⊢ p ∶ τ
      → ⊢ p ⟶ r
      → M ⊢ r ∶ τ ⇒ l , M′
      → Γ , M ⊢ use p ⟶ inl (l , M′)
  new : ∀ {p τ r l M′ M′′}
      → Γ ⊢ p ∶ τ
      → ⊢ p ⟶ r
      → M ⊢ r ∶ τ ⇒ l , M′
      → (map (↑#a-l 0) *** map (↑#a-l 0)) (second (_∷_ l) M′) ⊢ heap fZ ≔ ↑#a-l 0 l ⇒ M′′
      → Γ , M ⊢ new p ⟶ inr ((ptr (just (heap fZ))) , M′′)
  some : ∀ {p τ r l M′}
       → Γ ⊢ p ∶ τ
       → ⊢ p ⟶ r
       → M ⊢ r ∶ τ ⇒ l , M′
       → Γ , M ⊢ some p ⟶ inl (rec ([ int (just 1) ,, l ]) , M′)
  none : ∀ {τ}
       → Γ , M ⊢ none τ ⟶ inl (rec ([ int (just 0) ,, void-layout τ ]) , M)
      
module TestEval where
  rvok-1 : ([ int {0} ]) , [ int (just (bank-def _)) ] ⊢ int 1 ∶ int , ([ int (just (bank-def _)) ])
  rvok-1 = int
  rvok-2 : ([ int {0} ,, int ])
         , [ int (just (bank-def _)) ,, int (just (bank-def _)) ]
         ⊢ add (var (fin 0)) (var (fin 1)) ∶ int
         , ([ int (just (bank-def _)) ,, int (just (bank-def _)) ])
  rvok-2 = add (copy var int ((int (just (bank [] free))) , (var , int)))
               (copy var int ((int (just (bank [] free))) , (var , int)))
  rvok-3 : ¬ (([ int {0} ,, int ])
              , [ int none ,, int (just (bank-def _)) ]
              ⊢ add (var (fin 0)) (var (fin 1)) ∶ int
              , ([ int none ,, int (just (bank-def _)) ]))
  rvok-3 (add (copy Hτ τCopy (.(int none) , (var , ()))) p₂)
  rvok-3 (add (move Hτ () own init void) p₂)
  rvok-4 : ([ ~ {0} int ])
         , [ ~ (just ((bank-def _) , (int (just (bank-def _))))) ]
         ⊢ use (var fZ)
         ∶ ~ int
         , ([ ~ none ])
  rvok-4 = use (move var ~Aff var
               (~ (just (bank [] free , int (just (bank [] free)))) , (var , ~ int))
               (~ int , (var , var)))
  rvok-5 : ([ int {0} ])
         , [ int (just (bank-def _)) ]
         ⊢ new (var fZ) ∶ ~ int
         , ([ int (just (bank-def _)) ])
  rvok-5 = new (copy var int (int (just (bank [] free)) , (var , int)))

  rveval-1 : [] , [] , [] ⊢ int {0} {0} 0 ⟶ inl (int (just 0) , ([] , []))
  rveval-1 = int
  rveval-2 : ([ int {0} ,, int ])
           , ([ int (just 1) ,, int (just 2) ]) , []
           ⊢ add (var (fin 0)) (var (fin 1)) ⟶ inl (int (just 3)
           , (([ int (just 1) ,, int (just 2) ]) , []))
  rveval-2 = add var var stack stack refl
  rveval-3 : ¬ (([ int {0} ,, int ])
                , ([ int none ,, int (just 2) ]) , []
                ⊢ add (var (fin 0)) (var (fin 1)) ⟶ inl (int (just 3)
                , (([ int none ,, int (just 2) ]) , [])))
  rveval-3 (add var p₂⟶r₂ () r₂⇒n₂ n₁+n₂)
  rveval-4 : ([ int {0} ]) , ([ int (just 10) ]) , []
           ⊢ some (var (fin 0)) ⟶ inl (rec ([ int (just 1) ,, int (just 10) ])
           , (([ int (just 10) ]) , []))
  rveval-4 = some var var (copy int stack)
  rveval-5 : [] , [] , [] ⊢ none {0} {0} int ⟶ inl (rec ([ int (just 0) ,, int none ]) , ([] , []))
  rveval-5 = none
  rveval-6 : ([ ~ {0} int ]) , ([ ptr (just (heap fZ)) ]) , ([ int (just 1) ])
           ⊢ use (var fZ) ⟶ inl (ptr (just (heap fZ)) , (([ ptr none ]) , ([ int (just 1) ])))
  rveval-6 = use var var (move ~Aff stack stack)
  rveval-7 : ([ ~ {0} int ]) , ([ ptr (just (heap fZ)) ]) , ([ int (just 1) ,, int (just 2) ])
           ⊢ use (var fZ) ⟶ inl (ptr (just (heap fZ))
           , (([ ptr none ]) , ([ int (just 1) ,, int (just 2) ])))
  rveval-7 = use var var (move ~Aff stack stack)
  rveval-8 : ([ int {0} ]) , ([ int (just 10) ]) , []
           ⊢ new (var fZ) ⟶ inr (ptr (just (heap fZ)) , (([ int (just 10) ]) , ([ int (just 10) ])))
  rveval-8 = new var var (copy int stack) heap

-- -- Exprs are indexed by the number of variables and the lifetime relation
-- data Expr : (#x #ℓ : ℕ) → Set where
--   int : ∀ {#x #ℓ} → ℕ → Expr #x #ℓ
--   add : ∀ {#x #ℓ} → Path #x → Path #x → Expr #x #ℓ
--   use : ∀ {#x #ℓ} → Path #x → Expr #x #ℓ
--   new : ∀ {#x #ℓ} → Path #x → Expr #x #ℓ
--   some : ∀ {#x #ℓ} → Path #x → Expr #x #ℓ
--   none : ∀ {#x #ℓ} → Type #ℓ → Expr #x #ℓ

-- -- upshifting for the indicies of Expr
-- ↑-var-e : ∀ {#x #ℓ} → (amt : ℕ) → (cut : Fin #x) → Expr #x #ℓ → Expr (plus amt #x) #ℓ
-- ↑-var-e d c (int n) = int n
-- ↑-var-e d c (add p₁ p₂) = add (↑-var-p d c p₁) (↑-var-p d c p₂)
-- ↑-var-e d c (use p) = use (↑-var-p d c p)
-- ↑-var-e d c (new p) = new (↑-var-p d c p)
-- ↑-var-e d c (some p) = some (↑-var-p d c p)
-- ↑-var-e d c (none τ) = none τ

-- ↑-var-e′ : ∀ {#x #ℓ} → (d : ℕ) → ℕ → Expr #x #ℓ → Expr (plus #x d) #ℓ
-- ↑-var-e′ d c (int n) = int n
-- ↑-var-e′ d c (add p₁ p₂) = add (↑-var-p′′ d c p₁) (↑-var-p′′ d c p₂)
-- ↑-var-e′ d c (use p) = use (↑-var-p′′ d c p)
-- ↑-var-e′ d c (new p) = new (↑-var-p′′ d c p)
-- ↑-var-e′ d c (some p) = some (↑-var-p′′ d c p)
-- ↑-var-e′ d c (none τ) = none τ

-- ↑-#ℓ-e : ∀ {#x #ℓ} → (d : ℕ) → ℕ → Expr #x #ℓ → Expr #x (plus #ℓ d)
-- ↑-#ℓ-e d c (int n) = int n
-- ↑-#ℓ-e d c (add p₁ p₂) = add p₁ p₂
-- ↑-#ℓ-e d c (use p) = use p
-- ↑-#ℓ-e d c (new p) = new p
-- ↑-#ℓ-e d c (some p) = some p
-- ↑-#ℓ-e d c (none τ) = none (↑-#ℓ-t′ d 0 τ)

-- {-
-- ↑-#Ł-e : ∀ {#x #ℓ} → (d : ℕ) → ℕ → Expr #x #ℓ #Ł → Expr #x #ℓ (plus #Ł d)
-- ↑-#Ł-e d c (int n) = int n
-- ↑-#Ł-e d c (add p₁ p₂) = add p₁ p₂
-- ↑-#Ł-e d c (use p) = use p
-- ↑-#Ł-e d c (new p) = new p
-- ↑-#Ł-e d c (some p) = some p
-- ↑-#Ł-e d c (none τ) = none (↑-#Ł-t′ d 0 τ)
-- -}

-- -- Typing for Expressions
-- data _,_⊢_∶_,_expr {#x #ℓ} : Context #ℓ #x → State #ℓ #x → Expr #x #ℓ
--                            → Type #ℓ → State #ℓ #x → Set where
--   int : ∀ {Γ Δ n} → Γ , Δ ⊢ int n ∶ int , Δ expr
--   add : ∀ {Γ Δ₀ p₁ Δ₁ p₂ Δ₂}
--       → Γ , Δ₀ ⊢ p₁ ∶ int , Δ₁ use
--       → Γ , Δ₁ ⊢ p₂ ∶ int , Δ₂ use
--       → Γ , Δ₀ ⊢ add p₁ p₂ ∶ int , Δ₂ expr
--   use : ∀ {Γ Δᵢ p τ Δₒ}
--       → Γ , Δᵢ ⊢ p ∶ τ , Δₒ use
--       → Γ , Δᵢ ⊢ use p ∶ τ , Δₒ expr
--   new : ∀ {Γ Δᵢ p τ Δₒ}
--       → Γ , Δᵢ ⊢ p ∶ τ , Δₒ use
--       → Γ , Δᵢ ⊢ new p ∶ ~ τ , Δₒ expr
--   some : ∀ {Γ Δᵢ p τ Δₒ}
--        → Γ , Δᵢ ⊢ p ∶ τ , Δₒ use
--        → Γ , Δᵢ ⊢ some p ∶ opt τ , Δₒ expr
--   none : ∀ {Γ Δ τ}
--        -- TODO well-formed check for τ
--        → Γ , Δ ⊢ none τ ∶ opt τ , Δ expr

-- test-rvok-1 : ([ int {0} ]) , [ int (init (bank-def _) tt) ]
--             ⊢ int 1 ∶ int , [ int (init (bank-def _) tt) ] expr
-- test-rvok-1 = int
-- test-rvok-2 : ([ int {0} ,, int ])
--             , [ int (init (bank-def _) tt) ,, int (init (bank-def _) tt) ]
--             ⊢ add (var (fin 0)) (var (fin 1)) ∶ int
--             , [ int (init (bank-def _) tt) ,, int (init (bank-def _) tt) ] expr
-- test-rvok-2 = add (copy var int (can-access (int (init (bank [] free) tt) , (var , int))))
--                   (copy var int (can-access (int (init (bank [] free) tt) , (var , int))))
-- test-rvok-3 : ¬ (([ int {0} ,, int ])
--             , [ int void ,, int (init (bank-def _) tt) ]
--             ⊢ add (var (fin 0)) (var (fin 1))
--             ∶ int
--             , [ int void ,, int (init (bank-def _) tt) ] expr)
-- test-rvok-3 (add (copy p∶τ τPOD (can-access (.(int void) , (var , ())))) p₂)
-- test-rvok-3 (add (move p∶τ () pMove pDeinit) p₂)
-- test-rvok-4 : ([ ~ {0} int ])
--             , [ ~ (init (bank-def _) (int (init (bank-def _) tt))) ]
--             ⊢ use (var fZ)
--             ∶ ~ int
--             , [ ~ void ] expr
-- test-rvok-4 = use (move var
--                         ~Aff
--                         (var , can-access (~ (init (bank [] free) (int (init (bank [] free) tt)))
--                              , (var , ~ int)))
--                         (~ int , (var , var)))
-- test-rvok-5 : ([ int {0} ])
--             , [ int (init (bank-def _) tt) ]
--             ⊢ new (var fZ) ∶ ~ int
--             , [ int (init (bank-def _) tt) ] expr
-- test-rvok-5 = new (copy var int (can-access (int (init (bank [] free) tt) , (var , int))))

-- -- Evalutation for Exprs
-- -- Assigns the result to a provided Route
-- data _∣_,_,_⊢_←_⟶_∣_ {#x #ℓ} : (#aᵢ : ℕ) → Context #ℓ #x → Map #aᵢ #x → Heap #aᵢ
--                               → Route #aᵢ → Expr #x #ℓ
--                               → (#aₒ : ℕ) → Heap #aₒ → Set where
--   int : ∀ {#a T V H αᵣ n H′}
--       → H ⊢ αᵣ ≔ int (val n) ⇒ H′
--       → #a ∣ T , V , H ⊢ αᵣ ← int n ⟶ #a ∣ H′
--   add : ∀ {#a T V H αᵣ p₁ p₂ α₁ α₂ n₁ n₂ H′}
--       → T , V , H ⊢ p₁ ⟶ α₁
--       → T , V , H ⊢ p₂ ⟶ α₂
--       → H ⊢ α₁ ⇒ int (val n₁)
--       → H ⊢ α₂ ⇒ int (val n₂)
--       → H ⊢ αᵣ ≔ int (val (plus n₁ n₂)) ⇒ H′
--       → #a ∣ T , V , H ⊢ αᵣ ← add p₁ p₂ ⟶ #a ∣ H′
--   use : ∀ {#a T V H αᵣ p τ α H′}
--       → T ⊢ p ∶ τ -- TODO unnecessary?
--       → T , V , H ⊢ p ⟶ α
--       → H ⊢ α to αᵣ ⇒ H′
--       → #a ∣ T , V , H ⊢ αᵣ ← use p ⟶ #a ∣ H′
--   new : ∀ {#a T V H αᵣ p τ α H′ H′′ l}
--       → T ⊢ p ∶ τ
--       → layoutof τ l
--       → T , V , H ⊢ p ⟶ α
--       → (l ∷ map (↑-alloc-l 1 0) H) ⊢ ↑-alloc-r 1 0 α to alloc fZ ⇒ H′
--       → H′ ⊢ ↑-alloc-r 1 0 αᵣ ≔ ptr (val (alloc fZ)) ⇒ H′′
--       → #a ∣ T , V , H ⊢ αᵣ ← new p ⟶ S #a ∣ H′′
--   some : ∀ {#a T V H αᵣ p τ α H′ H′′}
--        → T ⊢ p ∶ τ -- TODO unnecessary?
--        → T , V , H ⊢ p ⟶ α
--        → H ⊢ α to < 2 > αᵣ ∙ fin 1 ⇒ H′
--        → H′ ⊢ < 2 > αᵣ ∙ fin 0 ≔ int (val 1) ⇒ H′′
--        → #a ∣ T , V , H ⊢ αᵣ ← some p ⟶ #a ∣ H′′
--   none : ∀ {#a T V H αᵣ τ H′}
--        → H ⊢ < 2 > αᵣ ∙ fin 0 ≔ int (val 0) ⇒ H′
--        → #a ∣ T , V , H ⊢ αᵣ ← none τ ⟶ #a ∣ H′

-- test-rveval-1 : 3 ∣ ([ int {0} ,, int ])
--               , [ fin 2 ,, fin 1 ]
--               , [ int void ,, int (val 1) ,, int (val 2) ]
--               ⊢ alloc (fin 0) ← int 0
--               ⟶ 3 ∣ ([ int (val 0) ,, int (val 1) ,, int (val 2) ])
-- test-rveval-1 = int alloc
-- test-rveval-2 : 3 ∣ ([ int {0} ,, int ])
--               , [ fin 2 ,, fin 1 ]
--               , [ int void ,, int (val 1) ,, int (val 2) ]
--               ⊢ alloc (fin 0) ← add (var (fin 0)) (var (fin 1))
--               ⟶ 3 ∣ ([ int (val 3) ,, int (val 1) ,, int (val 2) ])
-- test-rveval-2 = add var var alloc alloc alloc
-- test-rveval-3 : ¬ (3 ∣ ([ int {0} ,, int ])
--               , [ fin 2 ,, fin 1 ]
--               , [ int void ,, int (val 1) ,, int void ]
--               ⊢ alloc (fin 0) ← add (var (fin 0)) (var (fin 1))
--               ⟶ 3 ∣ ([ int (val 3) ,, int (val 1) ,, int void ]))
-- test-rveval-3 (add var p₂→α₂ () α₂→n₂ αᵣ←n₁+n₂)
-- test-rveval-4 : 2 ∣ ([ int {0} ])
--               , [ fin 1 ]
--               , [ rec ([ int void ,, int void ]) ,, int (val 10) ]
--               ⊢ alloc (fin 0) ← some (var (fin 0))
--               ⟶ 2 ∣ ([ rec ([ int (val 1) ,, int (val 10) ]) ,, int (val 10) ])
-- test-rveval-4 = some var var ((int (val 10)) , (alloc , ∙ alloc alloc)) (∙ alloc alloc)
-- test-rveval-5 : 2 ∣ ([ int {0} ])
--               , [ fin 1 ]
--               , [ rec ([ int void ,, int void ]) ,, int (val 10) ]
--               ⊢ alloc (fin 0) ← none int
--               ⟶ 2 ∣ ([ rec ([ int (val 0) ,, int void ]) ,, int (val 10) ])
-- test-rveval-5 = none (∙ alloc alloc)
-- test-rveval-6 : 3 ∣ ([ ~ {0} int ])
--               , [ fin 0 ]
--               , [ ptr (val (alloc (fin 1))) ,, int (val 1) ,, ptr void ]
--               ⊢ alloc (fin 2) ← use (var fZ)
--               ⟶ 3 ∣ ([ ptr (val (alloc (fin 1))) ,, int (val 1)
--                    ,, ptr (val (alloc (fin 1))) ])
-- test-rveval-6 = use var var (ptr (val (alloc (fS fZ))) , (alloc , alloc))
