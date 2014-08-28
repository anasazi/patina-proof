open import Common
open import Type
open import Path
open import Expr
open import Shape
open import Layout

module Stmt where

data Stmt (#f : ℕ) : (#x #ℓ : ℕ) → Set

infixr 5 _>>_
data Seq (#f #x #ℓ : ℕ) : Set where
  ∅ : Seq #f #x #ℓ
  _>>_ : Stmt #f #x #ℓ → Seq #f #x #ℓ → Seq #f #x #ℓ

data Stmt (#f : ℕ) where
  skip : ∀ {#x #ℓ} → Stmt #f #x #ℓ
  _←_ : ∀ {#x #ℓ} → Path #x → Expr #x #ℓ → Stmt #f #x #ℓ
  free : ∀ {#x #ℓ} → Path #x → Stmt #f #x #ℓ
  push : ∀ {#x #ℓ} → Type #ℓ → Seq #f (S #x) #ℓ → Stmt #f #x #ℓ
  region : ∀ {#x #ℓ} → Seq #f #x (S #ℓ) → Stmt #f #x #ℓ
  call : ∀ {#x #ℓ} → Fin #f → Path #x → Stmt #f #x #ℓ
  match : ∀ {#x #ℓ} → Path #x → Seq #f (S #x) (S #ℓ) → Seq #f #x #ℓ → Stmt #f #x #ℓ

record Func (#f : ℕ) : Set where
  constructor fn
  field
    arg : Type 1
    body : Seq #f 1 1
open Func

↑#x-s : ∀ {#f #x #ℓ} → ℕ → Stmt #f #x #ℓ → Stmt #f (S #x) #ℓ

↑#x-sq : ∀ {#f #x #ℓ} → ℕ → Seq #f #x #ℓ → Seq #f (S #x) #ℓ
↑#x-sq c ∅ = ∅
↑#x-sq c (s >> sq) = ↑#x-s c s >> ↑#x-sq c sq

↑#x-s c skip = skip
↑#x-s c (p ← e) = ↑#x-p c p ← ↑#x-e c e
↑#x-s c (free p) = free (↑#x-p c p)
↑#x-s c (push τ sq) = push τ (↑#x-sq (S c) sq)
↑#x-s c (region sq) = region (↑#x-sq c sq)
↑#x-s c (call f p) = call f (↑#x-p c p)
↑#x-s c (match p sqₛ sqₙ) = match (↑#x-p c p) (↑#x-sq (S c) sqₛ) (↑#x-sq c sqₙ)

↑#ℓ-s : ∀ {#f #x #ℓ} → ℕ → Stmt #f #x #ℓ → Stmt #f #x (S #ℓ)

↑#ℓ-sq : ∀ {#f #x #ℓ} → ℕ → Seq #f #x #ℓ → Seq #f #x (S #ℓ)
↑#ℓ-sq c ∅ = ∅
↑#ℓ-sq c (s >> sq) = ↑#ℓ-s c s >> ↑#ℓ-sq c sq

↑#ℓ-s c skip = skip
↑#ℓ-s c (p ← e) = p ← ↑#ℓ-e c e
↑#ℓ-s c (free p) = free p
↑#ℓ-s c (push τ sq) = push (↑#ℓ-τ c τ) (↑#ℓ-sq c sq)
↑#ℓ-s c (region sq) = region (↑#ℓ-sq (S c) sq)
↑#ℓ-s c (call f p) = call f p
↑#ℓ-s c (match p sqₛ sqₙ) = match p (↑#ℓ-sq (S c) sqₛ) (↑#ℓ-sq c sqₙ)

conv-help : ∀ {#ℓ #x #f} → Type 1 → Path #x → Seq #f 1 1 → Stmt #f #x #ℓ
conv-help {#ℓ} {#x} {#f} τ p sq = region (push τ′ (var fZ ← use (↑#x-p 0 p) >> sq′′) >> ∅)
  where τ′ = ⇑′ Type ↑#ℓ-τ #ℓ 1 τ
        sq′ = ⇑′ (Seq #f 1) ↑#ℓ-sq #ℓ 1 sq
        sq′′ = ⇑′ (λ #x → Seq #f #x (S #ℓ)) ↑#x-sq #x 1 sq′

conv : ∀ {#ℓ #x #f} → Func #f → Path #x → Stmt #f #x #ℓ
conv f p = conv-help (arg f) p (body f)

Funcs : ℕ → Set
Funcs #f = Vec (Func #f) #f

data stok {#f} (F : Funcs #f) : ∀ {#xᵢ #ℓᵢ #xₒ #ℓₒ} → Context #ℓᵢ #xᵢ → State #ℓᵢ #xᵢ
                              → Stmt #f #xᵢ #ℓᵢ → State #ℓₒ #xₒ → Set 

data seqok {#f} (F : Funcs #f) {#x #ℓ}
           (Γ : Context #ℓ #x) (Δ : State #ℓ #x) : Seq #f #x #ℓ → State #ℓ #x → Set where
  ∅ : seqok F Γ Δ ∅ Δ
  _>>_ : ∀ {s sq Δ₁ Δ₂}
       → stok F Γ Δ s Δ₁
       → seqok F Γ Δ₁ sq Δ₂
       → seqok F Γ Δ (s >> sq) Δ₂

data stok {#f} (F : Funcs #f) where
  skip : ∀ {#x #ℓ Δ} {Γ : Context #ℓ #x} → stok F Γ Δ skip Δ
  ←ok : ∀ {#x #ℓ p e τₗ τᵣ Δ₀ Δ₁ Δ₂} {Γ : Context #ℓ #x}
      → Γ , Δ₀ ⊢ e ∶ τᵣ , Δ₁
      → Γ , Δ₁ ⊢ p can-init
      → Γ ⊢ p ∶ τₗ
      → τᵣ <: τₗ
      → Γ , Δ₁ ⊢ p ⇒ Δ₂ init
      → stok F Γ Δ₀ (p ← e) Δ₂
  free : ∀ {#x #ℓ p τ Δ Δ′ δ} {Γ : Context #ℓ #x}
       → Γ ⊢ p ∶ ~ τ
       → Γ , Δ ⊢ * p ⇒ δ shape
       → τ ⊢ δ Dropped
       → Γ , Δ ⊢ p ⇒ Δ′ void
       → stok F Γ Δ (free p) Δ′
  push : ∀ {#x #ℓ τ sq Δ δ} {Γ : Context #ℓ #x} {Δ′ : State #ℓ #x}
       → seqok F (τ ∷ Γ) (void-shape τ ∷ Δ) sq (δ ∷ Δ′)
       → τ ⊢ δ Dropped
       → stok F Γ Δ (push τ sq) Δ′
  region : ∀ {#x #ℓ sq Δ ↓Δ′} {Γ : Context #ℓ #x} {Δ′ : State (S #ℓ) #x}
         → seqok F (map (↑#ℓ-τ 0) Γ) (map (↑#ℓ-δ 0) Δ) sq Δ′
         → All2 (↓#ℓ-δ 0) Δ′ ↓Δ′
         → stok F Γ Δ (region sq) ↓Δ′
  call : ∀ {#x #ℓ f p τ Δ Δ′} {Γ : Context #ℓ #x}
       → Γ , Δ ⊢ p ∶ τ ⇒ Δ′
       → ↑#ℓ-τ 0 τ <: ⇑′ Type ↑#ℓ-τ #ℓ 1 (arg (F ! f))
       → stok F Γ Δ (call f p) Δ′
  match : ∀ {#x #ℓ p τ sₛ sₙ Δ₀ Δ₁ δ Δ₂ ↓Δ₂} {Γ : Context #ℓ #x}
        → Γ , Δ₀ ⊢ p ∶ opt τ ⇒ Δ₁
        → seqok F (map (↑#ℓ-τ 0) (τ ∷ Γ)) (map (↑#ℓ-δ 0) (init-shape τ ∷ Δ₁)) sₛ (δ ∷ Δ₂)
        → ↑#ℓ-τ 0 τ ⊢ δ Dropped
        → seqok F Γ Δ₁ sₙ ↓Δ₂
        → All2 (↓#ℓ-δ 0) Δ₂ ↓Δ₂
        → stok F Γ Δ₀ (match p sₛ sₙ) ↓Δ₂

record fnok {#f} (F : Funcs #f) (f : Func #f) : Set where
  constructor fn
  field
    {δ} : Shape 1
    body-ok : seqok F ([ arg f ]) ([ init-shape (arg f) ]) (body f) ([ δ ])
    cleans : arg f ⊢ δ Dropped

module TestStmt where
  open import Loan

  ok-1 : stok [] ([ int {0} ]) ([ int (just (bank-def _)) ])
              (push (~ int) ∅) ([ int {0} (just (bank-def _)) ])
  ok-1 = push ∅ ~
  ok-2 : ¬ (stok [] ([ int {0} ]) ([ int (just (bank-def _)) ])
                 (push (~ int) (var fZ ← new (var (fin 1)) >> ∅)) ([ int {0} (just (bank-def _)) ]))
  ok-2 (push (←ok (new (copy var _ _)) _ var _ (.(~ int) , (var , var)) >> ∅) ())
  ok-2 (push (←ok (new (move var () _ _ _)) _ _ _ _ >> _) _)
  ok-3 : stok [] ([ int {0} ]) ([ int (just (bank-def _)) ])
              (push (~ int) (var fZ ← new (var (fin 1)) >> free (var fZ) >> ∅))
              ([ int {0} (just (bank-def _)) ])
  ok-3 = push (←ok (new (copy var int (int (just (bank [] free)) , (var , int))))
                   (~ none , (var , ~)) var (~ int) (~ int , (var , var)) >>
               free var (*~ var) int (~ int , (var , var)) >> ∅) ~
  ok-4 : stok [] ([ opt {0} int ,, int ]) ([ opt (just (bank-def _)) ,, int none ])
              (match (var fZ) (var (fin 2) ← use (var fZ) >> ∅) (var (fin 1) ← int 0 >> ∅))
              ([ opt (just (bank-def _)) ,, int {0} (just (bank-def _)) ])
  ok-4 = match (copy var (opt int) (opt (just (bank [] free)) , (var , opt)))
               (←ok (use (copy var int (int (just (bank (free ∷ []) free)) , (var , int))))
                    (int none , (var , int)) var int (int , (var , var)) >> ∅) int
               (←ok int (int none , (var , int)) var int (int , (var , var)) >> ∅)
               (opt (just (refl , Z)) ∷ (int (just (refl , Z)) ∷ []))
  ok-5 : stok ([ fn (~ int) (free (var fZ) >> ∅) ])
              ([ ~ {10} int ]) ([ ~ (just ((bank-def _) , (int (just (bank-def _))))) ])
              (call fZ (var fZ)) ([ ~ {10} none ])
  ok-5 = call (move var ~Aff var (_ , (var , ~ int)) (~ int , (var , var))) (~ int)
  ok-6 : seqok [] ([ int {0} ]) ([ int none ])
               (push int ∅ >> var fZ ← int 1 >> ∅) ([ int {0} (just (bank-def _)) ])
  ok-6 = push ∅ int >> ←ok int (int none , (var , int)) var int (int , (var , var)) >> ∅

{-
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

data Stmt (#f : ℕ) : (#x #ℓ : ℕ) → Set

record Func (#f : ℕ) : Set where
  constructor fn
  field
    {#args} : ℕ
    args : Context 1 #args
    body : Stmt #f #args 1
open Func

Funcs : ℕ → Set
Funcs #f = Vec (Func #f) #f

data Stmt (#f : ℕ) where
  skip : ∀ {#x #ℓ} → Stmt #f #x #ℓ
  _>>_ : ∀ {#x #ℓ} → Stmt #f #x #ℓ → Stmt #f #x #ℓ → Stmt #f #x #ℓ
  _∶_>>_ : ∀ {#x #ℓ} → Type #ℓ → Stmt #f (S #x) #ℓ → Stmt #f #x #ℓ → Stmt #f #x #ℓ
  push : ∀ {#x #ℓ} → Type #ℓ → Stmt #f (S #x) #ℓ → Stmt #f #x #ℓ
  unpush : ∀ {#x #ℓ} → Type #ℓ → Stmt #f (S #x) #ℓ → Stmt #f #x #ℓ
  pop : ∀ {#x #ℓ} → Stmt #f (S #x) #ℓ → Stmt #f (S #x) #ℓ
  region : ∀ {#x #ℓ} → Stmt #f #x (S #ℓ) → Stmt #f #x #ℓ
  unregion : ∀ {#x #ℓ} → Stmt #f #x (S #ℓ) → Stmt #f #x (S #ℓ)
  _←_ : ∀ {#x #ℓ} → Path #x → Expr #x #ℓ → Stmt #f #x #ℓ
  free : ∀ {#x #ℓ} → Path #x → Stmt #f #x #ℓ
  call : ∀ {#x #ℓ n} → Fin #f → Vec (Path #x) n → Stmt #f #x #ℓ
  matchbyval : ∀ {#x #ℓ} → Path #x → Stmt #f (S #x) (S #ℓ) → Stmt #f #x #ℓ → Stmt #f #x #ℓ

↑#x-s : ∀ {#f #x #ℓ} → ℕ → Stmt #f #x #ℓ → Stmt #f (S #x) #ℓ
↑#x-s c skip = skip
↑#x-s c (s₁ >> s₂) = ↑#x-s c s₁ >> ↑#x-s c s₂
↑#x-s c (τ ∶ s₁ >> s₂) = τ ∶ ↑#x-s (S c) s₁ >> ↑#x-s c s₂
↑#x-s c (push τ s) = push τ (↑#x-s (S c) s)
↑#x-s c (unpush τ s) = unpush τ (↑#x-s (S c) s)
↑#x-s c (pop s) = pop (↑#x-s (S c) s)
↑#x-s c (region s) = region (↑#x-s c s)
↑#x-s c (unregion s) = unregion (↑#x-s c s)
↑#x-s c (p ← e) = ↑#x-p c p ← ↑#x-e c e
↑#x-s c (free p) = free (↑#x-p c p)
↑#x-s c (call f ps) = call f (map (↑#x-p c) ps)
↑#x-s c (matchbyval p sₛ sₙ) = matchbyval (↑#x-p c p) (↑#x-s (S c) sₛ) (↑#x-s c sₙ)

↑#ℓ-s : ∀ {#f #x #ℓ} → ℕ → Stmt #f #x #ℓ → Stmt #f #x (S #ℓ)
↑#ℓ-s c skip = skip
↑#ℓ-s c (s₁ >> s₂) = ↑#ℓ-s c s₁ >> ↑#ℓ-s c s₂
↑#ℓ-s c (τ ∶ s₁ >> s₂) = ↑#ℓ-τ c τ ∶ ↑#ℓ-s c s₁ >> ↑#ℓ-s c s₂
↑#ℓ-s c (push τ s) = push (↑#ℓ-τ c τ) (↑#ℓ-s c s)
↑#ℓ-s c (unpush τ s) = unpush (↑#ℓ-τ c τ) (↑#ℓ-s c s)
↑#ℓ-s c (pop s) = pop (↑#ℓ-s c s)
↑#ℓ-s c (region s) = region (↑#ℓ-s (S c) s)
↑#ℓ-s c (unregion s) = unregion (↑#ℓ-s (S c) s)
↑#ℓ-s c (p ← e) = p ← ↑#ℓ-e c e
↑#ℓ-s c (free p) = free p
↑#ℓ-s c (call f ps) = call f ps
↑#ℓ-s c (matchbyval p sₛ sₙ) = matchbyval p (↑#ℓ-s (S c) sₛ) (↑#ℓ-s c sₙ)

data stok {#f} (F : Funcs #f) : ∀ {#xᵢ #ℓᵢ #xₒ #ℓₒ} → Context #ℓᵢ #xᵢ → State #ℓᵢ #xᵢ
                              → Stmt #f #xᵢ #ℓᵢ → State #ℓₒ #xₒ → Set where

--data stok {#f} (F : Funcs #f) where
  skip : ∀ {#x #ℓ Δ} {Γ : Context #ℓ #x} → stok F Γ Δ skip Δ
  _>>_ : ∀ {#x #ℓ s₁ s₂ Δ₀ Δ₁} {Γ : Context #ℓ #x} {Δ₂ : State #ℓ #x}
        → stok F Γ Δ₀ s₁  Δ₁
        → stok F Γ Δ₁ s₂  Δ₂
        → stok F Γ Δ₀ (s₁ >> s₂) Δ₂ 
  _∶_>>_ : ∀ {#x #ℓ τ s₁ s₂ δ} {Γ : Context #ℓ #x} {Δ₀ Δ₁ Δ₂ : State #ℓ #x}
         → τ ⊢ δ Dropped
         → stok F (τ ∷ Γ) (void-shape τ ∷ Δ₀) s₁ (δ ∷ Δ₁)
         → stok F Γ Δ₁ s₂ Δ₂
         → stok F Γ Δ₀ (τ ∶ s₁ >> s₂) Δ₂
  push : ∀ {#x #ℓ τ s Δ δ} {Γ : Context #ℓ #x} {Δ′ : State #ℓ #x}
       → stok F (τ ∷ Γ) (void-shape τ ∷ Δ) s (δ ∷ Δ′)
       → τ ⊢ δ Dropped
       → stok F Γ Δ (push τ s) Δ′
  unpush : ∀ {#x #ℓ τ s δ δ′} {Γ : Context #ℓ #x} {Δ Δ′ : State #ℓ #x}
         → stok F (τ ∷ Γ) (δ ∷ Δ) s (δ′ ∷ Δ′)
         → τ ⊢ δ′ Dropped
         → stok F Γ Δ (unpush τ s) Δ′
  pop : ∀ {#x #ℓ τ s δ δ′ Δ} {Γ : Context #ℓ #x} {Δ′ : State #ℓ #x}
      → stok F (τ ∷ Γ) (δ ∷ Δ) s (δ′ ∷ Δ′)
      → τ ⊢ δ′ Dropped
      → stok F (τ ∷ Γ) (δ ∷ Δ) (pop s) Δ′ 
  region : ∀ {#x #ℓ s Δ ↓Δ′} {Γ : Context #ℓ #x} {Δ′ : State (S #ℓ) #x}
         → stok F (map (↑#ℓ-τ 0) Γ) (map (↑#ℓ-δ 0) Δ) s Δ′
         → All2 (↓#ℓ-δ 0) Δ′ ↓Δ′
         → stok F Γ Δ (region s) ↓Δ′
  unregion : ∀ {#x #ℓ Δ s ↓Δ′} {Γ : Context (S #ℓ) #x} {Δ′ : State (S #ℓ) #x}
           → stok F Γ Δ s Δ′
           → All2 (↓#ℓ-δ 0) Δ′ ↓Δ′
           → stok F Γ Δ (unregion s) ↓Δ′
  ←ok : ∀ {#x #ℓ Δ₀ p e τₗ τᵣ Δ₁ Δ₂} {Γ : Context #ℓ #x}
      → Γ , Δ₀ ⊢ e ∶ τᵣ , Δ₁
      → Γ , Δ₁ ⊢ p can-init
      → Γ ⊢ p ∶ τₗ
      → τᵣ <: τₗ
      → Γ , Δ₁ ⊢ p ⇒ Δ₂ init
      → stok F Γ Δ₀ (p ← e) Δ₂
  free : ∀ {#x #ℓ p τ Δ Δ′ δ} {Γ : Context #ℓ #x}
       → Γ ⊢ p ∶ ~ τ
       → Γ , Δ ⊢ * p ⇒ δ shape
       → τ ⊢ δ Dropped
       → Γ , Δ ⊢ p ⇒ Δ′ void
       → stok F Γ Δ (free p) Δ′
  call : ∀ {#x #ℓ f ps τs Δ Δ′} {Γ : Context #ℓ #x}
       --→ fnok F (F ! f)
       → Γ , Δ ⊢ ps ∶ τs ⇒ Δ′ many
       → All2 (λ τₚ τₐ → τₚ <: τₐ)
              (map (⇑′ Type ↑#ℓ-τ #ℓ 1) (args (F ! f)))
              (map (↑#ℓ-τ 0) τs)
       → stok F Γ Δ (call f ps) Δ′
  matchbyval : ∀ {#x #ℓ p τ sₛ sₙ Δ₀ Δ₁ δ ↓Δ₂} {Γ : Context #ℓ #x} {Δ₂ : State (S #ℓ) #x}
             → Γ , Δ₀ ⊢ p ∶ opt τ ⇒ Δ₁
             → stok F (map (↑#ℓ-τ 0) (τ ∷ Γ)) (map (↑#ℓ-δ 0) (init-shape τ ∷ Δ₁)) sₛ (δ ∷ Δ₂)
             → ↑#ℓ-τ 0 τ ⊢ δ Dropped
             → stok F Γ Δ₁ sₙ ↓Δ₂
             → All2 (↓#ℓ-δ 0) Δ₂ ↓Δ₂
             → stok F Γ Δ₀ (matchbyval p sₛ sₙ) ↓Δ₂

record fnok {#f} (F : Funcs #f) (f : Func #f) : Set where
  constructor fn
  field
    {Δ} : State 1 (#args f)
    body-ok : stok F (rev (args f)) (rev (map init-shape (args f))) (body f) Δ
    cleans : All2 (λ τ δ → τ ⊢ δ Dropped) (rev (args f)) Δ

FuncsOk : ∀ {#f} (F : Funcs #f) → Set
FuncsOk F = All (fnok F) F

conv-help : ∀ {n #f #x #ℓ} → Context #ℓ n → Vec (Path #x) n → Stmt #f (plus n #x) #ℓ → Stmt #f #x #ℓ
conv-help [] [] = id
conv-help {S n} (τ ∷ τs) (p ∷ ps) = conv-help τs ps ∘ (λ s → push τ ((var fZ ← use p′) >> s))
  where p′ = ⇑ Path ↑#x-p (S n) 0 p

conv : ∀ {n #ℓ #f #x} → Context 1 n → Vec (Path #x) n → Stmt #f n 1 → Stmt #f #x #ℓ
conv {n} {#ℓ} {#f} {#x} τs ps s = region (conv-help (rev τs′) (rev ps) s′′)
  where τs′ = map (⇑′ Type ↑#ℓ-τ #ℓ n) τs
        s′ = ⇑′ (Stmt #f n) ↑#ℓ-s #ℓ 1 s
        s′′ = ⇑′ (λ #x → Stmt #f #x (S #ℓ)) ↑#x-s #x n s′

data stev {#f} (F : Funcs #f) : ∀ {#xᵢ #aᵢ #ℓᵢ #xₒ #aₒ #ℓₒ} → Context #ℓᵢ #xᵢ → Mem #xᵢ #aᵢ
                              → Stmt #f #xᵢ #ℓᵢ → Context #ℓₒ #xₒ → Mem #xₒ #aₒ
                              → Stmt #f #xₒ #ℓₒ → Set where
  >>skip : ∀ {#x #a #ℓ s} {Γ : Context #ℓ #x} {M : Mem #x #a}
          → stev F Γ M (skip >> s) Γ M s
  >>⟶ : ∀ {#x #a #ℓ #a′ s₁ s₁′ s₂}
            {Γ : Context #ℓ #x} {M : Mem #x #a} {M′ : Mem #x #a′}
            → stev F Γ M s₁ Γ M′ s₁′
            → stev F Γ M (s₁ >> s₂) Γ M′ (s₁′ >> s₂)
  push : ∀ {#x #a #ℓ τ s St} {Γ : Context #ℓ #x} {H : Heap #x #a}
       → stev F Γ (St , H) (push τ s) (τ ∷ Γ)
              ((void-layout τ ∷ map (↑#x-l 0) St) , map (↑#x-l 0) H) (pop s) 
  unpushskip : ∀ {#x #a #ℓ l τ St ↓St ↓H} {Γ : Context #ℓ #x} {H : Heap (S #x) #a}
             → All2 (↓#x-l 0) St ↓St
             → All2 (↓#x-l 0) H ↓H
             → stev F (τ ∷ Γ) ((l ∷ St) , H) (unpush τ skip) Γ (↓St , ↓H) skip
  unpush⟶ : ∀ {#x #a #ℓ τ s s′} {Γ : Context #ℓ #x} {M : Mem (S #x) #a}
            → stev F {!!} {!!} s {!!} {!!} s′
            → stev F (τ ∷ Γ) M (unpush τ s) {!!} {!!} (unpush τ s′)
  popskip : ∀ {#x #a #ℓ τ l St ↓St ↓H} {Γ : Context #ℓ #x} {H : Heap (S #x) #a}
          → All2 (↓#x-l 0) St ↓St
          → All2 (↓#x-l 0) H ↓H
          → stev F (τ ∷ Γ) ((l ∷ St) , H) (pop skip) Γ (↓St , ↓H) skip 
  pop⟶ : ∀ {#x #x′ #a #a′ #ℓ #ℓ′ s s′}
            {Γ : Context #ℓ (S #x)} {Γ′ : Context #ℓ′ (S #x′)}
            {M : Mem (S #x) #a} {M′ : Mem (S #x′) #a′}
          → stev F Γ M s Γ′ M′ s′
          → stev F Γ M (pop s) Γ′ M′ (pop s′)
  region : ∀ {#x #a #ℓ s} {Γ : Context #ℓ #x} {M : Mem #x #a}
         → stev F Γ M (region s) (map (↑#ℓ-τ 0) Γ) M (unregion s)
  unregionskip : ∀ {#x #a #ℓ ↓Γ} {Γ : Context (S #ℓ) #x} {M : Mem #x #a}
               → All2 (↓#ℓ-τ 0) Γ ↓Γ
               → stev F Γ M (unregion skip) ↓Γ M skip
  unregion⟶ : ∀ {#x #a #ℓ #x′ #ℓ′ #a′ s s′}
                 {Γ : Context (S #ℓ) #x} {M : Mem #x #a}
                 {Γ′ : Context (S #ℓ′) #x′} {M′ : Mem #x′ #a′}
              → stev F Γ M s Γ′ M′ s′
              → stev F Γ M (unregion s) Γ′ M′ (unregion s′)
  ←val : ∀ {#x #a #ℓ p r e l} {Γ : Context #ℓ #x} {M M′ M′′ : Mem #x #a}
       → Γ , M ⊢ e ⟶ inl (l , M′)
       → ⊢ p ⟶ r
       → M′ ⊢ r ≔ l ⇒ M′′
       → stev F Γ M (p ← e) Γ M′′ skip
  ←new : ∀ {#x #a #ℓ p r e lᵥ lₕ St St′ M′} {Γ : Context #ℓ #x} {H H′ : Heap #x #a}
       → Γ , (St , H) ⊢ e ⟶ inr (lᵥ , (lₕ , (St′ , H′)))
       → ⊢ p ⟶ r
       → (map (↑#a-l 0) St′ , (map (↑#a-l 0) (lₕ ∷ H′))) ⊢ r ≔ lᵥ ⇒ M′
       → stev F Γ (St , H) (p ← e) Γ M′ skip
  free : ∀ {#x #a #ℓ p r a St′ H′′ ↓St′ ↓H′′}
           {Γ : Context #ℓ #x} {M : Mem #x (S #a)} {H′ : Heap #x (S #a)}
       → ⊢ p ⟶ r
       → M ⊢ r ⇒ ptr (just (heap a))
       → M ⊢ r ≔ ptr none ⇒ (St′ , H′)
       → remove-elem H′ a H′′
       → All2 (↓#a-l 0) St′ ↓St′
       → All2 (↓#a-l 0) H′′ ↓H′′
       → stev F Γ M (free p) Γ (↓St′ , ↓H′′) skip
  call : ∀ {#x #a #ℓ f} {Γ : Context #ℓ #x} {M : Mem #x #a} {ps : Vec (Path #x) (#args (F ! f))}
       → stev F Γ M (call f ps) Γ M (conv (args (F ! f)) ps (body (F ! f)))
  nonebyval : ∀ {#x #a #ℓ p r l sₛ sₙ} {Γ : Context #ℓ #x} {M : Mem #x #a}
            → ⊢ p ⟶ r
            → M ⊢ r ⇒ rec ([ int (just 0) ,, l ])
            → stev F Γ M (matchbyval p sₛ sₙ) Γ M sₙ
  somebyval : ∀ {#x #a #ℓ p r l τ sₛ sₙ St St′} {Γ : Context #ℓ #x} {H H′ : Heap #x #a}
            → Γ ⊢ p ∶ opt τ
            → ⊢ p ⟶ r
            → (St , H) ⊢ r ∶ opt τ ⇒ rec ([ int (just 1) ,, l ]) , (St′ , H′)
            → stev F Γ (St , H) (matchbyval p sₛ sₙ)
                   (map (↑#ℓ-τ 0) (τ ∷ Γ))
                   (map (↑#x-l 0) (l ∷ St′) , map (↑#x-l 0) H′)
                   (unregion (pop sₛ))
  

  {-
data stok {#x #ℓ} (Γ : Context #ℓ #x) : State #ℓ #x → Stmt #x #ℓ → State #ℓ #x → Set where
  skip : ∀ {Δ} → stok Γ Δ skip Δ
  _seq_ : ∀ {Δ₀ Δ₁ Δ₂ s₁ s₂} → stok Γ Δ₀ s₁ Δ₁ → stok Γ Δ₁ s₂ Δ₂ → stok Γ Δ₀ (s₁ seq s₂) Δ₂
  push : ∀ {Δ τ s δ Δ′}
       → stok (τ ∷ Γ) (void-shape τ ∷ Δ) s (δ ∷ Δ′)
       → τ ⊢ δ Dropped
       → stok Γ Δ (push τ s) Δ′
       {-
  pop : ∀ {Δ τ s δ Δ′ δ′}
      → stok (τ ∷ Γ) (δ ∷ Δ) s (δ′ ∷ Δ′)
      → τ ⊢ δ′ Dropped
      → stok Γ Δ (pop τ s) Δ′
      -}
  ←ok : ∀ {Δ₀ Δ₁ Δ₂ p e τₗ τᵣ}
      → Γ , Δ₀ ⊢ e ∶ τᵣ , Δ₁
      → Γ , Δ₁ ⊢ p can-init
      → Γ ⊢ p ∶ τₗ
      → τᵣ <: τₗ
      → Γ , Δ₁ ⊢ p ⇒ Δ₂ init
      → stok Γ Δ₀ (p ← e) Δ₂

data stev : ∀ {#x₁ #a₁ #ℓ₁} → Context #ℓ₁ #x₁ → Mem #x₁ #a₁ → Stmt #x₁ #ℓ₁
          → ∀ {#x₂ #a₂ #ℓ₂} → Context #ℓ₂ #x₂ → Mem #x₂ #a₂ → Stmt #x₂ #ℓ₂
          → Set where
       {-
  push : ∀ {#ℓ #x #a τ s} {Γ : Context #ℓ #x} {M : Mem #x #a}
       → stev Γ M (push τ s) Γ M (pop τ s)
  popstep : ∀ {#ℓ #x #a τ s s′} {Γ : Context #ℓ #x} {M : Mem #x #a}
          → stev (τ ∷ Γ) (({!!} ∷ (map (↑#x-l 0) (fst M))) , (map (↑#x-l 0) (snd M))) s {!!} {!!} s′
          → stev Γ M (pop τ s) {!!} {!!} (pop τ s′)
          -}
          -}

module TestStmt where
  stok-1 : stok [] ([ int {0} ]) ([ int (just (bank-def _)) ])
                (push (~ int) skip) ([ int (just (bank-def _)) ])
  stok-1 = push skip ~
  stok-2 : stok [] ([ ~ int ,, int {0} ]) ([ ~ none ,, int none ])
                (pop skip) ([ int {0} none ])
  stok-2 = pop skip ~
  stok-3 : ¬ (stok [] {#ℓₒ = 0} ([ ~ {0} int ]) ([ ~ (just ((bank-def _) , int none)) ]) (pop skip) [])
  stok-3 (pop skip ())
  stok-4 : ¬ (stok [] ([ int {0} ]) ([ int (just (bank-def _)) ])
             (push (~ int) (var fZ ← new (var (fin 1)))) ([ int {0} (just (bank-def _)) ]))
  stok-4 (push (←ok (new (copy var int (.(int (just (bank [] free))) , (var , int))))
                               (.(~ none) , (var , ~)) var (~ int) (.(~ int) , (var , var))) ())
  stok-4 (push (←ok (new (move var () _ _ _)) _ _ _ _) _)
  stok-5 : stok [] ([ int {0} ])
                ([ int (just (bank-def _)) ])
                (push (~ int) ((var fZ ← new (var (fin 1))) >> free (var fZ)))
                ([ int {0} (just (bank-def _)) ])
  stok-5 = push (  ←ok (new (copy var int (int (just (bank [] free)) , (var , int))))
                       (~ none , (var , ~)) var (~ int) (~ int , (var , var))
                >> free var (*~ var) int (~ int , (var , var)))
                ~
  stok-6 : stok [] ([ opt {0} int ,, int ])
                ([ opt (just (bank-def _)) ,, int none ])
                (matchbyval (var fZ)
                            (var (fin 2) ← use (var (fin 0)))
                            (var (fin 1) ← int 0))
                ([ opt (just (bank-def _)) ,, int {0} (just (bank-def _)) ])
  stok-6 = matchbyval (copy var (opt int) (opt (just (bank [] free)) , (var , opt)))
                      (←ok (use (copy var int (int (just (bank (free ∷ []) free)) , (var , int))))
                           (int none , (var , int)) var int (int , (var , var)))
                      int
                      (←ok int (int none , (var , int)) var int (int , (var , var)))
                      (opt (just (refl , Z)) ∷ int (just (refl , Z)) ∷ [])
  stok-7 : stok ([ fn ([ int ,, ~ int ]) (free (var fZ)) ])
                ([ int {10} ,, ~ int ])
                ([ int (just (bank-def _)) ,, ~ (just (bank-def _ , int (just (bank-def _)))) ])
                (call fZ ([ var fZ ,, var (fin 1) ]))
                ([ int {10} (just (bank-def _)) ,, ~ none ])
  stok-7 = call --(fn (free var (*~ var) int (~ int , (var , var)))
                --     (~ ∷ int ∷ []))
                ( copy var int (_ , (var , int))
                ∷ move var ~Aff var (_ , (var , ~ int)) (~ int , (var , var))
                ∷ [])
                (int ∷ ~ int ∷ [])
  stok-8 : stok [] ([ int {0} ]) ([ int none ])
                   (push int skip >> (var fZ ← int 1)) ([ int {0} (just (bank-def _)) ])
  stok-8 = (push skip int) >> (←ok int (int none , (var , int)) var int (int , (var , var)))

  stev-1 : stev [] {#ℓᵢ = 0} [] ([] , []) (push (~ int) skip)
                ([ ~ {0} int ]) (([ ptr none ]) , []) (pop skip)
  stev-1 = push
  stev-2 : stev [] {#ℓₒ = 0} ([ ~ {0} int ]) (([ ptr none ]) , []) (pop skip) [] ([] , []) skip
  stev-2 = popskip [] []
  stev-3 : stev [] {#ℓₒ = 0} ([ ~ {0} int ])
           (([ ptr (just (heap fZ)) ]) , ([ int (just 1) ]))
           (pop skip) [] ([] , ([ int (just 1) ])) skip
  stev-3 = popskip [] (int ∷ [])
  stev-4 : stev [] ([ int {0} ]) (([ int none ]) , []) (var fZ ← int 0)
                ([ int {0} ]) (([ int (just 0) ]) , []) skip
  stev-4 = ←val int var stack
  stev-5 : stev [] ([ ~ {0} int ,, int ])
                  (([ ptr none ,, int (just 0) ])
                , ([ ptr (just (heap fZ)) ]))
                (var fZ ← new (var (fin 1)))
                ([ ~ {0} int ,, int ])
                 (([ ptr (just (heap fZ)) ,, int (just 0) ])
                , ([ int (just 0) ,, ptr (just (heap (fin 1))) ]))
                skip
  stev-5 = ←new (new var var (copy int stack)) var stack
  stev-6 : stev [] ([ int {0} ])
                ( ([ int (just 1) ])
                , [])
                (push (~ int) ((var fZ ← new (var (fin 1))) >> free (var fZ)))
                ([ ~ {0} int ,, int ])
                ( ([ ptr none ,, int (just 1) ])
                , [])
                (pop ((var fZ ← new (var (fin 1))) >> free (var fZ)))
  stev-6 = push
  stev-7 : stev [] ([ ~ {0} int ,, int ])
                ( ([ ptr none ,, int (just 1) ])
                , [])
                (pop ((var fZ ← new (var (fin 1))) >> free (var fZ)))
                ([ ~ {0} int ,, int ])
                ( ([ ptr (just (heap fZ)) ,, int (just 1) ])
                , ([ int (just 1) ]))
                (pop (skip >> free (var fZ)))
  stev-7 = pop⟶ (>>⟶ (←new (new var var (copy int stack)) var stack))
  stev-8 : stev [] ([ ~ {0} int ,, int ])
                ( ([ ptr (just (heap fZ)) ,, int (just 1) ])
                , ([ int (just 1) ]))
                (pop (skip >> free (var fZ)))
                ([ ~ {0} int ,, int ])
                ( ([ ptr (just (heap fZ)) ,, int (just 1) ])
                , ([ int (just 1) ]))
                (pop (free (var fZ)))
  stev-8 = pop⟶ >>skip
  stev-9 : stev [] ([ ~ {0} int ,, int ])
                ( ([ ptr (just (heap fZ)) ,, int (just 1) ])
                , ([ int (just 1) ]))
                (pop (free (var fZ)))
                ([ ~ {0} int ,, int ])
                ( ([ ptr none ,, int (just 1) ])
                , [])
                (pop skip)
  stev-9 = pop⟶ (free var stack stack re-Z (ptr none ∷ int ∷ []) [])
  stev-10 : stev [] ([ ~ {0} int ,, int ])
                 ( ([ ptr none ,, int (just 1) ])
                 , [])
                 (pop skip)
                 ([ int {0} ])
                 (([ int (just 1) ]) , [])
                 skip
  stev-10 = popskip (int ∷ []) []
  stev-11 : stev [] ([ opt {0} int ,, int ])
                 (([ rec ([ int (just 0) ,, int none ]) ,, int none ]) , [])
                 (matchbyval (var fZ) (var (fin 2) ← use (var fZ)) (var (fin 1) ← int 0))
                 ([ opt {0} int ,, int ])
                 (([ rec ([ int (just 0) ,, int none ]) ,, int none ]) , [])
                 (var (fin 1) ← int 0)
  stev-11 = nonebyval var stack
  stev-12 : stev [] ([ opt {0} int ,, int ])
                 (([ rec ([ int (just 0) ,, int none ]) ,, int none ]) , [])
                 (var (fin 1) ← int 0)
                 ([ opt {0} int ,, int ])
                 (([ rec ([ int (just 0) ,, int none ]) ,, int (just 0) ]) , [])
                 skip
  stev-12 = ←val int var stack
  stev-13 : stev [] ([ opt {0} int ,, int ])
                 (([ rec ([ int (just 1) ,, int (just 10) ]) ,, int none ]) , [])
                 (matchbyval (var fZ) (var (fin 2) ← use (var fZ)) (var (fin 1) ← int 0))
                 ([ int {1} ,, opt int ,, int ])
                 (([ int (just 10) ,, rec ([ int (just 1) ,, int (just 10) ]) ,, int none ]) , [])
                 (unregion (pop (var (fin 2) ← use (var fZ))))
  stev-13 = somebyval var var (copy (opt int) stack)
  stev-14 : stev [] ([ int {1} ,, opt int ,, int ])
                 (([ int (just 10) ,, rec ([ int (just 1) ,, int (just 10) ]) ,, int none ]) , [])
                 (unregion (pop (var (fin 2) ← use (var fZ))))
                 ([ int {1} ,, opt int ,, int ])
                 (([ int (just 10) ,, rec ([ int (just 1) ,, int (just 10) ]) ,, int (just 10) ]) , [])
                 (unregion (pop skip))
  stev-14 = unregion⟶ (pop⟶ (←val (use var var (copy int stack)) var stack))
  stev-15 : stev [] ([ int {1} ,, opt int ,, int ])
                 (([ int (just 10) ,, rec ([ int (just 1) ,, int (just 10) ]) ,, int (just 10) ]) , [])
                 (unregion (pop skip))
                 ([ opt {1} int ,, int ])
                 (([ rec ([ int (just 1) ,, int (just 10) ]) ,, int (just 10) ]) , [])
                 (unregion skip)
  stev-15 = unregion⟶ (popskip (rec (int ∷ int ∷ []) ∷ int ∷ []) [])
  stev-16 : stev [] ([ opt {1} int ,, int ])
                 (([ rec ([ int (just 1) ,, int (just 10) ]) ,, int (just 10) ]) , [])
                 (unregion skip)
                 ([ opt {0} int ,, int ])
                 (([ rec ([ int (just 1) ,, int (just 10) ]) ,, int (just 10) ]) , [])
                 skip
  stev-16 = unregionskip (opt int ∷ int ∷ [])
  stev-17 : stev ([ fn ([ int ,, ~ int ]) (free (var fZ)) ])
                 ([ int {10} ,, ~ int ])
                 (([ int (just 0) ,, ptr (just (heap fZ)) ]) , ([ int (just 1) ]))
                 (call fZ ([ var fZ ,, var (fin 1) ]))
                 ([ int {10} ,, ~ int ])
                 (([ int (just 0) ,, ptr (just (heap fZ)) ]) , ([ int (just 1) ]))
                 (region (push int ((var fZ ← use (var (fin 1))) >>
                         (push (~ int) ((var fZ ← use (var (fin 3))) >>
                         free (var fZ))))))
  stev-17 = call
  stev-18 : stev ([ fn ([ int ,, ~ int ]) (free (var fZ)) ])
                 ([ int {10} ,, ~ int ])
                 (([ int (just 0) ,, ptr (just (heap fZ)) ]) , ([ int (just 1) ]))
                 (region (push int ((var fZ ← use (var (fin 1))) >>
                         (push (~ int) ((var fZ ← use (var (fin 3))) >>
                         free (var fZ))))))
                 ([ int {11} ,, ~ int ])
                 (([ int (just 0) ,, ptr (just (heap fZ)) ]) , ([ int (just 1) ]))
                 (unregion (push int ((var fZ ← use (var (fin 1))) >>
                            push (~ int) ((var fZ ← use (var (fin 3))) >>
                            free (var fZ)))))
  stev-18 = region
  stev-19 : stev ([ fn ([ int ,, ~ int ]) (free (var fZ)) ])
                 ([ int {11} ,, ~ int ])
                 (([ int (just 0) ,, ptr (just (heap fZ)) ]) , ([ int (just 1) ]))
                 (unregion (push int ((var fZ ← use (var (fin 1))) >>
                            push (~ int) ((var fZ ← use (var (fin 3))) >>
                            free (var fZ)))))
                 ([ int ,, int {11} ,, ~ int ])
                 (([ int none ,, int (just 0) ,, ptr (just (heap fZ)) ]) , ([ int (just 1) ]))
                 (unregion (pop ((var fZ ← use (var (fin 1))) >>
                            push (~ int) ((var fZ ← use (var (fin 3))) >>
                            free (var fZ)))))
  stev-19 = unregion⟶ push
  stev-20 : stev ([ fn ([ int ,, ~ int ]) (free (var fZ)) ])
                 ([ int ,, int {11} ,, ~ int ])
                 (([ int none ,, int (just 0) ,, ptr (just (heap fZ)) ]) , ([ int (just 1) ]))
                 (unregion (pop ((var fZ ← use (var (fin 1))) >>
                            push (~ int) ((var fZ ← use (var (fin 3))) >>
                            free (var fZ)))))
                 ([ int ,, int {11} ,, ~ int ])
                 (([ int (just 0) ,, int (just 0) ,, ptr (just (heap fZ)) ]) , ([ int (just 1) ]))
                 (unregion (pop (skip >>
                            push (~ int) ((var fZ ← use (var (fin 3))) >>
                            free (var fZ)))))
  stev-20 = unregion⟶ (pop⟶ (>>⟶ (←val (use var var (copy int stack)) var stack)))
  stev-21 : stev ([ fn ([ int ,, ~ int ]) (free (var fZ)) ])
                 ([ int ,, int {11} ,, ~ int ])
                 (([ int (just 0) ,, int (just 0) ,, ptr (just (heap fZ)) ]) , ([ int (just 1) ]))
                 (unregion (pop (skip >>
                            push (~ int) ((var fZ ← use (var (fin 3))) >>
                            free (var fZ)))))
                 ([ int ,, int {11} ,, ~ int ])
                 (([ int (just 0) ,, int (just 0) ,, ptr (just (heap fZ)) ]) , ([ int (just 1) ]))
                 (unregion (pop (push (~ int) ((var fZ ← use (var (fin 3))) >>
                                 free (var fZ)))))
  stev-21 = unregion⟶ (pop⟶ >>skip)
  stev-22 : stev ([ fn ([ int ,, ~ int ]) (free (var fZ)) ])
                 ([ int ,, int {11} ,, ~ int ])
                 (([ int (just 0) ,, int (just 0) ,, ptr (just (heap fZ)) ]) , ([ int (just 1) ]))
                 (unregion (pop (push (~ int) ((var fZ ← use (var (fin 3))) >>
                                 free (var fZ)))))
                 ([ ~ int ,, int ,, int {11} ,, ~ int ])
                 (([ ptr none ,, int (just 0) ,, int (just 0) ,, ptr (just (heap fZ)) ]) , ([ int (just 1) ]))
                 (unregion (pop (pop ((var fZ ← use (var (fin 3))) >>
                                 free (var fZ)))))
  stev-22 = unregion⟶ (pop⟶ push)
  stev-23 : stev ([ fn ([ int ,, ~ int ]) (free (var fZ)) ])
                 ([ ~ int ,, int ,, int {11} ,, ~ int ])
                 (([ ptr none ,, int (just 0) ,, int (just 0) ,, ptr (just (heap fZ)) ]) , ([ int (just 1) ]))
                 (unregion (pop (pop ((var fZ ← use (var (fin 3))) >>
                                 free (var fZ)))))
                 ([ ~ int ,, int ,, int {11} ,, ~ int ])
                 (([ ptr (just (heap fZ)) ,, int (just 0) ,, int (just 0) ,, ptr none ]) , ([ int (just 1) ]))
                 (unregion (pop (pop (skip >> free (var fZ)))))
  stev-23 = unregion⟶ (pop⟶ (pop⟶ (>>⟶ (←val (use var var (move ~Aff stack stack)) var stack))))
  stev-24 : stev ([ fn ([ int ,, ~ int ]) (free (var fZ)) ])
                 ([ ~ int ,, int ,, int {11} ,, ~ int ])
                 (([ ptr (just (heap fZ)) ,, int (just 0) ,, int (just 0) ,, ptr none ]) , ([ int (just 1) ]))
                 (unregion (pop (pop (skip >> free (var fZ)))))
                 ([ ~ int ,, int ,, int {11} ,, ~ int ])
                 (([ ptr (just (heap fZ)) ,, int (just 0) ,, int (just 0) ,, ptr none ]) , ([ int (just 1) ]))
                 (unregion (pop (pop (free (var fZ)))))
  stev-24 = unregion⟶ (pop⟶ (pop⟶ >>skip))
  stev-25 : stev ([ fn ([ int ,, ~ int ]) (free (var fZ)) ])
                 ([ ~ int ,, int ,, int {11} ,, ~ int ])
                 (([ ptr (just (heap fZ)) ,, int (just 0) ,, int (just 0) ,, ptr none ]) , ([ int (just 1) ]))
                 (unregion (pop (pop (free (var fZ)))))
                 ([ ~ int ,, int ,, int {11} ,, ~ int ])
                 (([ ptr none ,, int (just 0) ,, int (just 0) ,, ptr none ]) , [])
                 (unregion (pop (pop skip)))
  stev-25 = unregion⟶ (pop⟶ (pop⟶ (free var stack stack re-Z (ptr none ∷ int ∷ int ∷ ptr none ∷ []) [])))
  stev-26 : stev ([ fn ([ int ,, ~ int ]) (free (var fZ)) ])
                 ([ ~ int ,, int ,, int {11} ,, ~ int ])
                 (([ ptr none ,, int (just 0) ,, int (just 0) ,, ptr none ]) , [])
                 (unregion (pop (pop skip)))
                 ([ int ,, int {11} ,, ~ int ])
                 (([ int (just 0) ,, int (just 0) ,, ptr none ]) , [])
                 (unregion (pop skip))
  stev-26 = unregion⟶ (pop⟶ (popskip (int ∷ int ∷ ptr none ∷ []) []))
  stev-27 : stev ([ fn ([ int ,, ~ int ]) (free (var fZ)) ])
                 ([ int ,, int {11} ,, ~ int ])
                 (([ int (just 0) ,, int (just 0) ,, ptr none ]) , [])
                 (unregion (pop skip))
                 ([ int {11} ,, ~ int ])
                 (([ int (just 0) ,, ptr none ]) , [])
                 (unregion skip)
  stev-27 = unregion⟶ (popskip (int ∷ ptr none ∷ []) [])
  stev-28 : stev ([ fn ([ int ,, ~ int ]) (free (var fZ)) ])
                 ([ int {11} ,, ~ int ])
                 (([ int (just 0) ,, ptr none ]) , [])
                 (unregion skip)
                 ([ int {10} ,, ~ int ])
                 (([ int (just 0) ,, ptr none ]) , [])
                 skip
  stev-28 = unregionskip (int ∷ ~ int ∷ [])
  stev-29 : stev []
                 ([ int {0} ])
                 (([ int none ]) , [])
                 (push int skip >> (var fZ ← int 1))
                 ([ int {0} ,, int ])
                 (([ int none ,, int none ]) , [])
                 (pop skip >> (var fZ ← int 1))
  stev-29 = {!>>⟶!}
  -}
{-
  stok-3 : stok ([ int {0} ]) ([ int none ]) (var fZ ← int 0) ([ int (just (bank-def _)) ])
  stok-3 = ←ok int (int none , (var , int)) var int (int , (var , var))
  stok-4 : ∀ Δ → ¬ (stok ([ int {0} ]) ([ int (just (bank-def _)) ]) (var fZ ← int 0) Δ)
  stok-4 Δ (←ok int (.(int (just (bank [] free))) , (var , ())) p∶τₗ τᵣ<:τₗ init)
  stok-5 : ¬ (stok ([ int {0} ]) ([ int (just (bank-def _)) ])
             (pop (~ int) (var fZ ← new (var (fin 1)))) ([ int (just (bank-def _)) ]))
  stok-5 (pop (←ok (new (copy var int (._ , (var , int))))
                   (δ , (var , snd)) var (~ int) (._ , (var , var))) ())
  stok-5 (pop (←ok (new (move var () _ _ _)) _ _ _ _) _)
  -}
  {-
  stev-1 : stev [] [] ([] , []) (push (int {0}) skip)
                ([ int {0} ]) (([ int none ]) , []) (skip seq pop)
  stev-1 = push
  stev-2 : stev [] ([ int {0} ]) (([ int none ]) , []) (skip seq pop)
                ([ int {0} ]) (([ int none ]) , []) pop
  stev-2 = skipseq
  stev-3 : stev [] ([ int {0} ]) (([ int none ]) , []) pop {_} {_} {0} [] ([] , []) skip
  stev-3 = pop [] []
  -}

{-
data Stmt (#f : ℕ) : (#x #ℓ : ℕ) → Set

record Func (#f : ℕ) : Set where
  constructor fn
  field
    {#args} : ℕ
    args : Vec (Type 1) #args
    body : Stmt #f #args 1
open Func

Funcs : ℕ → Set
Funcs #f = Vec (Func #f) #f

data Stmt (#f : ℕ) where
  skip : ∀ {#x #ℓ} → Stmt #f #x #ℓ
  _seq_ : ∀ {#x #ℓ} → Stmt #f #x #ℓ → Stmt #f #x #ℓ → Stmt #f #x #ℓ
  push : ∀ {#x #ℓ} → Type #ℓ → Stmt #f (S #x) #ℓ → Stmt #f #x #ℓ
  pop : ∀ {#x #ℓ} → Stmt #f (S #x) #ℓ
  --pop : ∀ {#x #ℓ} → Stmt #f (S #x) #ℓ → Stmt #f (S #x) #ℓ
  {-
  region : ∀ {#x #ℓ} → Stmt #f #x (S #ℓ) → Stmt #f #x #ℓ
  unregion : ∀ {#x #ℓ} → Stmt #f #x (S #ℓ) → Stmt #f #x (S #ℓ)
  _←_ : ∀ {#x #ℓ} → Path #x → Expr #x #ℓ → Stmt #f #x #ℓ
  free : ∀ {#x #ℓ} → Path #x → Stmt #f #x #ℓ
  call : ∀ {#x #ℓ n} → Fin #f → Vec (Path #x) n → Stmt #f #x #ℓ
  match : ∀ {#x #ℓ} → Path #x → Stmt #f (S #x) (S #ℓ) → Stmt #f #x #ℓ → Stmt #f #x #ℓ
  -}

data foo {#f} (F : Funcs #f) : ∀ {#ℓ #x} → Context #ℓ #x → State #ℓ #x
                             → Stmt #f #x #ℓ → ∀ {#ℓ′ #x′} → State #ℓ′ #x′ → Set where
  skip : ∀ {#x #ℓ Δ} {Γ : Context #ℓ #x} → foo F Γ Δ skip Δ
  _seq_ : ∀ {#x #ℓ s₁ s₂ Δ₀ Δ₁ Δ₂} {Γ : Context #ℓ #x}
        → foo F Γ Δ₀ s₁ Δ₁
        → foo F Γ Δ₁ s₂ Δ₂
        → foo F Γ Δ₀ (s₁ seq s₂) Δ₂

data stok {#f} (F : Funcs #f) : ∀ {#ℓ #x} → Context #ℓ #x → State #ℓ #x
                              → Stmt #f #x #ℓ → State #ℓ #x → Set
                             
data stok {#f} (F : Funcs #f) where
  skip : ∀ {#x #ℓ Δ} {Γ : Context #ℓ #x} → stok F Γ Δ skip Δ
  _seq_ : ∀ {#x #ℓ s₁ s₂ Δ₀ Δ₁ Δ₂} {Γ : Context #ℓ #x}
        → stok F Γ Δ₀ s₁ Δ₁
        → stok F Γ Δ₁ s₂ Δ₂
        → stok F Γ Δ₀ (s₁ seq s₂) Δ₂
  push : ∀ {#x #ℓ Δ Δ′ δ τ s} {Γ : Context #ℓ #x}
       → stok F (τ ∷ Γ) (void-shape τ ∷ Δ) s (δ ∷ Δ′)
       → τ ⊢ δ Dropped
       → stok F Γ Δ (push τ s) Δ′
  pop : ∀ {#x #ℓ τ δ Δ} {Γ : Context #ℓ #x}
      → τ ⊢ δ Dropped
      → stok F (τ ∷ Γ) (δ ∷ Δ) pop (δ ∷ Δ)
       {-
  pop : ∀ {#x #ℓ Δ Δ′ s} {Γ : Context #ℓ (S #x)}
      → stok F Γ Δ s Δ′
      → stok F Γ Δ (pop s) Δ′
      -}

data stev {#f} (F : Funcs #f) : ∀ {#x #a #ℓ} → Context #ℓ #x → Mem #x #a → Stmt #f #x #ℓ
                              → ∀ {#x′ #a′ #ℓ′} → Context #ℓ′ #x′ → Mem #x′ #a′ → Stmt #f #x′ #ℓ′
                              → Set where
  skipseq : ∀ {#x #a #ℓ s} {Γ : Context #ℓ #x} {M : Mem #x #a} → stev F Γ M (skip seq s) Γ M s
  stepseq : ∀ {#x #a #a′ #ℓ s₁ s₁′ s₂} {Γ : Context #ℓ #x} {M : Mem #x #a} {M′ : Mem #x #a′}
          → stev F Γ M s₁ Γ M′ s₁′
          → stev F Γ M (s₁ seq s₂) Γ M′ (s₁′ seq s₂)
  push : ∀ {#x #a #ℓ τ s St H} {Γ : Context #ℓ #x}
       → stev F {_} {#a} Γ (St , H) (push τ s)
              (τ ∷ Γ)
              ((void-layout τ ∷ map (↑#x-l 0) St) , map (↑#x-l 0) H)
              (s seq pop) 
  pop : ∀ {#x #a #ℓ τ Γ l St H ↓St ↓H}
      → All2 (↓#x-l 0) St ↓St
      → All2 (↓#x-l 0) H ↓H
      → stev F {S #x} {#a} {#ℓ} (τ ∷ Γ) ((l ∷ St) , H) pop Γ (↓St , ↓H) skip

module TestStmt where
          {-
  stok-1 : stok [] {0} [] [] (push int skip) []
  stok-1 = push skip int
  stok-2 : stok [] {0} ([ ~ int ]) ([ ~ none ]) (pop skip) ([ ~ none ])
  stok-2 = pop skip
  -}
  stev-1 : stev [] [] ([] , []) (push (int {0}) skip)
                ([ int {0} ]) (([ int none ]) , []) (skip seq pop)
  stev-1 = push
  stev-2 : stev [] ([ int {0} ]) (([ int none ]) , []) (skip seq pop)
                ([ int {0} ]) (([ int none ]) , []) pop
  stev-2 = skipseq
  stev-3 : stev [] ([ int {0} ]) (([ int none ]) , []) pop {_} {_} {0} [] ([] , []) skip
  stev-3 = pop [] []
  -}

-- module Stmt where

-- {-
-- Statements are indexed by:
-- - number of functions
-- - number of free variables
-- - the lifetime relation
-- -}
-- data Stmt : (#f #x #ℓ : ℕ) → Set

-- -- Functions are indexed by the number of functions (allows recursive calls)
-- -- TODO handle lifetime variables
-- record Func (#f : ℕ) : Set where
--   constructor fn
--   field
--     {#args} : ℕ -- implicit number of arguments
--     -- The arguments do not have the surrounding lifetime relation in scope
--     args : Vec (Type 1) #args
--     -- The body has the arguments in scope
--     body : Stmt #f #args 1
-- open Func

-- data Stmt where
--   -- Do nothing
--   skip : ∀ {#f #x #ℓ} → Stmt #f #x #ℓ
--   -- Sequence two statements with the *same* indicies
--   _seq_ : ∀ {#f #x #ℓ} → Stmt #f #x #ℓ → Stmt #f #x #ℓ → Stmt #f #x #ℓ
--   -- Create a new variable of the provided type and a Stmt where it is in scope
--   push : ∀ {#f #x #ℓ} → Type #ℓ → Stmt #f (S #x) #ℓ → Stmt #f #x #ℓ
--   -- Pop a stack variable once the wrapped statement finishes
--   pop : ∀ {#f #x #ℓ} → Stmt #f (S #x) #ℓ → Stmt #f (S #x) #ℓ
--   -- Create a new concrete lifetime value and a Stmt where it is in scope
--   region : ∀ {#f #x #ℓ} → Stmt #f #x (S #ℓ) → Stmt #f #x #ℓ
--   -- Pop a concrete lifetime value once the wrapped statement finishes
--   unregion : ∀ {#f #x #ℓ} → Stmt #f #x (S #ℓ) → Stmt #f #x (S #ℓ)
--   -- Assignment
--   _⇐_ : ∀ {#f #x #ℓ} → Path #x → Expr #x #ℓ → Stmt #f #x #ℓ
--   -- Free heap memory
--   free : ∀ {#f #x #ℓ} → Path #x → Stmt #f #x #ℓ
--   -- Call a function
--   call : ∀ {#f #x #ℓ n} → Fin #f → Vec (Path #x) n → Stmt #f #x #ℓ
--   -- Match by value (the Some block has an extra variable and lifetime in scope)
--   matchbyval : ∀ {#f #x #ℓ} → Path #x → Stmt #f (S #x) (S #ℓ) → Stmt #f #x #ℓ → Stmt #f #x #ℓ

-- -- Upshifting for the #x and #ℓ indicies of Stmt
-- ↑-var-s : ∀ {#f #x #ℓ} → (d : ℕ) → ℕ → Stmt #f #x #ℓ → Stmt #f (plus #x d) #ℓ
-- ↑-var-s d c skip = skip
-- ↑-var-s d c (s₁ seq s₂) = ↑-var-s d c s₁ seq ↑-var-s d c s₂
-- ↑-var-s d c (push τ s) = push τ (↑-var-s d (S c) s)
-- ↑-var-s d c (pop s) = pop (↑-var-s d c s)
-- ↑-var-s d c (region s) = region (↑-var-s d c s)
-- ↑-var-s d c (unregion s) = unregion (↑-var-s d c s)
-- ↑-var-s d c (p ⇐ e) = ↑-var-p′′ d c p ⇐ ↑-var-e′ d c e
-- ↑-var-s d c (free p) = free (↑-var-p′′ d c p)
-- ↑-var-s d c (call f ps) = call f (map (↑-var-p′′ d c) ps)
-- ↑-var-s d c (matchbyval p sₛ sₙ) = matchbyval (↑-var-p′′ d c p)
--                                               (↑-var-s d (S c) sₛ)
--                                               (↑-var-s d c sₙ)

-- ↑-var-s′ : ∀ {#x #f #ℓ} → (d : ℕ) → ℕ → Stmt #f #x #ℓ → Stmt #f (plus d #x) #ℓ
-- ↑-var-s′ {#x} d c s rewrite plus-comm d #x = ↑-var-s d c s

-- ↑-#ℓ-s : ∀ {#f #x #ℓ} → (d : ℕ) → ℕ → Stmt #f #x #ℓ → Stmt #f #x (plus #ℓ d)
-- ↑-#ℓ-s d c skip = skip
-- ↑-#ℓ-s d c (s₁ seq s₂) = ↑-#ℓ-s d c s₁ seq ↑-#ℓ-s d c s₂
-- ↑-#ℓ-s d c (push τ s) = push (↑-#ℓ-t′ d c τ) (↑-#ℓ-s d c s)
-- ↑-#ℓ-s d c (pop s) = pop (↑-#ℓ-s d c s)
-- ↑-#ℓ-s d c (region s) = region (↑-#ℓ-s d (S c) s)
-- ↑-#ℓ-s d c (unregion s) = unregion (↑-#ℓ-s d c s)
-- ↑-#ℓ-s d c (p ⇐ e) = p ⇐ ↑-#ℓ-e d c e
-- ↑-#ℓ-s d c (free p) = free p
-- ↑-#ℓ-s d c (call f ps) = call f ps
-- ↑-#ℓ-s d c (matchbyval p sₛ sₙ) = matchbyval p (↑-#ℓ-s d (S c) sₛ) (↑-#ℓ-s d c sₙ)

-- ↑-#ℓ-s′ : ∀ {#f #x #ℓ} → (d : ℕ) → ℕ → Stmt #f #x #ℓ → Stmt #f #x (plus d #ℓ)
-- ↑-#ℓ-s′ {_} {_} {#ℓ} d c s rewrite plus-comm d #ℓ = ↑-#ℓ-s d c s

-- {-
-- ↑-#Ł-s : ∀ {#f #x #ℓ #Ł} → (d : ℕ) → ℕ → Stmt #f #x #ℓ #Ł → Stmt #f #x #ℓ (plus #Ł d)
-- ↑-#Ł-s d c skip = skip
-- ↑-#Ł-s d c (s₁ seq s₂) = ↑-#Ł-s d c s₁ seq ↑-#Ł-s d c s₂
-- ↑-#Ł-s d c (s₁ pop s₂) = ↑-#Ł-s d c s₁ pop ↑-#Ł-s d c s₂
-- ↑-#Ł-s d c (s₁ endregion s₂) = ↑-#Ł-s d c s₁ endregion ↑-#Ł-s d c s₂
-- ↑-#Ł-s d c (push τ s) = push (↑-#Ł-t′ d c τ) (↑-#Ł-s d c s)
-- ↑-#Ł-s d c (region s) = region (↑-#Ł-s d c s)
-- ↑-#Ł-s d c (p ⇐ e) = p ⇐ ↑-#Ł-e d c e
-- ↑-#Ł-s d c (free p) = free p
-- ↑-#Ł-s d c (call f ps) = call f ps
-- ↑-#Ł-s d c (matchbyval p sₛ sₙ) = matchbyval p (↑-#Ł-s d c sₛ) (↑-#Ł-s d c sₙ)

-- ↑-#Ł-s′ : ∀ {#f #x #ℓ #Ł} → (d : ℕ) → ℕ → Stmt #f #x #ℓ #Ł → Stmt #f #x #ℓ (plus d #Ł)
-- ↑-#Ł-s′ {_} {_} {_} {#Ł} d c s rewrite plus-comm d #Ł = ↑-#Ł-s d c s
-- -}

-- {-
-- Converting a function body into a statement
-- Basically, we wrap the body in push statements for the arguments and then one region statement for the block lifetime
-- -}
-- conv-helper : ∀ {n #x #f #ℓ} → Vec (Type #ℓ) n → Vec (Path #x) n → Stmt #f (plus n #x) #ℓ → Stmt #f #x #ℓ
-- conv-helper [] [] s = s
-- conv-helper {S n} (τ ∷ τs) (p ∷ ps) s = conv-helper τs ps (push τ ((var fZ ⇐ use (↑-var-p′′′ (S n) 0 p)) seq s))

-- test-conv-helper-1 : conv-helper {_} {_} {0} ([ int {0} ]) ([ var {10} (fin 5) ]) skip
--             ≡ push int ((var fZ ⇐ use (var (fin 6))) seq skip)
-- test-conv-helper-1 = refl
-- test-conv-helper-2 : conv-helper {_} {_} {0} ([ int {0} ,, ~ int ]) ([ var {10} (fin 5) ,, var (fin 3) ]) (free (var (fin 1)))
--             ≡ push (~ int) ((var fZ ⇐ use (var (fin 4))) seq push int ((var fZ ⇐ use (var (fin 7))) seq free (var (fin 1))))
-- test-conv-helper-2 = refl

-- -- TODO fix lifetime parameters
-- conv : ∀ {n #x #f} #ℓ → Vec (Type 1) n → Vec (Path #x) n → Stmt #f n 1 → Stmt #f #x #ℓ
-- conv {n} {#x} {_} #ℓ τs ps s = region (conv-helper (rev (map (↑-#ℓ-t′ #ℓ 1) τs)) (rev ps) (↑-#ℓ-s #ℓ 1 (↑-var-s #x n s)))
-- --conv : ∀ {n #x #f} #ℓ #Ł → Vec (Type 1 0) n → Vec (Path #x) n → Stmt #f n 1 0 → Stmt #f #x #ℓ #Ł
-- --conv {n} {#x} {_} #ℓ #Ł τs ps s = region (conv-helper (rev (map (↑-#ℓ-t′ #ℓ 1 ∘ ↑-#Ł-t′ #Ł 0) τs)) (rev ps) (↑-#Ł-s #Ł 0 (↑-#ℓ-s #ℓ 1 (↑-var-s #x n s))))

-- test-conv-1 : conv {_} {_} {0} 1 ([ ~ int ,, int ]) ([ var {10} (fin 3) ,, var (fin 5) ]) (free (var (fin 1)))
--             ≡ region (push (~ int) ((var fZ ⇐ use (var (fin 4))) seq push int ((var fZ ⇐ use (var (fin 7))) seq free (var (fin 1)))))
-- test-conv-1 = refl
-- test-conv-2 : conv {_} {_} {0} 1 ([ & (val (fin 0)) imm int ]) ([ var {10} (fin 3) ]) skip
--             ≡ region (push (& (val (fin 0)) imm int) ((var fZ ⇐ use (var (fin 4))) seq skip))
-- test-conv-2 = refl

-- -- Typing for statements.
-- data stok {#f} (F : Vec (Func #f) #f) : (#x #ℓ : ℕ) → Context #ℓ #x → State #ℓ #x
--                                       → Stmt #f #x #ℓ → State #ℓ #x → Set

-- -- Typing for functions.
-- record fnok {#f} (F : Vec (Func #f) #f) (func : Func #f) : Set where
--   constructor fn
--   field
--     {Δ} : Vec (Shape 1) _
--     -- The body is a well-typed statement when the arguments are in scope (initialized)
--     body-ok : stok F _ 1
--                    (rev (args func))
--                    (rev (map init-t (args func)))
--                    (body func)
--                    Δ
--     -- The body cleans up after itself (freeing any heap memory it was responsible for)
--     cleans-up : All (λ x → fst x ⊢ snd x Dropped) (zip (rev (args func)) Δ)

-- data stok {#f} (F : Vec (Func #f) #f) where
--   -- Skip changes nothing
--   skip : ∀ {#x #ℓ Γ Δ} → stok F #x #ℓ Γ Δ skip Δ
--   -- Seq threads Shape data through the statements
--   _seq_ : ∀ {#x #ℓ Γ Δ₀ Δ₁ Δ₂ s₁ s₂}
--         → stok F #x #ℓ Γ Δ₀ s₁ Δ₁
--         → stok F #x #ℓ Γ Δ₁ s₂ Δ₂
--         → stok F #x #ℓ Γ Δ₀ (s₁ seq s₂) Δ₂ 
--   -- Push ensures that the wrapped statement
--   push : ∀ {#x #ℓ Γ Δ τ s δ′ Δ′}
--        -- is well typed when the context is extended
--        → stok F (S #x) #ℓ (τ ∷ Γ) (void-t τ ∷ Δ) s (δ′ ∷ Δ′)
--        -- cleans up after itself if necessary
--        → τ ⊢ δ′ Dropped
--        → stok F #x #ℓ Γ Δ (push τ s) Δ′
--   -- Pop is just a flag to the evalutator
--   pop : ∀ {#x #ℓ Γ Δ s Δ′}
--          → stok F (S #x) #ℓ Γ Δ s Δ′
--          → stok F (S #x) #ℓ Γ Δ (pop s) Δ′
--   -- Region ensures that the wrapped statement
--   region : ∀ {#x #ℓ Γ Δ s Δ′ ↓Δ′}
--          -- is well typed when the lifetime relation is extended
--          → stok F #x (S #ℓ) (map (↑-#ℓ-t 1 0) Γ) (map (↑-#ℓ-sh 1 0) Δ) s Δ′
--          -- provides output Shape data that can be downshifted
--          → ↓1-#ℓ-shs 0 Δ′ ↓Δ′
--          → stok F #x #ℓ Γ Δ (region s) ↓Δ′
--   -- Unregion is just a flag tot he evalutator
--   unregion : ∀ {#x #ℓ Γ Δ₀ s Δ₁}
--            → stok F #x (S #ℓ) Γ Δ₀ s Δ₁
--            → stok F #x (S #ℓ) Γ Δ₀ (unregion s) Δ₁
--   -- Assignment is ok if
--   ⇐ok : ∀ {#x #ℓ Γ Δ₀ p e τᵣ τₗ Δ₁ Δ₂}
--       -- the RHS is well typed
--       → Γ , Δ₀ ⊢ e ∶ τᵣ , Δ₁ expr
--       -- the LHS can be initialized once we've used the RHS
--       → Δ₁ ⊢ p can-init
--       -- the LHS is well typed
--       → Γ ⊢ p ∶ τₗ
--       -- the RHS is a subtype of the LHS
--       → τᵣ <: τₗ
--       -- the LHS can be marked initialized in the output
--       → Γ , Δ₁ ⊢ p ⇒ Δ₂ init
--       → stok F #x #ℓ Γ Δ₀ (p ⇐ e) Δ₂
--   -- Free is ok if
--   free : ∀ {#x #ℓ Γ Δ₀ p τ δ Δ₁}
--        -- The argument is a unique pointer
--        → Γ ⊢ p ∶ ~ τ
--        -- With cleaned up contents
--        → Δ₀ ⊢ * p ∶ δ shape
--        → τ ⊢ δ Dropped
--        -- So we mark it as deinitialized in the output
--        → Γ , Δ₀ ⊢ p ⇒ Δ₁ deinit
--        → stok F #x #ℓ Γ Δ₀ (free p) Δ₁
--   -- Calling a function is ok if
--   call : ∀ {#x #ℓ Γ Δ₀ Δ₁ f τs} {ps : Vec (Path #x) (#args (F ! f))}
--        -- the function is well formed
--        → fnok F (F ! f)
--        -- we can safely use the arguments
--        → Γ , Δ₀ ⊢ ps ∶ τs , Δ₁ use-many
--        -- and formal parameter types are subtypes of the argument types
--        → All (λ { (f , p) → f <: p })
--              (zip (map (↑-#ℓ-t′ #ℓ 0) (args (F ! f)))
--                   (map (↑-#ℓ-t 1 0) τs))
--        → stok F #x #ℓ Γ Δ₀ (call f ps) Δ₁
--   -- Matching by value is ok if
--   matchbyval : ∀ {#x #ℓ Γ Δ₀ p sₛ sₙ τ Δ₁ Δ₂} -- δ}
--              -- path safe to use (and is an option)
--              → Γ , Δ₀ ⊢ p ∶ opt τ , Δ₁ use
--              ---- arms of match are ok
--              -- Some:
--              -- there is a shape
--              → (δ : Shape #ℓ)
--              -- that's cleaned up
--              → τ ⊢ δ Dropped
--              -- which can be left over after evalutating the block
--              → stok F (S #x) (S #ℓ)
--                     (map (↑-#ℓ-t 1 0) (τ ∷ Γ))
--                     (map (↑-#ℓ-sh 1 0) ((init-t τ) ∷ Δ₁))
--                     sₛ
--                     (map (↑-#ℓ-sh 1 0) (δ ∷ Δ₂))
--              -- None:
--              -- the body is ok
--              → stok F #x #ℓ Γ Δ₁ sₙ Δ₂
--              ---- the arms are consistent
--              -- note that we required the none arm and the some arm to share Δ₂
--              -- so they have the same init/loan info
--              → stok F #x #ℓ Γ Δ₀ (matchbyval p sₛ sₙ) Δ₂

-- test-stok-1 : stok [] 0 0 [] [] (push int skip) []
-- test-stok-1 = push skip int
-- test-stok-2 : stok [] 0 0 [] [] (push int (var fZ ⇐ int 1)) []
-- test-stok-2 = push (⇐ok int (int void , (var , int)) var int (int , (var , var))) int
-- test-stok-3 : stok [] 3 0 ([ opt int ,, int ,, int ])
--               ([ opt (init (bank-def _) tt) ,, int (init (bank-def _) tt) ,, int void ])
--               (matchbyval (var fZ)
--                 (var (fin 3) ⇐ add (var (fin 0)) (var (fin 2)))
--                 (var (fin 2) ⇐ int 0))
--               ([ opt (init (bank-def _) tt) ,, int (init (bank-def _) tt) ,, int (init (bank-def _) tt) ])
-- test-stok-3 = matchbyval (copy var (opt int) (can-access (_ , (var , opt))))
--                          (int (init (bank [] free) tt))
--                          int
--                          (⇐ok (add (copy var int (can-access (_ , (var , int))))
--                                    (copy var int (can-access (_ , (var , int)))))
--                               (int void , (var , int)) var int (int , (var , var)))
--                          (⇐ok int (int void , (var , int)) var int (int , (var , var)))
-- test-stok-4 : stok [] 1 0 ([ ~ int ]) ([ ~ (init (bank-def _) (int (init (bank-def _) tt))) ])
--               (free (var fZ)) ([ ~ void ])
-- test-stok-4 = free var (*~ var) int (~ int , (var , var))
-- test-stok-5 : ¬ (stok [] 1 0 ([ ~ (~ int) ]) ([ ~ (init (bank-def _) (~ (init (bank-def _) (int (init (bank-def _) tt))))) ])
--                 (pop skip) ([ ~ void ]))
-- test-stok-5 (pop ())
-- test-stok-6 : stok [] 1 0 ([ ~ (~ int) ]) ([ ~ void ]) (pop skip) ([ ~ void ])
-- test-stok-6 = pop skip
-- test-stok-7 : stok ([ fn ([ int ,, int ]) skip ])
--                    2 0 
--                    ([ int ,, int ])
--                    ([ int (init (bank-def _) tt) ,, int (init (bank-def _) tt) ])
--                    (call fZ ([ var (fin 0) ,, var (fin 1) ]))
--                    ([ int (init (bank-def _) tt) ,, int (init (bank-def _) tt) ])
-- test-stok-7 = call (fn skip (int ∷ int ∷ []))
--                    (copy var int (can-access ((int (init (bank [] free) tt)) , (var , int)))
--                   ∷ copy var int (can-access ((int (init (bank [] free) tt)) , (var , int)))
--                   ∷ [])
--                    (int ∷ int ∷ [])
-- test-stok-8 : stok [] 1 3
--               ([ & (val (fin 1)) imm (& (val (fin 2)) imm int) ])
--               ([ & (init (bank-def _) (& (val (fin 2)) imm int)) ])
--               (unregion skip)
--               ([ & (init (bank-def _) (& (val (fin 2)) imm int)) ])
-- test-stok-8 = unregion skip

-- test-fnok-1 : fnok [] (fn ([ ~ int ,, ~ int ]) (free (var fZ) seq free (var (fin 1))))
-- test-fnok-1 = fn (free var (*~ var) int (~ int , (var , var)) seq
--                   free var (*~ var) int (~ int , (var , var)))
--                  (~ ∷ ~ ∷ [])
-- test-fnok-2 : ¬ (fnok [] (fn ([ ~ int ]) skip))
-- test-fnok-2 (fn skip (() ∷ []))

-- -- Statement evalutation can change the number of variables, allocations, or the lifetime relation
-- data stev {#f} (F : Vec (Func #f) #f) : (#x₁ #a₁ #ℓ₁ : ℕ) → Context #ℓ₁ #x₁ → Map #a₁ #x₁
--                                       → Heap #a₁ → Stmt #f #x₁ #ℓ₁
--                                       → (#x₂ #a₂ #ℓ₂ : ℕ) → Context #ℓ₂ #x₂ → Map #a₂ #x₂
--                                       → Heap #a₂ → Stmt #f #x₂ #ℓ₂ → Set where
--   -- if the LHS of a seq finishes, then proceed to the RHS
--   skipseq : ∀ {#x #a #ℓ T V H s} → stev F #x #a #ℓ T V H (skip seq s) #x #a #ℓ T V H s
--   -- if the LHS of a seq can step, then step it
--   stepseq : ∀ {#x #ℓ #a₁ T V₁ H₁ s₁ #a₂ V₂ H₂ s₁′ s₂}
--           → stev F #x #a₁ #ℓ T V₁ H₁ s₁ #x #a₂ #ℓ T V₂ H₂ s₁′
--           → stev F #x #a₁ #ℓ T V₁ H₁ (s₁ seq s₂) #x #a₂ #ℓ T V₂ H₂ (s₁′ seq s₂)
--   -- to push a new stack variable
--   push : ∀ {#x #a #ℓ T V H τ s l}
--        -- determine an uninitialized layout
--        → layoutof τ l
--        → stev F #x #a #ℓ T V H (push τ s)
--          -- extend the context with the type
--          (S #x) (S #a) #ℓ (τ ∷ T)
--          -- map the new variable to the new allocation
--          (fZ ∷ map (raise 1) V)
--          -- which is just the empty layout we created
--          (l ∷ (map (↑-alloc-l 1 0) H))
--          -- change the push to a pop
--          (pop s)
--   -- if the statement in a pop is finished
--   pop-skip : ∀ {#x #a #ℓ τ T α V ↓V l H ↓H}
--               -- downshift the map
--               → ↓xs 0 V ↓V
--               -- and the heap
--               → ↓-#a-ls 0 H ↓H
--               → stev F (S #x) (S #a) #ℓ (τ ∷ T) (α ∷ V) (l ∷ H) (pop skip) #x #a #ℓ T ↓V ↓H skip
--   -- if the statement in a pop can step, then step it
--   pop-step : ∀ {#x #a #ℓ T V H s #a′ V′ H′ s′}
--               → stev F (S #x) #a #ℓ T V H s (S #x) #a′ #ℓ T V′ H′ s′
--               → stev F (S #x) #a #ℓ T V H (pop s) (S #x) #a′ #ℓ T V′ H′ (pop s′)
--   -- to push a new region, just upshift the type context
--   region : ∀ {#x #a #ℓ T V H s}
--          → stev F #x #a #ℓ T V H (region s) #x #a (S #ℓ) (map (↑-#ℓ-t 1 0) T) V H (unregion s)
--   -- if the statement in a unregion is down, then downshift the context
--   unregion-skip : ∀ {#x #a #ℓ T V H ↓T}
--                 → ↓1-#ℓ-ts 0 T ↓T
--                 → stev F #x #a (S #ℓ) T V H (unregion skip) #x #a #ℓ ↓T V H skip
--   -- if the statement in an unregion can step, then step it
--   unregion-step : ∀ {#x #a #ℓ T V H s #a′ V′ H′ s′}
--                 → stev F #x #a (S #ℓ) T V H s #x #a′ (S #ℓ) T V′ H′ s′
--                 → stev F #x #a (S #ℓ) T V H (unregion s) #x #a′ (S #ℓ) T V′ H′ (unregion s′)
--   -- assign an expression to a path by
--   ⇐ev : ∀ {#x #a #ℓ T V Hᵢ Hₒ p e α}
--       -- finding where the path points to
--       → T , V , Hᵢ ⊢ p ⟶ α
--       -- and using it as the destination for evaluating the expression
--       → #a ∣ T , V , Hᵢ ⊢ α ← e ⟶ #a ∣ Hₒ
--       → stev F #x #a #ℓ T V Hᵢ (p ⇐ e) #x #a #ℓ T V Hₒ skip
--   -- similar, but the new expression increments the allocation count, so we need to shift some things
--   ⇐ev-new : ∀ {#x #a #ℓ T V Hᵢ Hₒ p e α}
--           → T , V , Hᵢ ⊢ p ⟶ α
--           → #a ∣ T , V , Hᵢ ⊢ α ← e ⟶ S #a ∣ Hₒ
--           → stev F #x #a #ℓ T V Hᵢ (p ⇐ e) #x (S #a) #ℓ T (map (raise 1) V) Hₒ skip
--   -- free heap memory by
--   free : ∀ {#x #a #ℓ T V H p α α′ H′ H′′}
--        -- finding where the path goes
--        → T , map (↑-fin 1 (asℕ α′)) V , H ⊢ p ⟶ α
--        -- finding which allocation it points to
--        → H ⊢ α ⇒ ptr (val (alloc α′))
--        -- set it to void
--        → H ⊢ α ≔ ptr void ⇒ H′
--        -- remove the pointed-to allocation from the heap
--        → remove-elem H′ α′ (map (↑-alloc-l 1 (asℕ α′)) H′′)
--        → stev F #x (S #a) #ℓ T (map (↑-fin 1 (asℕ α′)) V) H (free p) #x #a #ℓ T V H′′ skip
--   -- call a function by replacing the call with the expanded body
--   call : ∀ {#x #a #ℓ T V H f} {ps : Vec (Path #x) (#args (F ! f))}
--        → stev F #x #a #ℓ T V H (call f ps)
--                 #x #a #ℓ T V H (conv #ℓ (args (F ! f)) ps (body (F ! f)))
--   -- match on a none by value by
--   matchnonebyval : ∀ {#x #a #ℓ T V H p sₛ sₙ α l}
--                  -- finding out where the path goes
--                  → T , V , H ⊢ p ⟶ α
--                  -- ensuring a none occupies p
--                  → H ⊢ α ⇒ rec ([ int (val 0) ,, l ])
--                  -- and then going to the none statement
--                  → stev F #x #a #ℓ T V H (matchbyval p sₛ sₙ) #x #a #ℓ T V H sₙ
--   -- match on a some by value by
--   matchsomebyval : ∀ {#x #a #ℓ T V H p sₛ sₙ α l τ}
--                  -- ensuring the path points to an option
--                  → T ⊢ p ∶ opt τ
--                  -- finding out where it points
--                  → T , V , H ⊢ p ⟶ α
--                  -- ensuring a some occupies that spot
--                  → H ⊢ α ⇒ rec ([ int (val 1) ,, l ])
--                  -- pushing the contents onto the stack and executing the some statement
--                  → stev F #x #a #ℓ T V H (matchbyval p sₛ sₙ)
--                           (S #x) (S #a) (S #ℓ)
--                           (map (↑-#ℓ-t 1 0) (τ ∷ T))
--                           (fZ ∷ map (raise 1) V)
--                           (map (↑-alloc-l 1 0) (l ∷ H))
--                           (unregion (pop sₛ))

-- test-stev-1 : stev [] 0 0 0 [] [] [] (push int skip)
--                    1 1 0 ([ int ]) ([ fZ ]) ([ int void ]) (pop skip)
-- test-stev-1 = push int
-- test-stev-2 : stev [] 1 1 0 ([ int ]) ([ fZ ]) ([ int void ]) (pop skip)
--                    0 0 0 [] [] [] skip 
-- test-stev-2 = pop-skip [] []
-- test-stev-3 : stev [] 1 1 0 ([ int ]) ([ fZ ]) ([ int void ]) (var fZ ⇐ int 1)
--                    1 1 0 ([ int ]) ([ fZ ]) ([ int (val 1) ]) skip
-- test-stev-3 = ⇐ev var (int alloc)
-- test-stev-4 : stev [] 1 1 0 ([ int ]) ([ fZ ]) ([ int (val 1) ]) (pop skip)
--                    0 0 0 [] [] [] skip 
-- test-stev-4 = pop-skip [] []
-- test-stev-5 : stev [] 3 3 0
--               ([ opt int ,, int ,, int ])
--               ([ fin 0 ,, fin 1 ,, fin 2 ])
--               ([ rec ([ int (val 0) ,, int void ]) ,, int (val 1) ,, int void ])
--               (matchbyval (var fZ)
--                           (var (fin 3) ⇐ add (var (fin 0)) (var (fin 2)))
--                           (var (fin 2) ⇐ int 0))
--               3 3 0
--               ([ opt int ,, int ,, int ])
--               ([ fin 0 ,, fin 1 ,, fin 2 ])
--               ([ rec ([ int (val 0) ,, int void ]) ,, int (val 1) ,, int void ])
--               (var (fin 2) ⇐ int 0)
-- test-stev-5 = matchnonebyval var alloc
-- test-stev-6 : stev [] 3 3 0
--               ([ opt int ,, int ,, int ])
--               ([ fin 0 ,, fin 1 ,, fin 2 ])
--               ([ rec ([ int (val 1) ,, int (val 1) ]) ,, int (val 1) ,, int void ])
--               (matchbyval (var fZ)
--                           (var (fin 3) ⇐ add (var (fin 0)) (var (fin 2)))
--                           (var (fin 2) ⇐ int 0))
--               4 4 1
--               ([ int ,, opt int ,, int ,, int ])
--               ([ fin 0 ,, fin 1 ,, fin 2 ,, fin 3 ])
--               ([ int (val 1) ,, rec ([ int (val 1) ,, int (val 1) ]) ,, int (val 1) ,, int void ])
--               (unregion (pop (var (fin 3) ⇐ add (var (fin 0)) (var (fin 2)))))
-- test-stev-6 = matchsomebyval var var alloc
-- test-stev-7 : stev [] 2 2 0
--                    ([ ~ int ,, int ])
--                    ([ fin 0 ,, fin 1 ])
--                    ([ ptr void ,, int (val 1) ])
--                    (var fZ ⇐ new (var (fin 1)))
--                    2 3 0
--                    ([ ~ int ,, int ])
--                    ([ fin 1 ,, fin 2 ])
--                    ([ int (val 1) ,, ptr (val (alloc fZ)) ,, int (val 1) ])
--                    skip
-- test-stev-7 = ⇐ev-new var (new var int var (int (val 1) , (alloc , alloc)) alloc)
-- test-stev-8 : stev [] 1 5 0
--                    ([ ~ (~ (~ (~ int))) ])
--                    ([ fZ ])
--                    ([ ptr (val (alloc (fin 3)))
--                    ,, ptr (val (alloc (fin 4)))
--                    ,, int (val 1)
--                    ,, ptr (val (alloc (fin 1)))
--                    ,, ptr (val (alloc (fin 2))) ])
--                    (free (* (* (* (var fZ)))))
--                    1 4 0
--                    ([ ~ (~ (~ (~ int))) ])
--                    ([ fZ ])
--                    ([ ptr (val (alloc (fin 2)))
--                    ,, ptr (val (alloc (fin 3)))
--                    ,, ptr (val (alloc (fin 1)))
--                    ,, ptr void ])
--                    skip
-- test-stev-8 = free (* (* (* var)))
--                    (* (* (* alloc alloc) alloc) alloc)
--                    (* (* (* alloc alloc) alloc) alloc)
--                    (re-S (re-S re-Z))
-- test-stev-9 : stev ([ fn ([ int ,, int ]) skip ])
--                    2 2 0
--                    ([ int ,, int ])
--                    ([ fin 0 ,, fin 1 ])
--                    ([ int (val 1) ,, int (val 2) ])
--                    (call (fin 0) ([ var (fin 0) ,, var (fin 1) ]))
--                    2 2 0
--                    ([ int ,, int ])
--                    ([ fin 0 ,, fin 1 ])
--                    ([ int (val 1) ,, int (val 2) ])
--                    (region
--                      (push int ((var fZ ⇐ use (var (fin 1))) seq
--                       push int ((var fZ ⇐ use (var (fin 3))) seq
--                       skip))))
-- test-stev-9 = call
