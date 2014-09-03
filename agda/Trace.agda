open import Common
open import Type
open import Layout
open import Shape
open import Path
open import Expr
open import Stmt
open import Route
open import Life
module Trace where

infixr 5 _>>_ _pop_
data Trace (#f : ℕ) : (#x #ℓ : ℕ) → Set where
  ∅ : ∀ {#x #ℓ} → Trace #f #x #ℓ
  _>>_ : ∀ {#x #ℓ} → Stmt #f #x #ℓ → Trace #f #x #ℓ → Trace #f #x #ℓ
  _pop_ : ∀ {#x #ℓ} → Stmt #f (S #x) (S #ℓ) → Trace #f #x #ℓ → Trace #f (S #x) (S #ℓ)

_seq>>_ : ∀ {#f #x #ℓ} → Seq #f #x #ℓ → Trace #f #x #ℓ → Trace #f #x #ℓ
∅ seq>> t = t
(s >> sq) seq>> t = s >> sq seq>> t

_seqpop_ : ∀ {#f #x #ℓ} → Seq #f (S #x) (S #ℓ) → Trace #f #x #ℓ → Trace #f (S #x) (S #ℓ)
∅ seqpop t = skip pop t
(s >> sq) seqpop t = s >> sq seqpop t

data tok {#f} (F : Funcs #f) : ∀ {#x #ℓ #x′ #ℓ′} → Cxt #ℓ #x → Lifes #ℓ #x → State #ℓ #x
                             → Trace #f #x #ℓ → State #ℓ′ #x′ → Set where
  ∅ : ∀ {#x #ℓ L Δ} {Γ : Cxt #ℓ #x} → tok F Γ L Δ ∅ Δ
  _>>_ : ∀ {#x #ℓ s t L Δ₀ Δ₁} {Γ : Cxt #ℓ #x} {Δ₂ : State #ℓ #x}
        → stok F Γ L Δ₀ s  Δ₁
        → tok F Γ L Δ₁ t  Δ₂
        → tok F Γ L Δ₀ (s >> t) Δ₂ 
  _∶_,_,_,_pop_ : ∀ {#x #ℓ s t τ ↓Γ ℓ L ↓L Δ₀ δ Δ₁ ↓Δ₁} {Γ : Cxt (S #ℓ) #x} {Δ₂ : State #ℓ #x}
                → stok F (τ ∷ Γ) (ℓ ∷ L) Δ₀ s (δ ∷ Δ₁)
                → τ ⊢ δ Dropped
                → All2 (↓#ℓ-δ 0) Δ₁ ↓Δ₁
                → All2 (↓#ℓ-τ 0) Γ ↓Γ
                → All2 (↓#ℓ-ℓ 0) L ↓L
                → tok F ↓Γ ↓L ↓Δ₁ t Δ₂
                → tok F (τ ∷ Γ) (ℓ ∷ L) Δ₀ (s pop t) Δ₂

data stev {#f} (F : Funcs #f) : ∀ {#x #a #ℓ #x′ #a′ #ℓ′}
     → Cxt #ℓ #x → Mem #x #a → Stmt #f #x #ℓ → Trace #f #x #ℓ
     → Cxt #ℓ′ #x′ → Mem #x′ #a′ → Trace #f #x′ #ℓ′ → Set where
  ←old : ∀ {#x #a #ℓ p r e l t} {Γ : Cxt #ℓ #x} {M M′ M′′ : Mem #x #a}
       → Γ , M ⊢ e ⟶ inl (l , M′)
       → M′ ⊢ p ⟶ r
       → M′ ⊢ r ≔ l ⇒ M′′
       → stev F Γ M (p ← e) t Γ M′′ t
  ←new : ∀ {#x #a #ℓ p r e l t M′ M′′} {Γ : Cxt #ℓ #x} {M : Mem #x #a}
       → Γ , M ⊢ e ⟶ inr (l , M′)
       → M′ ⊢ p ⟶ r
       → M′ ⊢ r ≔ l ⇒ M′′
       → stev F Γ M (p ← e) t Γ M′′ t
  free : ∀ {#x #a #ℓ p r a St₁ H₂ ↓St₁ ↓H₂ t}
       {Γ : Cxt #ℓ #x} {M₀ : Mem #x (S #a)} {H₁ : Heap #x (S #a)}
       → M₀ ⊢ p ⟶ r
       → M₀ ⊢ r ⇒ ptr (just (heap a))
       → M₀ ⊢ r ≔ ptr none ⇒ (St₁ , H₁)
       → remove-elem H₁ a H₂
       → All2 (↓#a-l 0) St₁ ↓St₁
       → All2 (↓#a-l 0) H₂ ↓H₂
       → stev F Γ M₀ (free p) t Γ (↓St₁ , ↓H₂) t
  push : ∀ {#x #a #ℓ τ l sq t St} {Γ : Cxt #ℓ #x} {H : Heap #x #a}
       → void-layout τ l
       → stev F Γ (St , H) (push τ sq) t
         (τ ∷ map (↑#ℓ-τ 0) Γ)
         ((l ∷ map (↑#x-l 0) St) , map (↑#x-l 0) H)
         (sq seqpop t)
  call : ∀ {#x #a #ℓ f p t} {Γ : Cxt #ℓ #x} {M : Mem #x #a}
       → stev F Γ M (call f p) t Γ M (conv (F ! f) p >> t)
  none : ∀ {#x #a #ℓ p r l sₛ sₙ t} {Γ : Cxt #ℓ #x} {M : Mem #x #a}
       → M ⊢ p ⟶ r
       → M ⊢ r ⇒ rec ([ int (just 0) ,, l ])
       → stev F Γ M (match p sₛ sₙ) t Γ M (sₙ seq>> t)
  some : ∀ {#x #a #ℓ p r l τ t sₛ sₙ St St′} {Γ : Cxt #ℓ #x} {H H′ : Heap #x #a}
       → Γ ⊢ p ∶ opt τ path
       → (St , H) ⊢ p ⟶ r
       → (St , H) ⊢ r ∶ opt τ ⇒ rec ([ int (just 1) ,, l ]) , (St′ , H′)
       → stev F Γ (St , H) (match p sₛ sₙ) t
             (map (↑#ℓ-τ 0) (τ ∷ Γ))
             (map (↑#x-l 0) (l ∷ St′) , map (↑#x-l 0) H′)
             (sₛ seqpop t)

data tev {#f} (F : Funcs #f) : ∀ {#x #a #ℓ #x′ #a′ #ℓ′}
                             → Cxt #ℓ #x → Mem #x #a → Trace #f #x #ℓ
                             → Cxt #ℓ′ #x′ → Mem #x′ #a′ → Trace #f #x′ #ℓ′ → Set where
  skip>> : ∀ {#x #a #ℓ t} {Γ : Cxt #ℓ #x} {M : Mem #x #a} → tev F Γ M (skip >> t) Γ M t
  skippop : ∀ {#x #a #ℓ τ l t St ↓Γ ↓St ↓H} {Γ : Cxt (S #ℓ) #x} {H : Heap (S #x) #a}
          → All2 (↓#x-l 0) St ↓St
          → All2 (↓#x-l 0) H ↓H
          → All2 (↓#ℓ-τ 0) Γ ↓Γ
          → tev F (τ ∷ Γ) ((l ∷ St) , H) (skip pop t) ↓Γ (↓St , ↓H) t
  ⟶>> : ∀ {#x #a #ℓ #x′ #a′ #ℓ′ s t t′}
        {Γ : Cxt #ℓ #x} {M : Mem #x #a} {Γ′ : Cxt #ℓ′ #x′} {M′ : Mem #x′ #a′}
        → stev F Γ M s t Γ′ M′ t′
        → tev F Γ M (s >> t) Γ′ M′ t′
  ⟶pop : ∀ {#x #a #ℓ #x′ #a′ #ℓ′ s t t′}
         {Γ : Cxt (S #ℓ) (S #x)} {M : Mem (S #x) #a} {Γ′ : Cxt #ℓ′ #x′} {M′ : Mem #x′ #a′}
         → stev F Γ M s (skip pop t) Γ′ M′ t′
         → tev F Γ M (s pop t) Γ′ M′ t′

module TestTrace where
  open import Loan

  ok-1 : tok [] ([ ~ int ,, int {2} ]) ([ val fZ ,, val (fin 1) ]) ([ ~ none ,, int none ])
             (skip pop ∅) ([ int {1} none ])
  ok-1 = skip ∶ ~-drop , (int none ∷ []) , int ∷ [] , val (S≥ z<s) ∷ [] pop ∅
  ok-2 : ¬ (tok [] {#ℓ′ = 0} ([ ~ {1} int ]) ([ val fZ ]) ([ ~ (just ((bank-def _) , (int none))) ])
                (skip pop ∅) [])
  ok-2 (skip ∶ () , _ , _ , _ pop _)

  ev-1 : tev [] {#ℓ = 0} [] ([] , []) (push (~ int) ∅ >> ∅)
             ([ ~ {1} int ]) (([ ptr none ]) , []) (skip pop ∅)
  ev-1 = ⟶>> (push ~⊥)
  ev-2 : tev [] {#ℓ′ = 0} ([ ~ {1} int ]) (([ ptr none ]) , []) (skip pop ∅)
             [] ([] , []) ∅
  ev-2 = skippop [] [] []
  ev-3 : tev [] {#ℓ′ = 0} ([ ~ {1} int ]) (([ ptr (just (heap fZ)) ]) , ([ int (just 1) ]))
             (skip pop ∅) [] ([] , ([ int (just 1) ])) ∅
  ev-3 = skippop [] (int ∷ []) []
  ev-4 : tev [] ([ int {1} ]) (([ int none ]) , []) (var fZ ← int 0 >> ∅)
             ([ int {1} ]) (([ int (just 0) ]) , []) ∅
  ev-4 = ⟶>> (←old int var stack)
  ev-5 : tev [] ([ ~ {2} int ,, int ])
               (([ ptr none ,, int (just 0) ])
             , ([ ptr (just (heap fZ)) ]))
             (var fZ ← new (var (fin 1)) >> ∅)
             ([ ~ {2} int ,, int ])
              (([ ptr (just (heap fZ)) ,, int (just 0) ])
             , ([ int (just 0) ,, ptr (just (heap (fin 1))) ]))
             ∅
  ev-5 = ⟶>> (←new (new var var (copy int stack) heap) var stack)
  ev-6 : tev [] ([ int {1} ])
             (([ int (just 1) ]) , [])
             (push (~ int) (var fZ ← new (var (fin 1)) >> free (var fZ) >> ∅) >> ∅)
             ([ ~ {2} int ,, int ])
             (([ ptr none ,, int (just 1) ]) , [])
             (var fZ ← new (var (fin 1)) >> free (var fZ) >> skip pop ∅)
  ev-6 = ⟶>> (push ~⊥)
  ev-7 : tev [] ([ ~ {2} int ,, int ])
             (([ ptr none ,, int (just 1) ]) , [])
             (var fZ ← new (var (fin 1)) >> free (var fZ) >> skip pop ∅)
             ([ ~ {2} int ,, int ])
             (([ ptr (just (heap fZ)) ,, int (just 1) ]) , ([ int (just 1) ]))
             (free (var fZ) >> skip pop ∅)
  ev-7 = ⟶>> (←new (new var var (copy int stack) heap) var stack)
  ev-8 : tev [] ([ ~ {2} int ,, int ])
             (([ ptr (just (heap fZ)) ,, int (just 1) ]) , ([ int (just 1) ]))
             (free (var fZ) >> skip pop ∅)
             ([ ~ {2} int ,, int ])
             (([ ptr none ,, int (just 1) ]) , [])
             (skip pop ∅)
  ev-8 = ⟶>> (free var stack stack re-Z (ptr none ∷ (int ∷ [])) [])
  ev-9 : tev [] ([ ~ {2} int ,, int ])
             (([ ptr none ,, int (just 1) ]) , [])
             (skip pop ∅)
             ([ int {1} ])
             (([ int (just 1) ]) , [])
             ∅
  ev-9 = skippop (int ∷ []) [] (int ∷ [])
  ev-10 : tev [] ([ opt {2} int ,, int ])
              (([ rec ([ int (just 0) ,, int none ]) ,, int none ]) , [])
              (match (var fZ) (var (fin 2) ← use (var fZ) >> ∅) (var (fin 1) ← int 0 >> ∅) >> ∅)
              ([ opt {2} int ,, int ])
              (([ rec ([ int (just 0) ,, int none ]) ,, int none ]) , [])
              (var (fin 1) ← int 0 >> ∅)
  ev-10 = ⟶>> (none var stack)
  ev-11 : tev [] ([ opt {2} int ,, int ])
              (([ rec ([ int (just 0) ,, int none ]) ,, int none ]) , [])
              (var (fin 1) ← int 0 >> ∅)
              ([ opt {2} int ,, int ])
              (([ rec ([ int (just 0) ,, int none ]) ,, int (just 0) ]) , [])
              ∅
  ev-11 = ⟶>> (←old int var stack)
  ev-12 : tev [] ([ opt {2} int ,, int ])
              (([ rec ([ int (just 1) ,, int (just 10) ]) ,, int none ]) , [])
              (match (var fZ) (var (fin 2) ← use (var fZ) >> ∅) (var (fin 1) ← int 0 >> ∅) >> ∅)
              ([ int {3} ,, opt int ,, int ])
              (([ int (just 10) ,, rec ([ int (just 1) ,, int (just 10) ]) ,, int none ]) , [])
              (var (fin 2) ← use (var fZ) >> skip pop ∅)
  ev-12 = ⟶>> (some var var (copy (opt int) stack))
  ev-13 : tev [] ([ int {3} ,, opt int ,, int ])
              (([ int (just 10) ,, rec ([ int (just 1) ,, int (just 10) ]) ,, int none ]) , [])
              (var (fin 2) ← use (var fZ) >> skip pop ∅)
              ([ int {3} ,, opt int ,, int ])
              (([ int (just 10) ,, rec ([ int (just 1) ,, int (just 10) ]) ,, int (just 10) ]) , [])
              (skip pop ∅)
  ev-13 = ⟶>> (←old (use var var (copy int stack)) var stack)
  ev-14 : tev [] ([ int {3} ,, opt int ,, int ])
              (([ int (just 10) ,, rec ([ int (just 1) ,, int (just 10) ]) ,, int (just 10) ]) , [])
              (skip pop ∅)
              ([ opt {2} int ,, int ])
              (([ rec ([ int (just 1) ,, int (just 10) ]) ,, int (just 10) ]) , [])
              ∅
  ev-14 = skippop (rec (int ∷ (int ∷ [])) ∷ (int ∷ [])) [] (opt int ∷ (int ∷ []))
  ev-15 : tev ([ fn ( ~ int ) (free (var fZ) >> ∅) ])
              ([ ~ {10} int ])
              (([ ptr (just (heap fZ)) ]) , ([ int (just 1) ]))
              (call fZ (var fZ) >> ∅)
              ([ ~ {10} int ])
              (([ ptr (just (heap fZ)) ]) , ([ int (just 1) ]))
              (push (~ int) (var fZ ← use (var (fin 1)) >> free (var fZ) >> ∅) >> ∅)
  ev-15 = ⟶>> call
  ev-16 : tev ([ fn ( ~ int ) (free (var fZ) >> ∅) ])
              ([ ~ {10} int ])
              (([ ptr (just (heap fZ)) ]) , ([ int (just 1) ]))
              (push (~ int) (var fZ ← use (var (fin 1)) >> free (var fZ) >> ∅) >> ∅)
              ([ ~ {11} int ,, ~ int ])
              (([ ptr none ,, ptr (just (heap fZ)) ]) , ([ int (just 1) ]))
              (var fZ ← use (var (fin 1)) >> free (var fZ) >> skip pop ∅)
  ev-16 = ⟶>> (push ~⊥)
  ev-17 : tev ([ fn ( ~ int ) (free (var fZ) >> ∅) ])
              ([ ~ {11} int ,, ~ int ])
              (([ ptr none ,, ptr (just (heap fZ)) ]) , ([ int (just 1) ]))
              (var fZ ← use (var (fin 1)) >> free (var fZ) >> skip pop ∅)
              ([ ~ {11} int ,, ~ int ])
              (([ ptr (just (heap fZ)) ,, ptr none ]) , ([ int (just 1) ]))
              (free (var fZ) >> skip pop ∅)
  ev-17 = ⟶>> (←old (use var var (move ~Aff stack ~⊥ stack)) var stack)
  ev-18 : tev ([ fn ( ~ int ) (free (var fZ) >> ∅) ])
              ([ ~ {11} int ,, ~ int ])
              (([ ptr (just (heap fZ)) ,, ptr none ]) , ([ int (just 1) ]))
              (free (var fZ) >> skip pop ∅)
              ([ ~ {11} int ,, ~ int ])
              (([ ptr none ,, ptr none ]) , [])
              (skip pop ∅)
  ev-18 = ⟶>> (free var stack stack re-Z (ptr none ∷ (ptr none ∷ [])) [])
  ev-19 : tev ([ fn ( ~ int ) (free (var fZ) >> ∅) ])
              ([ ~ {11} int ,, ~ int ])
              (([ ptr none ,, ptr none ]) , [])
              (skip pop ∅)
              ([ ~ {10} int ])
              (([ ptr none ]) , [])
              ∅
  ev-19 = skippop (ptr none ∷ []) [] (~ int ∷ [])
  ev-20 : tev []
              ([ int {1} ])
              (([ int none ]) , [])
              (push int ∅ >> var fZ ← int 1 >> ∅)
              ([ int {2} ,, int ])
              (([ int none ,, int none ]) , [])
              (skip pop var fZ ← int 1 >> ∅)
  ev-20 = ⟶>> (push int)
  ev-21 : tev []
              ([ int {2} ,, int ])
              (([ int none ,, int none ]) , [])
              (skip pop var fZ ← int 1 >> ∅)
              ([ int {1} ])
              (([ int none ]) , [])
              (var fZ ← int 1 >> ∅)
  ev-21 = skippop (int ∷ []) [] (int ∷ [])
  ev-22 : tev []
              ([ int {1} ])
              (([ int none ]) , [])
              (var fZ ← int 1 >> ∅)
              ([ int {1} ])
              (([ int (just 1) ]) , [])
              ∅
  ev-22 = ⟶>> (←old int var stack)
