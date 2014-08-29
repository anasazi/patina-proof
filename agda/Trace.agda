open import Common
open import Type
open import Layout
open import Shape
open import Path
open import Expr
open import Stmt
open import Route
module Trace where

infixr 5 _>>_ _pop_ _end_
data Trace (#f : ℕ) : (#x #ℓ : ℕ) → Set where
  ∅ : ∀ {#x #ℓ} → Trace #f #x #ℓ
  _>>_ : ∀ {#x #ℓ} → Stmt #f #x #ℓ → Trace #f #x #ℓ → Trace #f #x #ℓ
  _pop_ : ∀ {#x #ℓ} → Stmt #f (S #x) #ℓ → Trace #f #x #ℓ → Trace #f (S #x) #ℓ
  _end_ : ∀ {#x #ℓ} → Stmt #f #x (S #ℓ) → Trace #f #x #ℓ → Trace #f #x (S #ℓ)

_seq>>_ : ∀ {#f #x #ℓ} → Seq #f #x #ℓ → Trace #f #x #ℓ → Trace #f #x #ℓ
∅ seq>> t = t
(s >> sq) seq>> t = s >> sq seq>> t

_seqpop_ : ∀ {#f #x #ℓ} → Seq #f (S #x) #ℓ → Trace #f #x #ℓ → Trace #f (S #x) #ℓ
∅ seqpop t = skip pop t
(s >> sq) seqpop t = s >> sq seqpop t

_seqend_ : ∀ {#f #x #ℓ} → Seq #f #x (S #ℓ) → Trace #f #x #ℓ → Trace #f #x (S #ℓ)
∅ seqend t = skip end t
(s >> sq) seqend t = s >> sq seqend t

_seqpopend_ : ∀ {#f #x #ℓ} → Seq #f (S #x) (S #ℓ) → Trace #f #x #ℓ → Trace #f (S #x) (S #ℓ)
∅ seqpopend t = skip pop skip end t
(s >> sq) seqpopend t = s >> sq seqpopend t

data tok {#f} (F : Funcs #f) : ∀ {#x #ℓ #x′ #ℓ′} → Context #ℓ #x → State #ℓ #x
                             → Trace #f #x #ℓ → State #ℓ′ #x′ → Set where
  ∅ : ∀ {#x #ℓ Δ} {Γ : Context #ℓ #x} → tok F Γ Δ ∅ Δ
  _>>_ : ∀ {#x #ℓ s t Δ₀ Δ₁} {Γ : Context #ℓ #x} {Δ₂ : State #ℓ #x}
        → stok F Γ Δ₀ s  Δ₁
        → tok F Γ Δ₁ t  Δ₂
        → tok F Γ Δ₀ (s >> t) Δ₂ 
  _∶_pop_ : ∀ {#x #ℓ s t τ δ Δ₀ Δ₁} {Γ : Context #ℓ #x} {Δ₂ : State #ℓ #x}
          → stok F (τ ∷ Γ) Δ₀ s (δ ∷ Δ₁)
          → τ ⊢ δ Dropped
          → tok F Γ Δ₁ t Δ₂
          → tok F (τ ∷ Γ) Δ₀ (s pop t) Δ₂
  _∶_,_end_ : ∀ {#x #ℓ Δ₀ s t ↓Γ ↓Δ₁} {Γ : Context (S #ℓ) #x} {Δ₁ : State (S #ℓ) #x} {Δ₂ : State #ℓ #x}
            → stok F Γ Δ₀ s Δ₁
            → All2 (↓#ℓ-δ 0) Δ₁ ↓Δ₁
            → All2 (↓#ℓ-τ 0) Γ ↓Γ
            → tok F ↓Γ ↓Δ₁ t Δ₂
            → tok F Γ Δ₀ (s end t) Δ₂

data stev {#f} (F : Funcs #f) : ∀ {#x #a #ℓ #x′ #a′ #ℓ′}
     → Context #ℓ #x → Mem #x #a → Stmt #f #x #ℓ → Trace #f #x #ℓ
     → Context #ℓ′ #x′ → Mem #x′ #a′ → Trace #f #x′ #ℓ′ → Set where
  ←old : ∀ {#x #a #ℓ p r e l t} {Γ : Context #ℓ #x} {M M′ M′′ : Mem #x #a}
       → Γ , M ⊢ e ⟶ inl (l , M′)
       → ⊢ p ⟶ r
       → M′ ⊢ r ≔ l ⇒ M′′
       → stev F Γ M (p ← e) t Γ M′′ t
  ←new : ∀ {#x #a #ℓ p r e l t M′ M′′} {Γ : Context #ℓ #x} {M : Mem #x #a}
       → Γ , M ⊢ e ⟶ inr (l , M′)
       → ⊢ p ⟶ r
       → M′ ⊢ r ≔ l ⇒ M′′
       → stev F Γ M (p ← e) t Γ M′′ t
  free : ∀ {#x #a #ℓ p r a St₁ H₂ ↓St₁ ↓H₂ t}
       {Γ : Context #ℓ #x} {M₀ : Mem #x (S #a)} {H₁ : Heap #x (S #a)}
       → ⊢ p ⟶ r
       → M₀ ⊢ r ⇒ ptr (just (heap a))
       → M₀ ⊢ r ≔ ptr none ⇒ (St₁ , H₁)
       → remove-elem H₁ a H₂
       → All2 (↓#a-l 0) St₁ ↓St₁
       → All2 (↓#a-l 0) H₂ ↓H₂
       → stev F Γ M₀ (free p) t Γ (↓St₁ , ↓H₂) t
  push : ∀ {#x #a #ℓ τ sq St t} {Γ : Context #ℓ #x} {H : Heap #x #a}
       → stev F Γ (St , H) (push τ sq) t
              (τ ∷ Γ) ((void-layout τ ∷ map (↑#x-l 0) St), map (↑#x-l 0) H) (sq seqpop t)
  region : ∀ {#x #a #ℓ sq t} {Γ : Context #ℓ #x} {M : Mem #x #a}
         → stev F Γ M (region sq) t (map (↑#ℓ-τ 0) Γ) M (sq seqend t)
  call : ∀ {#x #a #ℓ f p t} {Γ : Context #ℓ #x} {M : Mem #x #a}
       → stev F Γ M (call f p) t Γ M (conv (F ! f) p >> t)
  none : ∀ {#x #a #ℓ p r l sₛ sₙ t} {Γ : Context #ℓ #x} {M : Mem #x #a}
       → ⊢ p ⟶ r
       → M ⊢ r ⇒ rec ([ int (just 0) ,, l ])
       → stev F Γ M (match p sₛ sₙ) t Γ M (sₙ seq>> t)
  some : ∀ {#x #a #ℓ p r l τ t sₛ sₙ St St′} {Γ : Context #ℓ #x} {H H′ : Heap #x #a}
       → Γ ⊢ p ∶ opt τ
       → ⊢ p ⟶ r
       → (St , H) ⊢ r ∶ opt τ ⇒ rec ([ int (just 1) ,, l ]) , (St′ , H′)
       → stev F Γ (St , H) (match p sₛ sₙ) t
             (map (↑#ℓ-τ 0) (τ ∷ Γ))
             (map (↑#x-l 0) (l ∷ St′) , map (↑#x-l 0) H′)
             (sₛ seqpopend t)

data tev {#f} (F : Funcs #f) : ∀ {#x #a #ℓ #x′ #a′ #ℓ′}
                             → Context #ℓ #x → Mem #x #a → Trace #f #x #ℓ
                             → Context #ℓ′ #x′ → Mem #x′ #a′ → Trace #f #x′ #ℓ′ → Set where
  skip>> : ∀ {#x #a #ℓ t} {Γ : Context #ℓ #x} {M : Mem #x #a} → tev F Γ M (skip >> t) Γ M t
  skippop : ∀ {#x #a #ℓ τ t l St ↓St ↓H} {Γ : Context #ℓ #x} {H : Heap (S #x) #a}
          → All2 (↓#x-l 0) St ↓St
          → All2 (↓#x-l 0) H ↓H
          → tev F (τ ∷ Γ) ((l ∷ St) , H) (skip pop t) Γ (↓St , ↓H) t
  skipend : ∀ {#x #a #ℓ t ↓Γ} {Γ : Context (S #ℓ) #x} {M : Mem #x #a}
          → All2 (↓#ℓ-τ 0) Γ ↓Γ 
          → tev F Γ M (skip end t) ↓Γ M t
  ⟶>> : ∀ {#x #a #ℓ #x′ #a′ #ℓ′ s t t′}
        {Γ : Context #ℓ #x} {M : Mem #x #a} {Γ′ : Context #ℓ′ #x′} {M′ : Mem #x′ #a′}
        → stev F Γ M s t Γ′ M′ t′
        → tev F Γ M (s >> t) Γ′ M′ t′
  ⟶pop : ∀ {#x #a #ℓ #x′ #a′ #ℓ′ s t t′}
         {Γ : Context #ℓ (S #x)} {M : Mem (S #x) #a} {Γ′ : Context #ℓ′ #x′} {M′ : Mem #x′ #a′}
         → stev F Γ M s (skip pop t) Γ′ M′ t′
         → tev F Γ M (s pop t) Γ′ M′ t′
  ⟶end : ∀ {#x #a #ℓ #x′ #a′ #ℓ′ s t t′}
         {Γ : Context (S #ℓ) #x} {M : Mem #x #a} {Γ′ : Context #ℓ′ #x′} {M′ : Mem #x′ #a′}
         → stev F Γ M s (skip end t) Γ′ M′ t′
         → tev F Γ M (s end t) Γ′ M′ t′

module TestTrace where
  open import Loan

  ok-1 : tok [] ([ ~ int ,, int {0} ]) ([ ~ none ,, int none ])
             (skip pop ∅) ([ int {0} none ])
  ok-1 = skip ∶ ~ pop ∅
  ok-2 : ¬ (tok [] {#ℓ′ = 0} ([ ~ {0} int ]) ([ ~ (just ((bank-def _) , (int none))) ])
                (skip pop ∅) [])
  ok-2 (skip ∶ () pop pf)

  ev-1 : tev [] {#ℓ = 0} [] ([] , []) (push (~ int) ∅ >> ∅)
             ([ ~ {0} int ]) (([ ptr none ]) , []) (skip pop ∅)
  ev-1 = ⟶>> push
  ev-2 : tev [] {#ℓ′ = 0} ([ ~ {0} int ]) (([ ptr none ]) , []) (skip pop ∅)
             [] ([] , []) ∅
  ev-2 = skippop [] []
  ev-3 : tev [] {#ℓ′ = 0} ([ ~ {0} int ]) (([ ptr (just (heap fZ)) ]) , ([ int (just 1) ]))
             (skip pop ∅) [] ([] , ([ int (just 1) ])) ∅
  ev-3 = skippop [] (int ∷ [])
  ev-4 : tev [] ([ int {0} ]) (([ int none ]) , []) (var fZ ← int 0 >> ∅)
             ([ int {0} ]) (([ int (just 0) ]) , []) ∅
  ev-4 = ⟶>> (←old int var stack)
  ev-5 : tev [] ([ ~ {0} int ,, int ])
               (([ ptr none ,, int (just 0) ])
             , ([ ptr (just (heap fZ)) ]))
             (var fZ ← new (var (fin 1)) >> ∅)
             ([ ~ {0} int ,, int ])
              (([ ptr (just (heap fZ)) ,, int (just 0) ])
             , ([ int (just 0) ,, ptr (just (heap (fin 1))) ]))
             ∅
  ev-5 = ⟶>> (←new (new var var (copy int stack) heap) var stack)
  ev-6 : tev [] ([ int {0} ])
             (([ int (just 1) ]) , [])
             (push (~ int) (var fZ ← new (var (fin 1)) >> free (var fZ) >> ∅) >> ∅)
             ([ ~ {0} int ,, int ])
             (([ ptr none ,, int (just 1) ]) , [])
             (var fZ ← new (var (fin 1)) >> free (var fZ) >> skip pop ∅)
  ev-6 = ⟶>> push
  ev-7 : tev [] ([ ~ {0} int ,, int ])
             (([ ptr none ,, int (just 1) ]) , [])
             (var fZ ← new (var (fin 1)) >> free (var fZ) >> skip pop ∅)
             ([ ~ {0} int ,, int ])
             (([ ptr (just (heap fZ)) ,, int (just 1) ]) , ([ int (just 1) ]))
             (free (var fZ) >> skip pop ∅)
  ev-7 = ⟶>> (←new (new var var (copy int stack) heap) var stack)
  ev-8 : tev [] ([ ~ {0} int ,, int ])
             (([ ptr (just (heap fZ)) ,, int (just 1) ]) , ([ int (just 1) ]))
             (free (var fZ) >> skip pop ∅)
             ([ ~ {0} int ,, int ])
             (([ ptr none ,, int (just 1) ]) , [])
             (skip pop ∅)
  ev-8 = ⟶>> (free var stack stack re-Z (ptr none ∷ (int ∷ [])) [])
  ev-9 : tev [] ([ ~ {0} int ,, int ])
             (([ ptr none ,, int (just 1) ]) , [])
             (skip pop ∅)
             ([ int {0} ])
             (([ int (just 1) ]) , [])
             ∅
  ev-9 = skippop (int ∷ []) []
  ev-10 : tev [] ([ opt {0} int ,, int ])
              (([ rec ([ int (just 0) ,, int none ]) ,, int none ]) , [])
              (match (var fZ) (var (fin 2) ← use (var fZ) >> ∅) (var (fin 1) ← int 0 >> ∅) >> ∅)
              ([ opt {0} int ,, int ])
              (([ rec ([ int (just 0) ,, int none ]) ,, int none ]) , [])
              (var (fin 1) ← int 0 >> ∅)
  ev-10 = ⟶>> (none var stack)
  ev-11 : tev [] ([ opt {0} int ,, int ])
              (([ rec ([ int (just 0) ,, int none ]) ,, int none ]) , [])
              (var (fin 1) ← int 0 >> ∅)
              ([ opt {0} int ,, int ])
              (([ rec ([ int (just 0) ,, int none ]) ,, int (just 0) ]) , [])
              ∅
  ev-11 = ⟶>> (←old int var stack)
  ev-12 : tev [] ([ opt {0} int ,, int ])
              (([ rec ([ int (just 1) ,, int (just 10) ]) ,, int none ]) , [])
              (match (var fZ) (var (fin 2) ← use (var fZ) >> ∅) (var (fin 1) ← int 0 >> ∅) >> ∅)
              ([ int {1} ,, opt int ,, int ])
              (([ int (just 10) ,, rec ([ int (just 1) ,, int (just 10) ]) ,, int none ]) , [])
              (var (fin 2) ← use (var fZ) >> skip pop skip end ∅)
  ev-12 = ⟶>> (some var var (copy (opt int) stack))
  ev-13 : tev [] ([ int {1} ,, opt int ,, int ])
              (([ int (just 10) ,, rec ([ int (just 1) ,, int (just 10) ]) ,, int none ]) , [])
              (var (fin 2) ← use (var fZ) >> skip pop skip end ∅)
              ([ int {1} ,, opt int ,, int ])
              (([ int (just 10) ,, rec ([ int (just 1) ,, int (just 10) ]) ,, int (just 10) ]) , [])
              (skip pop skip end ∅)
  ev-13 = ⟶>> (←old (use var var (copy int stack)) var stack)
  ev-14 : tev [] ([ int {1} ,, opt int ,, int ])
              (([ int (just 10) ,, rec ([ int (just 1) ,, int (just 10) ]) ,, int (just 10) ]) , [])
              (skip pop skip end ∅)
              ([ opt {1} int ,, int ])
              (([ rec ([ int (just 1) ,, int (just 10) ]) ,, int (just 10) ]) , [])
              (skip end ∅)
  ev-14 = skippop (rec (int ∷ (int ∷ [])) ∷ (int ∷ [])) []
  ev-15 : tev [] ([ opt {1} int ,, int ])
              (([ rec ([ int (just 1) ,, int (just 10) ]) ,, int (just 10) ]) , [])
              (skip end ∅)
              ([ opt {0} int ,, int ])
              (([ rec ([ int (just 1) ,, int (just 10) ]) ,, int (just 10) ]) , [])
              ∅
  ev-15 = skipend ((opt int) ∷ (int ∷ []))
  ev-17 : tev ([ fn ( ~ int ) (free (var fZ) >> ∅) ])
              ([ ~ {10} int ])
              (([ ptr (just (heap fZ)) ]) , ([ int (just 1) ]))
              (call fZ (var fZ) >> ∅)
              ([ ~ {10} int ])
              (([ ptr (just (heap fZ)) ]) , ([ int (just 1) ]))
              (region (push (~ int) (var fZ ← use (var (fin 1)) >> free (var fZ) >> ∅) >> ∅) >> ∅)
  ev-17 = ⟶>> call
  ev-18 : tev ([ fn ( ~ int ) (free (var fZ) >> ∅) ])
              ([ ~ {10} int ])
              (([ ptr (just (heap fZ)) ]) , ([ int (just 1) ]))
              (region (push (~ int) (var fZ ← use (var (fin 1)) >> free (var fZ) >> ∅) >> ∅) >> ∅)
              ([ ~ {11} int ])
              (([ ptr (just (heap fZ)) ]) , ([ int (just 1) ]))
              (push (~ int) (var fZ ← use (var (fin 1)) >> free (var fZ) >> ∅) >> skip end ∅)
  ev-18 = ⟶>> region
  ev-19 : tev ([ fn ( ~ int ) (free (var fZ) >> ∅) ])
              ([ ~ {11} int ])
              (([ ptr (just (heap fZ)) ]) , ([ int (just 1) ]))
              (push (~ int) (var fZ ← use (var (fin 1)) >> free (var fZ) >> ∅) >> skip end ∅)
              ([ ~ int ,, ~ {11} int ])
              (([ ptr none ,, ptr (just (heap fZ)) ]) , ([ int (just 1) ]))
              (var fZ ← use (var (fin 1)) >> free (var fZ) >> skip pop skip end ∅)
  ev-19 = ⟶>> push
  ev-20 : tev ([ fn ( ~ int ) (free (var fZ) >> ∅) ])
              ([ ~ int ,, ~ {11} int ])
              (([ ptr none ,, ptr (just (heap fZ)) ]) , ([ int (just 1) ]))
              (var fZ ← use (var (fin 1)) >> free (var fZ) >> skip pop skip end ∅)
              ([ ~ int ,, ~ {11} int ])
              (([ ptr (just (heap fZ)) ,, ptr none ]) , ([ int (just 1) ]))
              (free (var fZ) >> skip pop skip end ∅)
  ev-20 = ⟶>> (←old (use var var (move ~Aff stack stack)) var stack)
  ev-21 : tev ([ fn ( ~ int ) (free (var fZ) >> ∅) ])
              ([ ~ int ,, ~ {11} int ])
              (([ ptr (just (heap fZ)) ,, ptr none ]) , ([ int (just 1) ]))
              (free (var fZ) >> skip pop skip end ∅)
              ([ ~ int ,, ~ {11} int ])
              (([ ptr none ,, ptr none ]) , [])
              (skip pop skip end ∅)
  ev-21 = ⟶>> (free var stack stack re-Z ((ptr none) ∷ ((ptr none) ∷ [])) [])
  ev-22 : tev ([ fn ( ~ int ) (free (var fZ) >> ∅) ])
              ([ ~ int ,, ~ {11} int ])
              (([ ptr none ,, ptr none ]) , [])
              (skip pop skip end ∅)
              ([ ~ {11} int ])
              (([ ptr none ]) , [])
              (skip end ∅)
  ev-22 = skippop (ptr none ∷ []) []
  ev-23 : tev ([ fn ( ~ int ) (free (var fZ) >> ∅) ])
              ([ ~ {11} int ])
              (([ ptr none ]) , [])
              (skip end ∅)
              ([ ~ {10} int ])
              (([ ptr none ]) , [])
              ∅
  ev-23 = skipend (~ int ∷ [])
  ev-24 : tev []
              ([ int {0} ])
              (([ int none ]) , [])
              (push int ∅ >> var fZ ← int 1 >> ∅)
              ([ int {0} ,, int ])
              (([ int none ,, int none ]) , [])
              (skip pop var fZ ← int 1 >> ∅)
  ev-24 = ⟶>> push
  ev-25 : tev []
              ([ int {0} ,, int ])
              (([ int none ,, int none ]) , [])
              (skip pop var fZ ← int 1 >> ∅)
              ([ int {0} ])
              (([ int none ]) , [])
              (var fZ ← int 1 >> ∅)
  ev-25 = skippop (int ∷ []) []
  ev-26 : tev []
              ([ int {0} ])
              (([ int none ]) , [])
              (var fZ ← int 1 >> ∅)
              ([ int {0} ])
              (([ int (just 1) ]) , [])
              ∅
  ev-26 = ⟶>> (←old int var stack)
