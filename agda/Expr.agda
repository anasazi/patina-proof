open import Common
open import Life
open import Mut
open import Type
open import Path
open import Route
open import Layout
open import Shape
open import Loan

module Expr where

data Expr (#x : ℕ) : Set where
  int : ℕ → Expr #x
  add : Path #x → Path #x → Expr #x
  use : Path #x → Expr #x
  new : Path #x → Expr #x
  & : Life #x → Mut → Path #x → Expr #x
  some : Path #x → Expr #x
  none : Type #x → Expr #x

↑#x-e : ∀ {#x} → ℕ → Expr #x → Expr (S #x)
↑#x-e c (int n) = int n
↑#x-e c (add p₁ p₂) = add (↑#x-p c p₁) (↑#x-p c p₂)
↑#x-e c (use p) = use (↑#x-p c p)
↑#x-e c (new p) = new (↑#x-p c p)
↑#x-e c (& ℓ μ p) = & (↑#x-ℓ c ℓ) μ (↑#x-p c p)
↑#x-e c (some p) = some (↑#x-p c p)
↑#x-e c (none τ) = none (↑#x-τ c τ)

data _,_⊢_∶_,_ {#x} (Γ : Cxt #x) : State #x → Expr #x
               → Type #x → State #x → Set where
  int : ∀ {n Δ} → Γ , Δ ⊢ int n ∶ int , Δ
  add : ∀ {p₁ p₂ Δ} → Γ , Δ ⊢ p₁ ∶ int ⇒ Δ → Γ , Δ ⊢ p₂ ∶ int ⇒ Δ → Γ , Δ ⊢ add p₁ p₂ ∶ int , Δ
  use : ∀ {Δᵢ p τ Δₒ} → Γ , Δᵢ ⊢ p ∶ τ ⇒ Δₒ → Γ , Δᵢ ⊢ use p ∶ τ , Δₒ
  new : ∀ {Δᵢ p τ Δₒ} → Γ , Δᵢ ⊢ p ∶ τ ⇒ Δₒ → Γ , Δᵢ ⊢ new p ∶ ~ τ , Δₒ
  &imm : ∀ {Δᵢ ℓ p τ Δₒ}
       → Γ ⊢ p ∶ τ path
       → Γ , Δᵢ ⊢ p readable
       → Γ ⊢ p freezable-for ℓ
       → Γ ⊢ p outlives ℓ
       → Γ , Δᵢ ⊢ imm borrow p for ℓ ⇒ Δₒ
       → Γ , Δᵢ ⊢ & ℓ imm p ∶ & ℓ imm τ , Δₒ
  &mut : ∀ {Δᵢ ℓ p τ Δₒ}
       → Γ ⊢ p ∶ τ path
       → Γ , Δᵢ ⊢ p writeable
       → Γ ⊢ p unique-for ℓ
       → Γ ⊢ p outlives ℓ
       → Γ , Δᵢ ⊢ mut borrow p for ℓ ⇒ Δₒ
       → Γ , Δᵢ ⊢ & ℓ mut p ∶ & ℓ mut τ , Δₒ
  some : ∀ {Δᵢ p τ Δₒ} → Γ , Δᵢ ⊢ p ∶ τ ⇒ Δₒ → Γ , Δᵢ ⊢ some p ∶ opt τ , Δₒ
  none : ∀ {Δ τ} → {- TODO wellformed check on τ -} Γ , Δ ⊢ none τ ∶ opt τ , Δ

data _,_⊢_⟶_ {#x #a} (Γ : Cxt #x) (M : Mem #x #a) : Expr #x
              → (Layout #x #a × Mem #x #a) + (Layout #x (S #a) × Mem #x (S #a)) → Set where
  int : ∀ {n} → Γ , M ⊢ int n ⟶ inl (int (just n) , M)
  add : ∀ {p₁ p₂ r₁ r₂ n₁ n₂ n}
      → M ⊢ p₁ ⟶ r₁
      → M ⊢ p₂ ⟶ r₂
      → M ⊢ r₁ ⇒ int (just n₁)
      → M ⊢ r₂ ⇒ int (just n₂)
      → n ≡ plus n₁ n₂
      → Γ , M ⊢ add p₁ p₂ ⟶ inl (int (just n) , M)
  use : ∀ {p τ r l M′}
      → Γ ⊢ p ∶ τ path
      → M ⊢ p ⟶ r
      → M ⊢ r ∶ τ ⇒ l , M′
      → Γ , M ⊢ use p ⟶ inl (l , M′)
  new : ∀ {p τ r l M′ M′′}
      → Γ ⊢ p ∶ τ path
      → M ⊢ p ⟶ r
      → M ⊢ r ∶ τ ⇒ l , M′
      → (map (↑#a-l 0) *** map (↑#a-l 0)) (second (_∷_ l) M′) ⊢ heap fZ ≔ ↑#a-l 0 l ⇒ M′′
      → Γ , M ⊢ new p ⟶ inr ((ptr (just (heap fZ))) , M′′)
  & : ∀ {ℓ μ p τ r}
    → Γ ⊢ p ∶ τ path
    → M ⊢ p ⟶ r
    → Γ , M ⊢ & ℓ μ p ⟶ inl (ptr (just r) , M)
  some : ∀ {p τ r l M′}
       → Γ ⊢ p ∶ τ path
       → M ⊢ p ⟶ r
       → M ⊢ r ∶ τ ⇒ l , M′
       → Γ , M ⊢ some p ⟶ inl (rec ([ int (just 1) ,, l ]) , M′)
  none : ∀ {τ l}
       → void-layout τ l
       → Γ , M ⊢ none τ ⟶ inl (rec ([ int (just 0) ,, l ]) , M)

{-
expr-progress : ∀ {#x #ℓ #a e τ} {Γ : Context #ℓ #x} {Δ Δ′ : State #ℓ #x} {M : Mem #x #a}
              → Γ ⊢ Δ state
              → Δ ⊢ M mem-state
              → NoGarbage M
              → Γ , Δ ⊢ e ∶ τ , Δ′
              → Σ[ l×M′ ∈ (Layout #x #a × Mem #x #a) + (Layout #x (S #a) × Mem #x (S #a)) ]
                Γ , M ⊢ e ⟶ l×M′
expr-progress Γ⊢Δ Δ⊢M NG int = _ , int
expr-progress Γ⊢Δ Δ⊢M NG (add p₁∶int⇒Δ p₂∶int⇒Δ)
  with path-progress (use-to-path p₁∶int⇒Δ) | path-progress (use-to-path p₂∶int⇒Δ)
... | r₁ , p₁⟶r₁ | r₂ , p₂⟶r₂ = {!!}
                                 , (add p₁⟶r₁
                                        p₂⟶r₂
                                        {!!}
                                        {!!}
                                        refl)
expr-progress Γ⊢Δ Δ⊢M NG (use p∶τ) = {!!}
expr-progress Γ⊢Δ Δ⊢M NG (new p∶τ) = {!!}
expr-progress Γ⊢Δ Δ⊢M NG (some p∶τ⇒Δ′) with path-progress (use-to-path p∶τ⇒Δ′)
... | r , p⟶r = {!!} , (some (use-to-path p∶τ⇒Δ′) p⟶r {!!})
expr-progress Γ⊢Δ Δ⊢M NG none = _ , none
-}
      
module TestEval where
  rvok-1 : ([ int {1} ]) , [ int (just (bank-def _)) ] ⊢ int 1 ∶ int , ([ int (just (bank-def _)) ])
  rvok-1 = int
  rvok-2 : ([ int ,, int ])
         , [ int (just (bank-def _)) ,, int (just (bank-def _)) ]
         ⊢ add (var (fin 0)) (var (fin 1)) ∶ int
         , ([ int (just (bank-def _)) ,, int (just (bank-def _)) ])
  rvok-2 = add (copy var int
                     (can-read (deep var int)
                               (read-unres var (int (readable (free ∷ (free ∷ [])) free)))
                               (var (int (nomuts (free ∷ free ∷ []) free)))))
               (copy var int
                     (can-read (deep var int)
                               (read-unres var (int (readable (free ∷ (free ∷ [])) free)))
                               (var (int (nomuts (free ∷ free ∷ []) free)))))
  rvok-3 : ¬ (([ int ,, int ])
              , [ int none ,, int (just (bank-def _)) ]
              ⊢ add (var (fin 0)) (var (fin 1)) ∶ int
              , ([ int none ,, int (just (bank-def _)) ]))
  rvok-3 (add (copy _ _ (can-read (deep var ()) _ _)) _)
  rvok-3 (add (move _ () _ _) _)
  rvok-4 : ([ ~ int ])
         , [ ~ (just ((bank-def _) , (int (just (bank-def _))))) ]
         ⊢ use (var fZ)
         ∶ ~ int
         , ([ ~ none ])
  rvok-4 = use (move var ~Aff
                     (can-move var
                               (can-write (deep var (~ int))
                                          (write-unres var (~ (unborrowed (free ∷ []) free)
                                                           (int (unborrowed (free ∷ []) free))))
                                          (var (~ (unborrowed (free ∷ []) free)))))
                     (void var var))
  rvok-5 : ([ int ])
         , [ int (just (bank-def _)) ]
         ⊢ new (var fZ) ∶ ~ int
         , ([ int (just (bank-def _)) ])
  rvok-5 = new (copy var int (can-read (deep var int)
                                       (read-unres var (int (readable (free ∷ []) free)))
                                       (var (int (nomuts (free ∷ []) free)))))

  rveval-1 : [] , [] , [] ⊢ int 0 ⟶ inl (int (just 0) , ([] , []))
  rveval-1 = int
  rveval-2 : ([ int ,, int ])
           , ([ int (just 1) ,, int (just 2) ]) , []
           ⊢ add (var (fin 0)) (var (fin 1)) ⟶ inl (int (just 3)
           , (([ int (just 1) ,, int (just 2) ]) , []))
  rveval-2 = add var var stack stack refl
  rveval-3 : ¬ (([ int ,, int ])
                , ([ int none ,, int (just 2) ]) , []
                ⊢ add (var (fin 0)) (var (fin 1)) ⟶ inl (int (just 3)
                , (([ int none ,, int (just 2) ]) , [])))
  rveval-3 (add var p₂⟶r₂ () r₂⇒n₂ n₁+n₂)
  rveval-4 : ([ int ]) , ([ int (just 10) ]) , []
           ⊢ some (var (fin 0)) ⟶ inl (rec ([ int (just 1) ,, int (just 10) ])
           , (([ int (just 10) ]) , []))
  rveval-4 = some var var (copy int stack)
  rveval-5 : [] , [] , [] ⊢ none int ⟶ inl (rec ([ int (just 0) ,, int none ]) , ([] , []))
  rveval-5 = none int
  rveval-6 : ([ ~ int ]) , ([ ptr (just (heap fZ)) ]) , ([ int (just 1) ])
           ⊢ use (var fZ) ⟶ inl (ptr (just (heap fZ)) , (([ ptr none ]) , ([ int (just 1) ])))
  rveval-6 = use var var (move ~Aff stack ~⊥ stack)
  rveval-7 : ([ ~ int ]) , ([ ptr (just (heap fZ)) ]) , ([ int (just 1) ,, int (just 2) ])
           ⊢ use (var fZ) ⟶ inl (ptr (just (heap fZ))
           , (([ ptr none ]) , ([ int (just 1) ,, int (just 2) ])))
  rveval-7 = use var var (move ~Aff stack ~⊥ stack)
  rveval-8 : ([ int ]) , ([ int (just 10) ]) , []
           ⊢ new (var fZ) ⟶ inr (ptr (just (heap fZ)) , (([ int (just 10) ]) , ([ int (just 10) ])))
  rveval-8 = new var var (copy int stack) heap
