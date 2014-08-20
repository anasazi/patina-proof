open import Common
open import Life
open import Mut

module Type where

data Type (#ℓ : ℕ) : Set where
  int : Type #ℓ
  ~ : Type #ℓ → Type #ℓ
  & : Life #ℓ → Mut → Type #ℓ → Type #ℓ
  opt : Type #ℓ → Type #ℓ

  {-
_=type=_ : (τ₁ τ₂ : Type) → Dec (τ₁ ≡ τ₂)
int =type= int = yes refl

EqType : Eq Type
EqType = record { _==_ = _=type=_ }
-}

↑-#ℓ-t : ∀ {#ℓ} → (d : ℕ) → ℕ → Type #ℓ → Type (plus d #ℓ)
↑-#ℓ-t d c int = int
↑-#ℓ-t d c (~ τ) = ~ (↑-#ℓ-t d c τ)
--↑-#ℓ-t d c (& (var Ł) μ τ) = & (var Ł) μ (↑-#ℓ-t d c τ)
↑-#ℓ-t d c (& static μ τ) = & static μ (↑-#ℓ-t d c τ)
↑-#ℓ-t d c (& (val ℓ) μ τ) with asℕ ℓ <? c
↑-#ℓ-t d c (& (val ℓ) μ τ) | yes ℓ<c = & (val (expand′ d ℓ)) μ (↑-#ℓ-t d c τ)
↑-#ℓ-t d c (& (val ℓ) μ τ) | no  ℓ≥c = & (val (raise d ℓ)) μ (↑-#ℓ-t d c τ)
↑-#ℓ-t d c (opt τ) = opt (↑-#ℓ-t d c τ)

↑-#ℓ-t′ : ∀ {#ℓ} → (d : ℕ) → ℕ → Type #ℓ → Type (plus #ℓ d)
↑-#ℓ-t′ {#ℓ} d c τ rewrite plus-comm #ℓ d = ↑-#ℓ-t d c τ

{-
↑-#Ł-t : ∀ {#ℓ #Ł} → (d : ℕ) → ℕ → Type #ℓ #Ł → Type #ℓ (plus d #Ł)
↑-#Ł-t d c int = int
↑-#Ł-t d c (~ τ) = ~ (↑-#Ł-t d c τ)
↑-#Ł-t d c (& (var Ł) μ τ) with asℕ Ł <? c
↑-#Ł-t d c (& (var Ł) μ τ) | yes Ł<c = & (var (expand′ d Ł)) μ (↑-#Ł-t d c τ)
↑-#Ł-t d c (& (var Ł) μ τ) | no  Ł≥c = & (var (raise d Ł)) μ (↑-#Ł-t d c τ)
↑-#Ł-t d c (& static μ τ) = & static μ (↑-#Ł-t d c τ)
↑-#Ł-t d c (& (val Ł) μ τ) = & (val Ł) μ (↑-#Ł-t d c τ)
↑-#Ł-t d c (opt τ) = opt (↑-#Ł-t d c τ)

↑-#Ł-t′ : ∀ {#Ł #ℓ} → (d : ℕ) → ℕ → Type #ℓ #Ł → Type #ℓ (plus #Ł d)
↑-#Ł-t′ {#Ł} d c τ rewrite plus-comm #Ł d = ↑-#Ł-t d c τ
-}

data ↓1-#ℓ-t {#ℓ} : ℕ → Type (S #ℓ) → Type #ℓ → Set where
  int : ∀ {c} → ↓1-#ℓ-t c int int
  ~ : ∀ {c τ τ′} → ↓1-#ℓ-t c τ τ′ → ↓1-#ℓ-t c (~ τ) (~ τ′)
  & : ∀ {c ℓ ℓ′ μ τ τ′}
    → ↓c c ℓ ℓ′
    → ↓1-#ℓ-t c τ τ′
    → ↓1-#ℓ-t c (& (val ℓ) μ τ) (& (val ℓ′) μ τ′)
  opt : ∀ {c τ τ′} → ↓1-#ℓ-t c τ τ′ → ↓1-#ℓ-t c (opt τ) (opt τ′)

data ↓1-#ℓ-ts {#ℓ} : ∀ {n} → ℕ → Vec (Type (S #ℓ)) n → Vec (Type #ℓ) n → Set where
  [] : ∀ {c} → ↓1-#ℓ-ts c [] []
  _∷_ : ∀ {n c τ τ′ τs} {τs′ : Vec (Type #ℓ) n}
      → ↓1-#ℓ-t c τ τ′
      → ↓1-#ℓ-ts c τs τs′
      → ↓1-#ℓ-ts c (τ ∷ τs) (τ′ ∷ τs′) 

test-↓1-#ℓ-t-1 : ↓1-#ℓ-t {5} 3 int int
test-↓1-#ℓ-t-1 = int
test-↓1-#ℓ-t-2 : ↓1-#ℓ-t {5} 3 (& (val (fin 0)) imm int) (& (val (fin 0)) imm int)
test-↓1-#ℓ-t-2 = & Z int
test-↓1-#ℓ-t-3 : ↓1-#ℓ-t {5} 3 (& (val (fin 3)) imm int) (& (val (fin 2)) imm int)
test-↓1-#ℓ-t-3 = & (S≥ (s<s (s<s (s<s z<s)))) int

data _<:_ {#ℓ} : Type #ℓ → Type #ℓ → Set where
  int : int <: int
  ~ : ∀ {τ₁ τ₂} → τ₁ <: τ₂ → ~ τ₁ <: ~ τ₂
  &imm : ∀ {ℓ₁ ℓ₂ τ₁ τ₂} → #ℓ ∣ ℓ₂ <: ℓ₁ → τ₁ <: τ₂ → & ℓ₁ imm τ₁ <: & ℓ₂ imm τ₂
  &mut : ∀ {ℓ₁ ℓ₂ τ} → #ℓ ∣ ℓ₂ <: ℓ₁ → & ℓ₁ mut τ <: & ℓ₂ mut τ
  opt : ∀ {τ₁ τ₂} → τ₁ <: τ₂ → opt τ₁ <: opt τ₂

test-subtype-1 : int {0} <: int
test-subtype-1 = int
test-subtype-2 : ¬ (& {3} (val (fin 1)) mut int <: & (val (fin 2)) mut int)
test-subtype-2 (&mut (val-val (s<s (s<s ()))))
test-subtype-3 : & {1} static mut int <: & (val fZ) mut int
test-subtype-3 = &mut val-static
test-subtype-4 : & {3} (val (fin 2)) mut int <: & (val (fin 1)) mut int
test-subtype-4 = &mut (val-val (s<s z<s))
test-subtype-5 : opt (& {3} (val (fin 2)) mut int) <: opt (& (val (fin 1)) mut int)
test-subtype-5 = opt (&mut (val-val (s<s z<s)))
test-subtype-6 : ~ (& {3} (val (fin 2)) mut int) <: ~ (& (val (fin 1)) mut int)
test-subtype-6 = ~ (&mut (val-val (s<s z<s)))

  {-
data sizeof : Type → ℕ → Set where
  int : sizeof int 1
  opt : ∀ {τ n} → sizeof τ n → sizeof (opt τ) (S n)
  -}

data _Copy {#ℓ} : Type #ℓ → Set where
  int : int Copy
  &imm : ∀ {ℓ τ} → & ℓ imm τ Copy
  opt : ∀ {τ} → τ Copy → opt τ Copy

data _Affine {#ℓ} : Type #ℓ → Set where
  ~Aff : ∀ {τ} → ~ τ Affine
  &mut : ∀ {ℓ τ} → & ℓ mut τ Affine
  opt : ∀ {τ} → τ Affine → opt τ Affine

copy×affine≡⊥ : ∀ {#ℓ} → (τ : Type #ℓ) → ¬ (τ Copy × τ Affine)
copy×affine≡⊥ int (copy , ())
copy×affine≡⊥ (~ τ) (() , affine)
copy×affine≡⊥ (& ℓ imm τ) (copy , ())
copy×affine≡⊥ (& ℓ mut τ) (() , affine)
copy×affine≡⊥ (opt τ) (opt copy , opt affine) = copy×affine≡⊥ τ (copy , affine)

copy+affine≡⊤ : ∀ {#ℓ} → (τ : Type #ℓ) → τ Copy + τ Affine
copy+affine≡⊤ int = inl int
copy+affine≡⊤ (~ τ) = inr ~Aff
copy+affine≡⊤ (& ℓ imm τ) = inl &imm
copy+affine≡⊤ (& ℓ mut τ) = inr &mut
copy+affine≡⊤ (opt τ) with copy+affine≡⊤ τ
copy+affine≡⊤ (opt τ) | inl copy = inl (opt copy)
copy+affine≡⊤ (opt τ) | inr affine = inr (opt affine)

data _Drop {#ℓ} : Type #ℓ → Set where
  ~ : ∀ {τ} → ~ τ Drop
  opt : ∀ {τ} → τ Drop → opt τ Drop

data _¬Drop {#ℓ} : Type #ℓ → Set where
  int : int ¬Drop
  & : ∀ {ℓ μ τ} → & ℓ μ τ ¬Drop
  opt : ∀ {τ} → τ ¬Drop → opt τ ¬Drop

drop×copy≡⊥ : ∀ {#ℓ} → (τ : Type #ℓ) → ¬ (τ Drop × τ Copy)
drop×copy≡⊥ int (() , copy)
drop×copy≡⊥ (~ τ) (drop , ())
drop×copy≡⊥ (& ℓ μ τ) (() , copy)
drop×copy≡⊥ (opt τ) (opt drop , opt copy) = drop×copy≡⊥ τ (drop , copy)

drop×¬drop≡⊥ : ∀ {#ℓ} → (τ : Type #ℓ) → ¬ (τ Drop × τ ¬Drop)
drop×¬drop≡⊥ int (() , ¬drop)
drop×¬drop≡⊥ (~ τ) (drop , ())
drop×¬drop≡⊥ (& ℓ μ τ) (() , ¬drop)
drop×¬drop≡⊥ (opt τ) (opt drop , opt ¬drop) = drop×¬drop≡⊥ τ (drop , ¬drop)

drop+¬drop≡⊤ : ∀ {#ℓ} → (τ : Type #ℓ) → τ Drop + τ ¬Drop
drop+¬drop≡⊤ int = inr int
drop+¬drop≡⊤ (~ τ) = inl ~
drop+¬drop≡⊤ (& ℓ μ τ) = inr &
drop+¬drop≡⊤ (opt τ) with drop+¬drop≡⊤ τ
drop+¬drop≡⊤ (opt τ) | inl drop = inl (opt drop)
drop+¬drop≡⊤ (opt τ) | inr ¬drop = inr (opt ¬drop)

_Drop? : ∀ {#ℓ} → (τ : Type #ℓ) → τ Drop + τ ¬Drop
_Drop? τ = drop+¬drop≡⊤ τ
