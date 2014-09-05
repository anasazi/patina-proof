open import Common
open import Life
open import Mut

module Type where

{-
Types are indexed by the lifetime relation (so the lifetimes of & are always well-formed).
-}
data Type (#x : ℕ) : Set where
  int : Type #x
  ~ : Type #x → Type #x
  & : Life #x → Mut → Type #x → Type #x
  opt : Type #x → Type #x

private
  ~-inj : ∀ {#x} {τ₁ τ₂ : Type #x} → ~ τ₁ ≡ ~ τ₂ → τ₁ ≡ τ₂
  ~-inj refl = refl
  &-inj : ∀ {#x μ} {ℓ₁ ℓ₂ : Life #x} {τ₁ τ₂ : Type #x} → & ℓ₁ μ τ₁ ≡ & ℓ₂ μ τ₂ → ℓ₁ ≡ ℓ₂ × τ₁ ≡ τ₂
  &-inj refl = refl , refl
  opt-inj : ∀ {#x} {τ₁ τ₂ : Type #x} → opt τ₁ ≡ opt τ₂ → τ₁ ≡ τ₂
  opt-inj refl = refl

  _=type=_ : ∀  {#x} → (τ₁ τ₂ : Type #x) → Dec (τ₁ ≡ τ₂)
  int =type= int = yes refl
  int =type= ~ τ₂ = no (λ ())
  int =type= & ℓ₂ μ₂ τ₂ = no (λ ())
  int =type= opt τ₂ = no (λ ())
  ~ τ₁ =type= int = no (λ ())
  ~ τ₁ =type= ~ τ₂ with τ₁ =type= τ₂
  ~ τ₁ =type= ~ .τ₁ | yes refl = yes refl
  ~ τ₁ =type= ~ τ₂ | no neq = no (neq ∘ ~-inj)
  ~ τ₁ =type= & ℓ₂ μ₂ τ₂ = no (λ ())
  ~ τ₁ =type= opt τ₂ = no (λ ())
  & ℓ₁ μ₁ τ₁ =type= int = no (λ ())
  & ℓ₁ μ₁ τ₁ =type= ~ τ₂ = no (λ ())
  & ℓ₁ imm τ₁ =type= & ℓ₂ imm τ₂ with ℓ₁ == ℓ₂
  & ℓ₁ imm τ₁ =type= & .ℓ₁ imm τ₂ | yes refl with τ₁ =type= τ₂
  & ℓ₁ imm τ₁ =type= & .ℓ₁ imm .τ₁ | yes refl | yes refl = yes refl
  & ℓ₁ imm τ₁ =type= & .ℓ₁ imm τ₂ | yes refl | no neq = no (neq ∘ snd ∘ &-inj)
  & ℓ₁ imm τ₁ =type= & ℓ₂ imm τ₂ | no neq = no (neq ∘ fst ∘ &-inj)
  & ℓ₁ imm τ₁ =type= & ℓ₂ mut τ₂ = no (λ ())
  & ℓ₁ mut τ₁ =type= & ℓ₂ imm τ₂ = no (λ ())
  & ℓ₁ mut τ₁ =type= & ℓ₂ mut τ₂ with ℓ₁ == ℓ₂
  & ℓ₁ mut τ₁ =type= & .ℓ₁ mut τ₂ | yes refl with τ₁ =type= τ₂
  & ℓ₁ mut τ₁ =type= & .ℓ₁ mut .τ₁ | yes refl | yes refl = yes refl
  & ℓ₁ mut τ₁ =type= & .ℓ₁ mut τ₂ | yes refl | no neq = no (neq ∘ snd ∘ &-inj)
  & ℓ₁ mut τ₁ =type= & ℓ₂ mut τ₂ | no neq = no (neq ∘ fst ∘ &-inj)
  & ℓ₁ μ₁ τ₁ =type= opt τ₂ = no (λ ())
  opt τ₁ =type= int = no (λ ())
  opt τ₁ =type= ~ τ₂ = no (λ ())
  opt τ₁ =type= & ℓ₂ μ₂ τ₂ = no (λ ())
  opt τ₁ =type= opt τ₂ with τ₁ =type= τ₂
  opt τ₂ =type= opt .τ₂ | yes refl = yes refl
  opt τ₁ =type= opt τ₂ | no neq = no (neq ∘ opt-inj)

EqType : ∀ {#x} → Eq (Type #x)
EqType = record { _==_ = _=type=_ }

-- A context is a vector of types (variables -> types)
Cxt : ℕ → Set
Cxt #x = Vec (Type #x) #x

-- upshift and downshift for the indicies of types
↑#x-τ : ∀ {#x} → ℕ → Type #x → Type (S #x)
↑#x-τ c int = int
↑#x-τ c (~ τ) = ~ (↑#x-τ c τ)
↑#x-τ c (& ℓ μ τ) = & (↑#x-ℓ c ℓ) μ (↑#x-τ c τ)
↑#x-τ c (opt τ) = opt (↑#x-τ c τ)

data ↓#x-τ {#x} : ℕ → Type (S #x) → Type #x → Set where
  int : ∀ {c} → ↓#x-τ c int int
  ~ : ∀ {c τ τ′} → ↓#x-τ c τ τ′ → ↓#x-τ c (~ τ) (~ τ′)
  & : ∀ {c ℓ ℓ′ μ τ τ′} → ↓#x-ℓ c ℓ ℓ′ → ↓#x-τ c τ τ′ → ↓#x-τ c (& ℓ μ τ) (& ℓ′ μ τ′)
  opt : ∀ {c τ τ′} → ↓#x-τ c τ τ′ → ↓#x-τ c (opt τ) (opt τ′)

-- The subtyping relationship
data _<:_ {#x} : Type #x → Type #x → Set where
  int : int <: int
  ~ : ∀ {τ₁ τ₂}
    → τ₁ <: τ₂
    → ~ τ₁ <: ~ τ₂
  &imm : ∀ {ℓ₁ ℓ₂ τ₁ τ₂}
       → ℓ₂ :<: ℓ₁
       → τ₁ <: τ₂
       → & ℓ₁ imm τ₁ <: & ℓ₂ imm τ₂
  &mut : ∀ {ℓ₁ ℓ₂ τ}
       → ℓ₂ :<: ℓ₁
       → & ℓ₁ mut τ <: & ℓ₂ mut τ
  opt : ∀ {τ₁ τ₂}
      → τ₁ <: τ₂
      → opt τ₁ <: opt τ₂

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

-- Predicate for implicitly copyable types
data _Copy {#x} : Type #x → Set where
  int : int Copy
  &imm : ∀ {ℓ τ} → & ℓ imm τ Copy
  opt : ∀ {τ} → τ Copy → opt τ Copy

-- Predicate for affine types
data _Affine {#x} : Type #x → Set where
  ~Aff : ∀ {τ} → ~ τ Affine
  &mut : ∀ {ℓ τ} → & ℓ mut τ Affine
  opt : ∀ {τ} → τ Affine → opt τ Affine

-- No type is both Copy and Affine
copy×affine≡⊥ : ∀ {#x} → (τ : Type #x) → ¬ (τ Copy × τ Affine)
copy×affine≡⊥ int (copy , ())
copy×affine≡⊥ (~ τ) (() , affine)
copy×affine≡⊥ (& ℓ imm τ) (copy , ())
copy×affine≡⊥ (& ℓ mut τ) (() , affine)
copy×affine≡⊥ (opt τ) (opt copy , opt affine) = copy×affine≡⊥ τ (copy , affine)

-- Every type is either Copy or Affine
copy+affine≡⊤ : ∀ {#x} → (τ : Type #x) → τ Copy + τ Affine
copy+affine≡⊤ int = inl int
copy+affine≡⊤ (~ τ) = inr ~Aff
copy+affine≡⊤ (& ℓ imm τ) = inl &imm
copy+affine≡⊤ (& ℓ mut τ) = inr &mut
copy+affine≡⊤ (opt τ) with copy+affine≡⊤ τ
copy+affine≡⊤ (opt τ) | inl copy = inl (opt copy)
copy+affine≡⊤ (opt τ) | inr affine = inr (opt affine)

-- Thus, Affine is a correct negation of Copy

-- Predicate for types which must drop heap memory
data _Drop {#x} : Type #x → Set where
  ~ : ∀ {τ} → ~ τ Drop
  opt : ∀ {τ} → τ Drop → opt τ Drop

-- Predicate for types which do not need to drop heap memory
data _¬Drop {#x} : Type #x → Set where
  int : int ¬Drop
  & : ∀ {ℓ μ τ} → & ℓ μ τ ¬Drop
  opt : ∀ {τ} → τ ¬Drop → opt τ ¬Drop

-- No type is both Copy and Drop
drop×copy≡⊥ : ∀ {#x} → (τ : Type #x) → ¬ (τ Drop × τ Copy)
drop×copy≡⊥ int (() , copy)
drop×copy≡⊥ (~ τ) (drop , ())
drop×copy≡⊥ (& ℓ μ τ) (() , copy)
drop×copy≡⊥ (opt τ) (opt drop , opt copy) = drop×copy≡⊥ τ (drop , copy)

-- No type is both Drop and ¬Drop
drop×¬drop≡⊥ : ∀ {#x} → (τ : Type #x) → ¬ (τ Drop × τ ¬Drop)
drop×¬drop≡⊥ int (() , ¬drop)
drop×¬drop≡⊥ (~ τ) (drop , ())
drop×¬drop≡⊥ (& ℓ μ τ) (() , ¬drop)
drop×¬drop≡⊥ (opt τ) (opt drop , opt ¬drop) = drop×¬drop≡⊥ τ (drop , ¬drop)

-- Every type is either Drop or ¬Drop
drop+¬drop≡⊤ : ∀ {#x} → (τ : Type #x) → τ Drop + τ ¬Drop
drop+¬drop≡⊤ int = inr int
drop+¬drop≡⊤ (~ τ) = inl ~
drop+¬drop≡⊤ (& ℓ μ τ) = inr &
drop+¬drop≡⊤ (opt τ) with drop+¬drop≡⊤ τ
drop+¬drop≡⊤ (opt τ) | inl drop = inl (opt drop)
drop+¬drop≡⊤ (opt τ) | inr ¬drop = inr (opt ¬drop)

-- Thus ¬Drop is a correct negation of Drop

-- nicer name for the above proof
_Drop? : ∀ {#x} → (τ : Type #x) → τ Drop + τ ¬Drop
_Drop? τ = drop+¬drop≡⊤ τ

data _bound-by_ {#x} : Type #x → Life #x → Set where
  int : ∀ {ℓ} → int bound-by ℓ
  ~ : ∀ {τ ℓ} → τ bound-by ℓ → ~ τ bound-by ℓ
  & : ∀ {ℓ′ μ τ ℓ} → ℓ :<: ℓ′ → τ bound-by ℓ → & ℓ′ μ τ bound-by ℓ
  opt : ∀ {τ ℓ} → τ bound-by ℓ → opt τ bound-by ℓ
