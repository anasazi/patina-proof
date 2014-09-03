open import Common
open import Life
open import Mut

module Type where

{-
Types are indexed by the lifetime relation (so the lifetimes of & are always well-formed).
-}
data Type (#ℓ : ℕ) : Set where
  int : Type #ℓ
  ~ : Type #ℓ → Type #ℓ
  & : Life #ℓ → Mut → Type #ℓ → Type #ℓ
  opt : Type #ℓ → Type #ℓ

private
  ~-inj : ∀ {#ℓ} {τ₁ τ₂ : Type #ℓ} → ~ τ₁ ≡ ~ τ₂ → τ₁ ≡ τ₂
  ~-inj refl = refl
  &-inj : ∀ {#ℓ μ} {ℓ₁ ℓ₂ : Life #ℓ} {τ₁ τ₂ : Type #ℓ} → & ℓ₁ μ τ₁ ≡ & ℓ₂ μ τ₂ → ℓ₁ ≡ ℓ₂ × τ₁ ≡ τ₂
  &-inj refl = refl , refl
  opt-inj : ∀ {#ℓ} {τ₁ τ₂ : Type #ℓ} → opt τ₁ ≡ opt τ₂ → τ₁ ≡ τ₂
  opt-inj refl = refl

  _=type=_ : ∀  {#ℓ} → (τ₁ τ₂ : Type #ℓ) → Dec (τ₁ ≡ τ₂)
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

EqType : ∀ {#ℓ} → Eq (Type #ℓ)
EqType = record { _==_ = _=type=_ }

-- A context is a vector of types (variables -> types)
Cxt : ℕ → ℕ → Set
Cxt #ℓ #x = Vec (Type #ℓ) #x

RCxt : ℕ → ℕ → ℕ → Set
RCxt #ℓ #x #a = Cxt #ℓ #x × Cxt #ℓ #a

-- upshift and downshift for the indicies of types
↑#ℓ-τ : ∀ {#ℓ} → ℕ → Type #ℓ → Type (S #ℓ)
↑#ℓ-τ c int = int
↑#ℓ-τ c (~ τ) = ~ (↑#ℓ-τ c τ)
↑#ℓ-τ c (& ℓ μ τ) = & (↑#ℓ-ℓ c ℓ) μ (↑#ℓ-τ c τ)
↑#ℓ-τ c (opt τ) = opt (↑#ℓ-τ c τ)

data ↓#ℓ-τ {#ℓ} : ℕ → Type (S #ℓ) → Type #ℓ → Set where
  int : ∀ {c} → ↓#ℓ-τ c int int
  ~ : ∀ {c τ τ′} → ↓#ℓ-τ c τ τ′ → ↓#ℓ-τ c (~ τ) (~ τ′)
  & : ∀ {c ℓ ℓ′ μ τ τ′} → ↓#ℓ-ℓ c ℓ ℓ′ → ↓#ℓ-τ c τ τ′ → ↓#ℓ-τ c (& ℓ μ τ) (& ℓ′ μ τ′)
  opt : ∀ {c τ τ′} → ↓#ℓ-τ c τ τ′ → ↓#ℓ-τ c (opt τ) (opt τ′)

-- The subtyping relationship
data _<:_ {#ℓ} : Type #ℓ → Type #ℓ → Set where
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
data _Copy {#ℓ} : Type #ℓ → Set where
  int : int Copy
  &imm : ∀ {ℓ τ} → & ℓ imm τ Copy
  opt : ∀ {τ} → τ Copy → opt τ Copy

-- Predicate for affine types
data _Affine {#ℓ} : Type #ℓ → Set where
  ~Aff : ∀ {τ} → ~ τ Affine
  &mut : ∀ {ℓ τ} → & ℓ mut τ Affine
  opt : ∀ {τ} → τ Affine → opt τ Affine

-- No type is both Copy and Affine
copy×affine≡⊥ : ∀ {#ℓ} → (τ : Type #ℓ) → ¬ (τ Copy × τ Affine)
copy×affine≡⊥ int (copy , ())
copy×affine≡⊥ (~ τ) (() , affine)
copy×affine≡⊥ (& ℓ imm τ) (copy , ())
copy×affine≡⊥ (& ℓ mut τ) (() , affine)
copy×affine≡⊥ (opt τ) (opt copy , opt affine) = copy×affine≡⊥ τ (copy , affine)

-- Every type is either Copy or Affine
copy+affine≡⊤ : ∀ {#ℓ} → (τ : Type #ℓ) → τ Copy + τ Affine
copy+affine≡⊤ int = inl int
copy+affine≡⊤ (~ τ) = inr ~Aff
copy+affine≡⊤ (& ℓ imm τ) = inl &imm
copy+affine≡⊤ (& ℓ mut τ) = inr &mut
copy+affine≡⊤ (opt τ) with copy+affine≡⊤ τ
copy+affine≡⊤ (opt τ) | inl copy = inl (opt copy)
copy+affine≡⊤ (opt τ) | inr affine = inr (opt affine)

-- Thus, Affine is a correct negation of Copy

-- Predicate for types which must drop heap memory
data _Drop {#ℓ} : Type #ℓ → Set where
  ~ : ∀ {τ} → ~ τ Drop
  opt : ∀ {τ} → τ Drop → opt τ Drop

-- Predicate for types which do not need to drop heap memory
data _¬Drop {#ℓ} : Type #ℓ → Set where
  int : int ¬Drop
  & : ∀ {ℓ μ τ} → & ℓ μ τ ¬Drop
  opt : ∀ {τ} → τ ¬Drop → opt τ ¬Drop

-- No type is both Copy and Drop
drop×copy≡⊥ : ∀ {#ℓ} → (τ : Type #ℓ) → ¬ (τ Drop × τ Copy)
drop×copy≡⊥ int (() , copy)
drop×copy≡⊥ (~ τ) (drop , ())
drop×copy≡⊥ (& ℓ μ τ) (() , copy)
drop×copy≡⊥ (opt τ) (opt drop , opt copy) = drop×copy≡⊥ τ (drop , copy)

-- No type is both Drop and ¬Drop
drop×¬drop≡⊥ : ∀ {#ℓ} → (τ : Type #ℓ) → ¬ (τ Drop × τ ¬Drop)
drop×¬drop≡⊥ int (() , ¬drop)
drop×¬drop≡⊥ (~ τ) (drop , ())
drop×¬drop≡⊥ (& ℓ μ τ) (() , ¬drop)
drop×¬drop≡⊥ (opt τ) (opt drop , opt ¬drop) = drop×¬drop≡⊥ τ (drop , ¬drop)

-- Every type is either Drop or ¬Drop
drop+¬drop≡⊤ : ∀ {#ℓ} → (τ : Type #ℓ) → τ Drop + τ ¬Drop
drop+¬drop≡⊤ int = inr int
drop+¬drop≡⊤ (~ τ) = inl ~
drop+¬drop≡⊤ (& ℓ μ τ) = inr &
drop+¬drop≡⊤ (opt τ) with drop+¬drop≡⊤ τ
drop+¬drop≡⊤ (opt τ) | inl drop = inl (opt drop)
drop+¬drop≡⊤ (opt τ) | inr ¬drop = inr (opt ¬drop)

-- Thus ¬Drop is a correct negation of Drop

-- nicer name for the above proof
_Drop? : ∀ {#ℓ} → (τ : Type #ℓ) → τ Drop + τ ¬Drop
_Drop? τ = drop+¬drop≡⊤ τ

data _bound-by_ {#ℓ} : Type #ℓ → Life #ℓ → Set where
  int : ∀ {ℓ} → int bound-by ℓ
  ~ : ∀ {τ ℓ} → τ bound-by ℓ → ~ τ bound-by ℓ
  & : ∀ {ℓ′ μ τ ℓ} → ℓ :<: ℓ′ → τ bound-by ℓ → & ℓ′ μ τ bound-by ℓ
  opt : ∀ {τ ℓ} → τ bound-by ℓ → opt τ bound-by ℓ
