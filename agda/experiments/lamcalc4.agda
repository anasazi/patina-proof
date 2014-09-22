module lamcalc4 where

infix 4 _≡_
data _≡_ {α} {A : Set α} (x : A) : A → Set α where
  refl : x ≡ x

{-# BUILTIN EQUALITY _≡_ #-}
{-# BUILTIN REFL refl #-}

data Type : Set where
  unit : Type
  _⇒_ : Type → Type → Type

record ⊤ : Set where
  constructor tt

  -- not strictly positive
  {-
data Term : Type → Set where
  unit : Term unit
  var : ∀ {τ} → Term τ
  abs : ∀ {τ₁ τ₂} → ({!Term τ₁!} → Term τ₂) → Term (τ₁ ⇒ τ₂)
  app : ∀ {τ₁ τ₂} → Term (τ₁ ⇒ τ₂) → Term τ₁ → Term τ₂
  -}

-- PHOAS version
data Term (Var : Type → Set) : Type → Set where
  unit : Term Var unit
  var : ∀ {τ} → Var τ → Term Var τ
  abs : ∀ {τ₁ τ₂} → (Var τ₁ → Term Var τ₂) → Term Var (τ₁ ⇒ τ₂)
  app : ∀ {τ₁ τ₂} → Term Var (τ₁ ⇒ τ₂) → Term Var τ₁ → Term Var τ₂

data Value {Var} : ∀ {τ} → Term Var τ → Set where
  unit : Value unit
  abs : ∀ {τ₁ τ₂ t} → Value (abs {_} {τ₁} {τ₂} t)

type-denote : Type → Set
type-denote unit = ⊤
type-denote (τ₁ ⇒ τ₂) = type-denote τ₁ → type-denote τ₂

value-denote : ∀ {Var τ} (v : Term (Term Var) τ) → Value v → Term (Term Var) τ
value-denote unit unit = unit
value-denote (abs t) abs = abs t

Closed : Type → Set1
Closed τ = ∀ Var → Term Var τ

1Open : Type → Type → Set₁
1Open τ₁ τ₂ = ∀ Var → Var τ₁ → Term Var τ₂

squash : ∀ {Var τ} → Term (Term Var) τ → Term Var τ
squash unit = unit
squash (var x) = x
squash (abs t) = abs (λ x → squash (t (var x)))
squash (app t₁ t₂) = app (squash t₁) (squash t₂)

Subst : ∀ {τ₁ τ₂} → 1Open τ₁ τ₂ → Closed τ₁ → Closed τ₂
Subst E E′ = λ Var → squash (E (Term Var) (E′ Var))

data _⟶_ {τ} : ∀ {Var} → Term Var τ → Term Var τ → Set1 where
  app-1 : ∀ {Var τ′ t₁ t₁′} {t₂ : Term Var τ′} → t₁ ⟶ t₁′ → app t₁ t₂ ⟶ app t₁′ t₂
  app-2 : ∀ {Var τ′ v} {t t′ : Term Var τ′} → Value v → t ⟶ t′ → app v t ⟶ app v t′
  app-abs : ∀ {Var τ′ t} {v : Term (Term Var) τ′} (pf : Value v)
          → app (abs t) v ⟶ t (squash (value-denote v pf))

record IsAbs {Var τ₁ τ₂} (v : Term Var (τ₁ ⇒ τ₂)) : Set where
  constructor is-abs
  field
    body : Var τ₁ → Term Var τ₂
    pf : v ≡ abs body
    

canonical-2 : ∀ {Var τ₁ τ₂} (v : Term Var (τ₁ ⇒ τ₂)) → Value v → IsAbs v
canonical-2 (var _) ()
canonical-2 (abs t) abs = is-abs t refl
canonical-2 (app _ _) ()

data Progress {τ} : ∀ {Var} → Term Var τ → Set1 where
  value : ∀ {Var} {t : Term Var τ} → Value t → Progress t
  steps : ∀ {Var t} → (t′ : Term Var τ) → t ⟶ t′ → Progress t

progress : ∀ {Var τ} (t : Term Var τ) → Progress t
progress unit = value unit
progress (var x) = {!!}
progress (abs t) = value abs
progress (app t₁ t₂) with progress t₁
progress (app t₁ t₂) | value v₁ with progress t₂
progress (app t₁ t₂) | value v₁ | value v₂ with canonical-2 t₁ v₁
progress (app .(abs t₁) t₂) | value v₁ | value v₂ | is-abs t₁ refl = {!!}
progress (app t₁ t₂) | value v₁ | steps t₂′ t₂⟶t₂′ = steps (app t₁ t₂′) (app-2 v₁ t₂⟶t₂′)
progress (app t₁ t₂) | steps t₁′ t₁⟶t₁′ = steps (app t₁′ t₂) (app-1 t₁⟶t₁′)

{-
data _⟶_ {Var τ} : Term (Term Var) τ → Term (Term Var) τ → Set where
  app-1 : ∀ {τ′ t₁ t₁′} {t₂ : Term _ τ′} → t₁ ⟶ t₁′ → app t₁ t₂ ⟶ app t₁′ t₂
  app-2 : ∀ {τ′ v} {t t′ : Term _ τ′} → Value v → t ⟶ t′ → app v t ⟶ app v t′
  app-abs : ∀ {τ′ t} {v : Term _ τ′} (pf : Value v) → app (abs t) v ⟶ t (squash (value-denote v pf))

data Progress {Var τ} : Term Var τ → Set where
  value : ∀ {t} → Value t → Progress t
  steps : ∀ {t} → (t′ : {!!}) → t ⟶ t′ → Progress {!t!}

progress : ∀ {Var τ} (t : Term Var τ) → {!!}
progress = {!!}
-}

{-
data _⟶_ {Var τ} : Term Var τ → Term Var τ → Set where
  app-1 : ∀ {τ′ t₁ t₁′} {t₂ : Term Var τ′} → t₁ ⟶ t₁′ → app t₁ t₂ ⟶ app t₁′ t₂
  app-2 : ∀ {τ′ v} {t t′ : Term Var τ′} → Value v → t ⟶ t′ → app v t ⟶ app v t′
  app-abs : ∀ {τ′ t} {v : Term Var τ′} → (pf : Value v) → app (abs t) v ⟶ t {!value-denote !}
  -}

term-denote : ∀ {τ} → Term type-denote τ → type-denote τ
term-denote unit = tt
term-denote (var x) = x
term-denote (abs t) = λ x → term-denote (t x)
term-denote (app t₁ t₂) = (term-denote t₁) (term-denote t₂)

TermDenote : ∀ {τ} → Closed τ → type-denote τ
TermDenote E = term-denote (E type-denote)

-- data Term : Set → Set1 where
--   unit : Term ⊤
--   var : ∀ {τ} → Term τ
--   abs : ∀ {τ₁ τ₂} → (τ₁ → Term τ₂) → Term (τ₁ → τ₂)
--   app : ∀ {τ₁ τ₂} → Term (τ₁ → τ₂) → Term τ₁ → Term τ₂

--   {-
-- data Value : ∀ {τ} → Term τ → τ → Set1 where
--   unit : Value unit tt
--   abs : ∀ {τ₁ τ₂} {t : τ₁ → Term τ₂} → Value (abs t) {!!}
--   -}

-- data Value : ∀ {τ} → Term τ → Set1 where
--   v-unit : Value unit
--   v-abs : ∀ {τ₁ τ₂} {t : τ₁ → Term τ₂} → Value (abs t)
--   --abs : ∀ {τ₁ τ₂} {t : τ₁ → Term τ₂} → Value ?

--   {-
-- embed : ∀ {τ} (v : Term τ) → Value v → τ
-- embed unit v-unit = tt
-- embed (abs t) v-abs = {!!}
-- -}

-- data _⟶_ : ∀ {τ} → Term τ → Term τ → Set1 where
--   app-1 : ∀ {τ₁ τ₂} {t₁ t₁′ : Term (τ₁ → τ₂)} {t₂} → t₁ ⟶ t₁′ → app t₁ t₂ ⟶ app t₁′ t₂
--   app-2 : ∀ {τ₁ τ₂} {v : Term (τ₁ → τ₂)} {t t′} → Value v → t ⟶ t′ → app v t ⟶ app v t′
--   app-abs : ∀ {τ₁ τ₂} {t : τ₁ → Term τ₂} {v} → Value v → app (abs t) v ⟶ {!!}
