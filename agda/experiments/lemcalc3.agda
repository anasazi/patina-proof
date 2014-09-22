module experiments.lemcalc3 where

data ⊥ : Set where

¬_ : ∀ {a} → Set a → Set a
¬ x = x → ⊥

data Dec {a} (P : Set a) : Set a where
  yes : P → Dec P
  no  : ¬ P → Dec P

data Type : Set where
  Unit : Type
  _⇒_ : Type → Type → Type

data Cxt : Set where
  ∅ : Cxt
  _,_ : Cxt → Type → Cxt

data _∈_ : Type → Cxt → Set where
  Z : ∀ {τ Γ} → τ ∈ (Γ , τ)
  S : ∀ {τ Γ τ′} → τ ∈ Γ → τ ∈ (Γ , τ′)

  {-
remove : ∀ {Γ τ} → τ ∈ Γ → Cxt
remove {∅} x = ∅
remove {Γ , τ} Z = Γ
remove {Γ , τ} (S x) = remove x
-}

data _<_ : ∀ {Γ τ τ′} → τ ∈ Γ → τ′ ∈ Γ → Set where
  Z<S : ∀ {Γ τ τ′ x′} → Z < S {τ′} {Γ} {τ} x′
  S<S : ∀ {Γ τ τ′ τ′′ x x′} → x < x′ → S {τ′′} x < S {τ′} {Γ} {τ} x′

_<?_ : ∀ {Γ τ τ′} (x : τ ∈ Γ) (x′ : τ′ ∈ Γ) → Dec (x < x′)
Z <? Z = no (λ ())
Z <? S x′ = yes Z<S
S x <? Z = no (λ ())
S x <? S x′ with x <? x′
S x <? S x′ | yes x<x′ = yes (S<S x<x′)
S x <? S x′ | no  x≥x′ = no (λ {(S<S x<x′) → x≥x′ x<x′})

data Term (Γ : Cxt) : Type → Set where
  unit : Term Γ Unit
  var : ∀ {τ} → τ ∈ Γ → Term Γ τ
  abs : (τ₁ : Type) → ∀ {τ₂} → (t : Term (Γ , τ₁) τ₂) → Term Γ (τ₁ ⇒ τ₂)
  app : ∀ {τ₁ τ₂} → (t₁ : Term Γ (τ₁ ⇒ τ₂)) → (t₂ : Term Γ τ₁) → Term Γ τ₂

data Value {Γ} : ∀ {τ} → Term Γ τ → Set where
  unit : Value unit
  abs : ∀ {τ₁ τ₂} {t : Term (Γ , τ₁) τ₂} → Value (abs τ₁ t)

  {-
↑ : ∀ {Γ τ τ′′} → (τ′ : Type) → (x : τ′′ ∈ Γ) → Term Γ τ → Term (Γ , τ′) τ
↑ τ′ x unit = unit
↑ τ′ x (var k) with k <? x
↑ τ′ x (var k) | yes k<x = {!!}
↑ τ′ x (var k) | no  k≥x = var (S k)
↑ τ′ x (abs τ t) = abs τ {!↑ τ′ (S x) t!}
↑ τ′ x (app t₁ t₂) = {!!}
-}

{-
[_↦_]_ : ∀ {Γ τ τ′} → (x : τ′ ∈ Γ) → Term {!!} τ′ → Term Γ τ → Term (remove x) τ
[ x ↦ v ] unit = unit
[ x ↦ v ] var y = {!!}
[ x ↦ v ] abs τ t = abs τ {!!}
[ x ↦ v ] app t₁ t₂ = app ([ x ↦ v ] t₁) ([ x ↦ v ] t₂)
-}

data _⟶_ {Γ τ} : Term Γ τ → Term Γ τ → Set where
  app-1 : ∀ {τ′} {t₁ t₁′ : Term Γ (τ′ ⇒ τ)} {t₂} → t₁ ⟶ t₁′ → app t₁ t₂ ⟶ app t₁′ t₂
  app-2 : ∀ {τ′} {v : Term Γ (τ′ ⇒ τ)} {t t′} → Value v → t ⟶ t′ → app v t ⟶ app v t′
  app-abs : ∀ {τ′ t v} → Value v → app (abs τ′ t) v ⟶ {!!}
  --app-abs : ∀ {τ′ t v} → Value v → app (abs τ′ t) v ⟶ ([ Z ↦ v ] t)
