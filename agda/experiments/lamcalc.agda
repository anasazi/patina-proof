open import Common
module experiments.lamcalc where

data Type : Set where
  unit : Type
  _⇒_ : Type → Type → Type

private
  ⇒-inj-1 : ∀ {τ₁ τ₁′ τ₂ τ₂′} → τ₁ ⇒ τ₂ ≡ τ₁′ ⇒ τ₂′ → τ₁ ≡ τ₁′
  ⇒-inj-1 refl = refl
  ⇒-inj-2 : ∀ {τ₁ τ₁′ τ₂ τ₂′} → τ₁ ⇒ τ₂ ≡ τ₁′ ⇒ τ₂′ → τ₂ ≡ τ₂′
  ⇒-inj-2 refl = refl

  _=Type=_ : ∀ (τ₁ τ₂ : Type) → Dec (τ₁ ≡ τ₂)
  unit =Type= unit = yes refl
  unit =Type= (τ₂₁ ⇒ τ₂₂) = no (λ ())
  (τ₁₁ ⇒ τ₁₂) =Type= unit = no (λ ())
  (τ₁₁ ⇒ τ₁₂) =Type= (τ₂₁ ⇒ τ₂₂) with τ₁₁ =Type= τ₂₁ | τ₁₂ =Type= τ₂₂
  (τ₁₁ ⇒ τ₁₂) =Type= (.τ₁₁ ⇒ .τ₁₂) | yes refl | yes refl = yes refl
  (τ₁₁ ⇒ τ₁₂) =Type= (.τ₁₁ ⇒ τ₂₂) | yes refl | no neq = no (neq ∘ ⇒-inj-2)
  (τ₁₁ ⇒ τ₁₂) =Type= (τ₂₁ ⇒ τ₂₂) | no neq | _ = no (neq ∘ ⇒-inj-1)

EqType : Eq Type
EqType = record { _==_ = _=Type=_ }

data Term (#x : ℕ) : Set where
  unit : Term #x
  var : Fin #x → Term #x
  abs : Type → Term (S #x) → Term #x
  app : Term #x → Term #x → Term #x

↑#x-t : ∀ {#x} → ℕ → Term #x → Term (S #x)
↑#x-t c unit = unit
↑#x-t c (var x) = var (↑ c x)
↑#x-t c (abs τ t) = abs τ (↑#x-t (S c) t)
↑#x-t c (app t₁ t₂) = app (↑#x-t c t₁) (↑#x-t c t₂)

[_↦_]_ : ∀ {#x} → Fin (S #x) → Term #x → Term (S #x) → Term #x
[ s ↦ t′ ] unit = unit
[ s ↦ t′ ] var x with Ftrichotomy x s
[ s ↦ t′ ] var x | inl x<s = var (<→shrink x x<s)
[ s ↦ t′ ] var x | inr (inl x≡s) = t′
[ s ↦ t′ ] var x | inr (inr x>s) = var (>→shrink x x>s)
[ s ↦ t′ ] abs τ t = abs τ ([ fS s ↦ ↑#x-t 0 t′ ] t)
[ s ↦ t′ ] app t₁ t₂ = app ([ s ↦ t′ ] t₁) ([ s ↦ t′ ] t₂)

{-
[_]_ : ∀ {#x} → Term #x → Term (S #x) → Term #x
[ t′ ] unit = unit
[ t′ ] var x with FIsMax? x
[ t′ ] var x | yes pf = t′
[ t′ ] var x | no ¬pf = var (↓¬max x ¬pf)
[ t′ ] abs τ t = abs τ ([ ↑#x-t 0 t′ ] t)
[ t′ ] app t₁ t₂ = app ([ t′ ] t₁) ([ t′ ] t₂)
-}

data Value {#x} : Term #x → Set where
  unit : Value unit
  abs : ∀ {τ t} → Value (abs τ t)

data _⊢_∶_ {#x} (Γ : Vec Type #x) : Term #x → Type → Set where
  unit : Γ ⊢ unit ∶ unit
  var : ∀ {x} → Γ ⊢ var x ∶ (Γ ! x)
  abs : ∀ {τ₁ τ₂ t} → (τ₁ ∷ Γ) ⊢ t ∶ τ₂ → Γ ⊢ abs τ₁ t ∶ (τ₁ ⇒ τ₂)
  app : ∀ {t₁ t₂ τ₁ τ₂} → Γ ⊢ t₁ ∶ (τ₁ ⇒ τ₂) → Γ ⊢ t₂ ∶ τ₁ → Γ ⊢ app t₁ t₂ ∶ τ₂

bar : ∀ {#x} n {t τ} (Γ′ : Vec _ n) τ′ (Γ : Vec _ #x)
    → (Γ′ ++ Γ) ⊢ t ∶ τ
    → subst (Vec Type) (plus-S n #x) (Γ′ ++ (τ′ ∷ Γ)) ⊢ ↑#x-t n t ∶ τ
bar n Γ′ τ′ Γ unit = unit
bar n Γ′ τ′ Γ var = {!!}
bar n Γ′ τ′ Γ (abs pf) = abs {!bar (S n) ? ? ? pf!}
bar n Γ′ τ′ Γ (app pf₁ pf₂) = app (bar n Γ′ τ′ Γ pf₁) (bar n Γ′ τ′ Γ pf₂)

foo : ∀ {#x t τ τ′ τ′′} {Γ : Vec _ #x} → (τ ∷ Γ) ⊢ t ∶ τ′′ → (τ ∷ τ′ ∷ Γ) ⊢ ↑#x-t 1 t ∶ τ′′
foo unit = unit
foo var = {!!}
foo (abs pf) = abs {!!}
foo (app pf₁ pf₂) = app (foo pf₁) (foo pf₂)

data _⟶_ {#x} : Term #x → Term #x → Set where
  app-1 : ∀ {t₁ t₁′ t₂} → t₁ ⟶ t₁′ → app t₁ t₂ ⟶ app t₁′ t₂
  app-2 : ∀ {v t t′} → Value v → t ⟶ t′ → app v t ⟶ app v t′
  app-abs : ∀ {τ t v} → Value v → app (abs τ t) v ⟶ ([ fZ ↦ v ] t)

unique : ∀ {#x} {Γ : Vec Type #x} {t : Term #x} {τ τ′} → Γ ⊢ t ∶ τ → Γ ⊢ t ∶ τ′ → τ ≡ τ′
unique unit unit = refl
unique var var = refl
unique (abs H1) (abs H2) rewrite unique H1 H2 = refl
unique (app H11 H12) (app H21 H22) rewrite unique H12 H22 | ⇒-inj-2 (unique H11 H21) = refl

canonical-1 : ∀ {#x} {Γ : Vec Type #x} {v : Term #x} → Value v → Γ ⊢ v ∶ unit → v ≡ unit
canonical-1 unit unit = refl
canonical-1 abs ()

canonical-2 : ∀ {#x} {Γ : Vec Type #x} {v : Term #x} {τ₁ τ₂ : Type}
            → Value v → Γ ⊢ v ∶ (τ₁ ⇒ τ₂) → Σ Term (S #x) ** λ t → v ≡ abs τ₁ t
canonical-2 unit ()
canonical-2 abs (abs pf) = _ , refl

progress : ∀ {t : Term 0} {τ : Type} → [] ⊢ t ∶ τ → Value t + Σ Term 0 ** (λ t′ → t ⟶ t′)
progress unit = inl unit
progress {var ()} var
progress (abs pf) = inl abs
progress (app pf₁ pf₂) with progress pf₁
progress (app pf₁ pf₂) | inl val₁ with progress pf₂
progress (app pf₁ pf₂) | inl val₁ | inl val₂ with canonical-2 val₁ pf₁
progress (app pf₁ pf₂) | inl val₁ | inl val₂ | _ , refl = inr (_ , app-abs val₂)
progress (app pf₁ pf₂) | inl val₁ | inr (_ , eval₂) = inr (_ , app-2 val₁ eval₂)
progress (app pf₁ pf₂) | inr (_ , eval₁) = inr (_ , app-1 eval₁)

weakening : ∀ {#x} {Γ : Vec Type #x} {t : Term #x} {τ : Type} τ′
          → Γ ⊢ t ∶ τ → (τ′ ∷ Γ) ⊢ ↑#x-t 0 t ∶ τ
weakening τ′ unit = unit
weakening τ′ (var {x}) rewrite ↑-0-fS x = var
weakening τ′ (abs pf) = abs {!!}
weakening τ′ (app pf₁ pf₂) = app (weakening τ′ pf₁) (weakening τ′ pf₂)

substitution : ∀ {#x t t′ τ τ′} {Γ : Vec _ #x}
             → (τ′ ∷ Γ) ⊢ t ∶ τ → Γ ⊢ t′ ∶ τ′ → Γ ⊢ [ fZ ↦ t′ ] t ∶ τ
substitution unit pf′ = unit
substitution (var {x}) pf′ with Ftrichotomy x fZ
substitution var pf′ | inl ()
substitution var pf′ | inr (inl refl) = pf′
substitution {τ′ = τ′} {Γ = Γ} var pf′ | inr (inr x>0)
  rewrite !->→shrink {x = τ′} {xs = Γ} x>0 = var
substitution (abs {τ′′} pf) pf′ = {!!}
substitution (app pf₁ pf₂) pf′ = app (substitution pf₁ pf′) (substitution pf₂ pf′)

{-
substitution : ∀ {#x} {t : Term (S #x)} {t′ : Term #x} {τ τ′ : Type} {Γ : Vec Type #x}
             → snoc Γ τ′ ⊢ t ∶ τ
             → Γ ⊢ t′ ∶ τ′
             → Γ ⊢ [ t′ ] t ∶ τ
substitution unit pf′ = unit
substitution (var {x}) pf′ with FIsMax? x
substitution {τ′ = τ′} {Γ = Γ} var pf′ | yes pf rewrite snoc-ismax Γ τ′ _ pf = pf′
substitution {τ′ = τ′} {Γ = Γ} var pf′ | no ¬pf rewrite snoc-notmax Γ τ′ _ ¬pf = var
substitution (abs {τ′′} pf) pf′ with substitution pf (weakening τ′′ pf′)
... | IH = abs IH
substitution (app pf₁ pf₂) pf′ with substitution pf₁ pf′ | substitution pf₂ pf′
... | IH₁ | IH₂ = app IH₁ IH₂

preservation : ∀ {#x} {Γ : Vec Type #x} {t t′ : Term #x} {τ : Type}
             → Γ ⊢ t ∶ τ → t ⟶ t′ → Γ ⊢ t′ ∶ τ
preservation unit ()
preservation var ()
preservation (abs pf) ()
preservation (app pf₁ pf₂) (app-1 ev₁) = app (preservation pf₁ ev₁) pf₂
preservation (app pf₁ pf₂) (app-2 val₁ ev₂) = app pf₁ (preservation pf₂ ev₂)
preservation (app (abs pf₁) pf₂) (app-abs val₂) = substitution {!!} pf₂
-}
