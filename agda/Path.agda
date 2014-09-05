open import Common
open import Type
open import Life
open import Route
open import Layout
module Path where

data Path (#x : ℕ) : Set where
  var : Fin #x → Path #x
  * : Path #x → Path #x

↑#x-p : ∀ {#x} → ℕ → Path #x → Path (S #x)
↑#x-p c (var x) = var (↑ c x)
↑#x-p c (* p) = * (↑#x-p c p)

data ↓#x-p {#x} : ℕ → Path (S #x) → Path #x → Set where
  var : ∀ {c x x′} → ↓ c x x′ → ↓#x-p c (var x) (var x′)
  * : ∀ {c p p′} → ↓#x-p c p p′ → ↓#x-p c (* p) (* p′)

data _⊢_∶_path {#x} (Γ : Cxt #x) : Path #x → Type #x → Set where
  var : ∀ {x} → Γ ⊢ var x ∶ (Γ ! x) path
  *~ : ∀ {p τ} → Γ ⊢ p ∶ ~ τ path → Γ ⊢ * p ∶ τ path
  *& : ∀ {p ℓ μ τ} → Γ ⊢ p ∶ & ℓ μ τ path → Γ ⊢ * p ∶ τ path

-- Path evaluation
data _⊢_⟶_ {#x #a} (M : Mem #x #a) : Path #x → Route #x #a → Set where
  var : ∀ {x} → M ⊢ var x ⟶ stack x
  * : ∀ {p r r′} → M ⊢ p ⟶ r → M ⊢ r ⇒ ptr (just r′) → M ⊢ * p ⟶ r′

data _⊢_owned {#x} (Γ : Cxt #x) : Path #x → Set where
  var : ∀ {x} → Γ ⊢ var x owned
  *~ : ∀ {p τ} → Γ ⊢ p ∶ ~ τ path → Γ ⊢ * p owned

data _⊢_freezable-for_ {#x} (Γ : Cxt #x) : Path #x → Life #x → Set where
  var : ∀ {x ℓ} → Γ ⊢ var x freezable-for ℓ
  *~ : ∀ {p τ ℓ}
     → Γ ⊢ p ∶ ~ τ path
     → Γ ⊢ p freezable-for ℓ
     → Γ ⊢ * p freezable-for ℓ
  *&mut : ∀ {p ℓ′ μ τ ℓ}
        → Γ ⊢ p ∶ & ℓ′ μ τ path
        → ℓ :<: ℓ′
        → Γ ⊢ p freezable-for ℓ
        → Γ ⊢ * p freezable-for ℓ
  *&imm : ∀ {p ℓ′ μ τ ℓ}
        → Γ ⊢ p ∶ & ℓ′ μ τ path
        → ℓ :<: ℓ′
        → Γ ⊢ * p freezable-for ℓ

data _⊢_unique-for_ {#x} (Γ : Cxt #x) : Path #x → Life #x → Set where
  var : ∀ {x ℓ} → Γ ⊢ var x unique-for ℓ
  *~ : ∀ {p τ ℓ}
     → Γ ⊢ p ∶ ~ τ path
     → Γ ⊢ p unique-for ℓ
     → Γ ⊢ * p unique-for ℓ
  *&mut : ∀ {p ℓ′ μ τ ℓ}
        → Γ ⊢ p ∶ & ℓ′ μ τ path
        → ℓ :<: ℓ′
        → Γ ⊢ p unique-for ℓ
        → Γ ⊢ * p unique-for ℓ

data _⊢_valid-for_ {#x} (Γ : Cxt #x) : Path #x → Life #x → Set where
  var : ∀ {x ℓ}
      → ℓ :<: val x
      → Γ ⊢ var x valid-for ℓ
  *~ : ∀ {p τ ℓ}
     → Γ ⊢ p ∶ ~ τ path
     → Γ ⊢ p valid-for ℓ
     → Γ ⊢ * p valid-for ℓ
  & : ∀ {p ℓ′ μ τ ℓ}
    → Γ ⊢ p ∶ & ℓ′ μ τ path
    → ℓ :<: ℓ′
    → Γ ⊢ * p valid-for ℓ

record _⊢_outlives_ {#x} (Γ : Cxt #x) (p : Path #x) (ℓ : Life #x) : Set where
  constructor outlives
  field
    valid : Γ ⊢ p valid-for ℓ
    {τ} : Type #x
    path : Γ ⊢ p ∶ τ path
    bound : τ bound-by ℓ

  {-
path-progress : ∀ {#x #ℓ p τ} {Γ : Context #ℓ #x}
              → Γ ⊢ p ∶ τ
              → ∀ {#a} → Σ[ r ∈ Route #x #a ] ⊢ p ⟶ r
path-progress var = (stack _) , var
path-progress (*~ p∶~τ) {#a} with path-progress p∶~τ {#a}
path-progress (*~ p∶~τ) | r , p⟶r = * r , * p⟶r
path-progress (*& p∶&τ) {#a} with path-progress p∶&τ {#a}
path-progress (*& p∶&τ) | r , p⟶r = * r , * p⟶r

path-preservation : ∀ {#x #a #ℓ p r τ} {Γ : Context #ℓ #x} {Σ : Context #ℓ #a}
                  → Γ ⊢ p ∶ τ
                  → ⊢ p ⟶ r
                  → Γ , Σ ⊢ r ∶ τ route
path-preservation var var = stack
path-preservation (*~ p∶~τ) (* p⟶r) = *~ (path-preservation p∶~τ p⟶r)
path-preservation (*& p∶&τ) (* p⟶r) = *& (path-preservation p∶&τ p⟶r)
-}
