open import Common
open import Life
open import Mut

module Type where

data Type (#s #u #x #ℓ : ℕ) : Set where
  int : Type #s #u #x #ℓ
  ~ : Type (plus #s #u) 0 #x #ℓ → Type #s #u #x #ℓ
  & : (ℓ : Life #x #ℓ) → (m : Mut) → Type (plus #s #u) 0 #x #ℓ → Type #s #u #x #ℓ
  opt : Type #s #u #x #ℓ → Type #s #u #x #ℓ
  rec : ∀ {n} → (τs : Vec (Type #s #u #x #ℓ) n) → Type #s #u #x #ℓ
  μ : Type #s (S #u) #x #ℓ → Type #s #u #x #ℓ
  var : (s : Fin #s) → Type #s #u #x #ℓ

Cxt : ℕ → ℕ → ℕ → ℕ → Set
Cxt #s #u #x #ℓ = Vec (Type #s #u #x #ℓ) #x

subst-τ : ∀ {#s #u #x #ℓ #ℓ′} → Vec (Life #x #ℓ) #ℓ′ → Type #s #u 0 #ℓ′ → Type #s #u #x #ℓ
subst-τ ℓs int = int
subst-τ ℓs (~ τ) = ~ (subst-τ ℓs τ)
subst-τ ℓs (& ℓ m τ) = & (subst-ℓ ℓs ℓ) m (subst-τ ℓs τ)
subst-τ ℓs (opt τ) = opt (subst-τ ℓs τ)
subst-τ ℓs (rec τs) = rec (helper τs)
  where
  helper : ∀ {n} → Vec _ n → Vec _ n
  helper [] = []
  helper (τ ∷ τs′) = subst-τ ℓs τ ∷ helper τs′
subst-τ ℓs (μ τ) = μ (subst-τ ℓs τ)
subst-τ ℓs (var s) = var s

↑#x-τ : ∀ {#s #u #x #ℓ} → ℕ → Type #s #u #x #ℓ → Type #s #u (S #x) #ℓ
↑#x-τ c int = int
↑#x-τ c (~ τ) = ~ (↑#x-τ c τ)
↑#x-τ c (& ℓ m τ) = & (↑#x-ℓ c ℓ) m (↑#x-τ c τ)
↑#x-τ c (opt τ) = opt (↑#x-τ c τ)
↑#x-τ c (rec τs) = rec (helper τs)
  where
  helper : ∀ {n} → Vec _ n → Vec _ n
  helper [] = []
  helper (τ ∷ τs′) = ↑#x-τ c τ ∷ helper τs′
↑#x-τ c (μ τ) = μ (↑#x-τ c τ)
↑#x-τ c (var s) = var s

{-
data ↓#x-τ {#s #x} : ℕ → Type #s (S #x) → Type #s #x → Set where
  int : ∀ {c} → ↓#x-τ c int int
  ~ : ∀ {c τ τ′} → ↓#x-τ c τ τ′ → ↓#x-τ c (~ τ) (~ τ′)
  & : ∀ {c ℓ ℓ′ μ τ τ′} → ↓#x-ℓ c ℓ ℓ′ → ↓#x-τ c τ τ′ → ↓#x-τ c (& ℓ μ τ) (& ℓ′ μ τ′)
  opt : ∀ {c τ τ′} → ↓#x-τ c τ τ′ → ↓#x-τ c (opt τ) (opt τ′)
  struct : ∀ {c s} → ↓#x-τ c (struct s) (struct s)
-}

↑#s-τ : ∀ {#s #u #x #ℓ} → ℕ → Type #s #u #x #ℓ → Type (S #s) #u #x #ℓ
↑#s-τ c int = int
↑#s-τ c (~ τ) = ~ (↑#s-τ (S c) τ)
↑#s-τ c (& ℓ m τ) = & ℓ m (↑#s-τ (S c) τ)
↑#s-τ c (opt τ) = opt (↑#s-τ c τ)
↑#s-τ c (rec τs) = rec (helper τs)
  where
  helper : ∀ {n} → Vec _ n → Vec _ n
  helper [] = []
  helper (τ ∷ τs′) = ↑#s-τ c τ ∷ helper τs′
↑#s-τ c (μ τ) = μ (↑#s-τ c τ)
↑#s-τ c (var x) = var (↑ c x)

↑#u-τ : ∀ {#s #u #x #ℓ} → ℕ → Type #s #u #x #ℓ → Type #s (S #u) #x #ℓ
↑#u-τ c int = int
↑#u-τ {#s} {#u} {#x} {#ℓ} c (~ τ) = ~ (fix-+ (↑#s-τ (plus #u c) τ))
  where fix-+ = subst (λ s → Type s 0 #x #ℓ) (sym (plus-S #s #u))
↑#u-τ {#s} {#u} {#x} {#ℓ} c (& ℓ m τ) = & ℓ m (fix-+ (↑#s-τ (plus #u c) τ))
  where fix-+ = subst (λ s → Type s 0 #x #ℓ) (sym (plus-S #s #u))
↑#u-τ c (opt τ) = opt (↑#u-τ c τ)
↑#u-τ c (rec τs) = rec (helper τs)
  where
  helper : ∀ {n} → Vec _ n → Vec _ n
  helper [] = []
  helper (τ ∷ τs′) = ↑#u-τ c τ ∷ helper τs′
↑#u-τ c (μ τ) = μ (↑#u-τ (S c) τ)
↑#u-τ c (var x) = var x

promote-closed : ∀ {#s #u #x #ℓ} → Type 0 0 #x #ℓ → Type #s #u #x #ℓ
promote-closed {#s} {#u} τ = ⇑#s (⇑#u τ)
  where
  ⇑#s = ⇑′ (λ s → Type s #u _ _) ↑#s-τ #s 0
  ⇑#u = ⇑′ (λ u → Type 0 u _ _) ↑#u-τ #u 0

μ-subst[s] : ∀ {#s #u #x #ℓ} → Type 0 0 #x #ℓ → Type (S #s) #u #x #ℓ → Type #s #u #x #ℓ
μ-subst[s] τ′ int = int
μ-subst[s] τ′ (~ τ) = ~ (μ-subst[s] τ′ τ)
μ-subst[s] τ′ (& ℓ m τ) = & ℓ m (μ-subst[s] τ′ τ)
μ-subst[s] τ′ (opt τ) = opt (μ-subst[s] τ′ τ)
μ-subst[s] τ′ (rec τs) = rec (helper τs)
  where
  helper : ∀ {n} → Vec _ n → Vec _ n
  helper [] = []
  helper (τ ∷ τs′) = μ-subst[s] τ′ τ ∷ helper τs′
μ-subst[s] τ′ (μ τ) = μ (μ-subst[s] τ′ τ)
μ-subst[s] τ′ (var x) with x == max-el
μ-subst[s] τ′ (var .max-el) | yes refl = promote-closed τ′
μ-subst[s] τ′ (var x) | no ¬max-el = var (↓¬max-el ¬max-el)

μ-subst[u] : ∀ {#u #x #ℓ} → Type 0 0 #x #ℓ → Type 0 (S #u) #x #ℓ → Type 0 #u #x #ℓ
μ-subst[u] τ′ int = int
μ-subst[u] τ′ (~ τ) = ~ (μ-subst[s] τ′ τ)
μ-subst[u] τ′ (& ℓ m τ) = & ℓ m (μ-subst[s] τ′ τ)
μ-subst[u] τ′ (opt τ) = opt (μ-subst[u] τ′ τ)
μ-subst[u] τ′ (rec τs) = rec (helper τs)
  where
  helper : ∀ {n} → Vec _ n → Vec _ n
  helper [] = []
  helper (τ ∷ τs′) = μ-subst[u] τ′ τ ∷ helper τs′
μ-subst[u] τ′ (μ τ) = μ (μ-subst[u] τ′ τ)
μ-subst[u] τ′ (var ())

private
  test-ℕ : Type 0 0 0 0
  test-ℕ = μ (opt (~ (var fZ)))

  test-ℕ-unroll : μ-subst[u] {#u = 0} test-ℕ (opt (~ (var fZ)))
                ≡ opt (~ (μ (opt (~ (var fZ)))))
  test-ℕ-unroll = refl

data _Copy {#s #u #x #ℓ} : Type #s #u #x #ℓ → Set where
  int : int Copy
  &imm : ∀ {ℓ τ} → & ℓ imm τ Copy
  opt : ∀ {τ} → τ Copy → opt τ Copy
  rec : ∀ {n τs} → All _Copy {n} τs → rec τs Copy
  μ : ∀ {τ} → τ Copy → μ τ Copy

data _Move {#s #u #x #ℓ} : Type #s #u #x #ℓ → Set where
  ~ : ∀ {τ} → ~ τ Move
  &mut : ∀ {ℓ τ} → & ℓ mut τ Move
  opt : ∀ {τ} → τ Move → opt τ Move
  rec : ∀ {n τs} → Any _Move {n} τs → rec τs Move
  μ : ∀ {τ} → τ Move → μ τ Move

copy×move : ∀ {#s #u #x #ℓ} (τ : Type #s #u #x #ℓ) → ¬ (τ Copy × τ Move)
copy×move int (copy , ())
copy×move (~ τ) (() , move)
copy×move (& ℓ imm τ) (copy , ())
copy×move (& ℓ mut τ) (() , move)
copy×move (opt τ) (opt copy , opt move) = copy×move τ (copy , move)
copy×move (rec τs) (rec all-copy , rec any-move) = helper τs (all-copy , any-move)
  where
  helper : ∀ {n} (τs : Vec _ n) → ¬ (All _ τs × Any _ τs)
  helper [] (all , ())
  helper (τ ∷ τs′) ((copy ∷ all) , Z move) = copy×move τ (copy , move)
  helper (τ ∷ τs′) ((copy ∷ all) , S any) = helper τs′ (all , any)
copy×move (μ τ) (μ copy , μ move) = copy×move τ (copy , move)
copy×move (var x) (() , ())

copy+move : ∀ {#u #x #ℓ} (τ : Type 0 #u #x #ℓ) → τ Copy + τ Move
copy+move int = inl int
copy+move (~ τ) = inr ~
copy+move (& ℓ imm τ) = inl &imm
copy+move (& ℓ mut τ) = inr &mut
copy+move (opt τ) with copy+move τ
copy+move (opt τ) | inl copy = inl (opt copy)
copy+move (opt τ) | inr move = inr (opt move)
copy+move (rec τs) with helper τs
  where
  helper : ∀ {n} (τs : Vec _ n) → (All _ τs + Any _ τs)
  helper [] = inl []
  helper (τ ∷ τs′) with helper τs′
  helper (τ ∷ τs′) | inl all-copy with copy+move τ
  helper (τ ∷ τs′) | inl all-copy | inl copy = inl (copy ∷ all-copy)
  helper (τ ∷ τs′) | inl all-copy | inr move = inr (Z move)
  helper (τ ∷ τs′) | inr any-move = inr (S any-move)
copy+move (rec τs) | inl all-copy = inl (rec all-copy)
copy+move (rec τs) | inr any-move = inr (rec any-move)
copy+move (μ τ) with copy+move τ
copy+move (μ τ) | inl copy = inl (μ copy)
copy+move (μ τ) | inr move = inr (μ move)
copy+move (var ())

data _Drop {#s #u #x #ℓ} : Type #s #u #x #ℓ → Set where
  ~ : ∀ {τ} → ~ τ Drop
  opt : ∀ {τ} → τ Drop → opt τ Drop
  rec : ∀ {n τs} → Any _Drop {n} τs → rec τs Drop
  μ : ∀ {τ} → τ Drop → μ τ Drop

data _Safe {#s #u #x #ℓ} : Type #s #u #x #ℓ → Set where
  int : int Safe
  & : ∀ {ℓ m τ} → & ℓ m τ Safe
  opt : ∀ {τ} → τ Safe → opt τ Safe
  rec : ∀ {n τs} → All _Safe {n} τs → rec τs Safe
  μ : ∀ {τ} → τ Safe → μ τ Safe

drop×safe : ∀ {#s #u #x #ℓ} (τ : Type #s #u #x #ℓ) → ¬ (τ Drop × τ Safe)
drop×safe int (() , safe)
drop×safe (~ τ) (drop , ())
drop×safe (& ℓ m τ) (() , safe)
drop×safe (opt τ) (opt drop , opt safe) = drop×safe τ (drop , safe)
drop×safe (rec τs) (rec any-drop , rec all-safe) = helper τs (any-drop , all-safe)
  where
  helper : ∀ {n} (τs : Vec _ n) → ¬ (Any _ τs × All _ τs)
  helper [] (() , all)
  helper (τ ∷ τs′) (Z drop , (safe ∷ all)) = drop×safe τ (drop , safe)
  helper (τ ∷ τs′) (S any , (safe ∷ all)) = helper τs′ (any , all)
drop×safe (μ τ) (μ drop , μ safe) = drop×safe τ (drop , safe)
drop×safe (var x) (() , ())

drop+safe : ∀ {#u #x #ℓ} (τ : Type 0 #u #x #ℓ) → τ Drop + τ Safe
drop+safe int = inr int
drop+safe (~ τ) = inl ~
drop+safe (& ℓ m τ) = inr &
drop+safe (opt τ) with drop+safe τ
drop+safe (opt τ) | inl drop = inl (opt drop)
drop+safe (opt τ) | inr safe = inr (opt safe)
drop+safe (rec τs) with helper τs
  where
  helper : ∀ {n} (τs : Vec _ n) → (Any _ τs + All _ τs)
  helper [] = inr []
  helper (τ ∷ τs′) with helper τs′
  helper (τ ∷ τs′) | inl any-drop = inl (S any-drop)
  helper (τ ∷ τs′) | inr all-safe with drop+safe τ
  helper (τ ∷ τs′) | inr all-safe | inl drop = inl (Z drop)
  helper (τ ∷ τs′) | inr all-safe | inr safe = inr (safe ∷ all-safe)
drop+safe (rec τs) | inl any-drop = inl (rec any-drop)
drop+safe (rec τs) | inr all-safe = inr (rec all-safe)
drop+safe (μ τ) with drop+safe τ
drop+safe (μ τ) | inl drop = inl (μ drop)
drop+safe (μ τ) | inr safe = inr (μ safe)
drop+safe (var ())

data _<:_ {#s #u #x #ℓ} : Type #s #u #x #ℓ → Type #s #u #x #ℓ → Set where
  int : int <: int
  ~ : ∀ {τ₁ τ₂} → τ₁ <: τ₂ → ~ τ₁ <: ~ τ₂
  &imm : ∀ {ℓ₁ ℓ₂ τ₁ τ₂} → ℓ₂ :<: ℓ₁ → τ₁ <: τ₂ → & ℓ₁ imm τ₁ <: & ℓ₂ imm τ₂
  &mut : ∀ {ℓ₁ ℓ₂ τ} → ℓ₂ :<: ℓ₁ → & ℓ₁ mut τ <: & ℓ₂ mut τ
  opt : ∀ {τ₁ τ₂} → τ₁ <: τ₂ → opt τ₁ <: opt τ₂
  rec : ∀ {n τs₁ τs₂} → All2 _<:_ {n} τs₁ τs₂ → rec τs₁ <: rec τs₂
  μ : ∀ {τ₁ τ₂} → τ₁ <: τ₂ → μ τ₁ <: μ τ₂
  var : ∀ {s} → var s <: var s

<:-refl : ∀ {#s #u #x #ℓ} (τ : Type #s #u #x #ℓ) → τ <: τ
<:-refl int = int
<:-refl (~ τ) = ~ (<:-refl τ)
<:-refl (& ℓ imm τ) = &imm (:<:-refl ℓ) (<:-refl τ)
<:-refl (& ℓ mut τ) = &mut (:<:-refl ℓ)
<:-refl (opt τ) = opt (<:-refl τ)
<:-refl (rec τs) = rec (helper τs)
  where
  helper : ∀ {n} (τs : Vec _ n) → All2 _<:_ τs τs
  helper [] = []
  helper (τ ∷ τs′) = <:-refl τ ∷ helper τs′
<:-refl (μ τ) = μ (<:-refl τ)
<:-refl (var s) = var

<:-antisym : ∀ {#s #u #x #ℓ} {τ₁ τ₂ : Type #s #u #x #ℓ} → τ₁ <: τ₂ → τ₂ <: τ₁ → τ₁ ≡ τ₂
<:-antisym int int = refl
<:-antisym (~ τ₁<:τ₂) (~ τ₂<:τ₁) = cong ~ (<:-antisym τ₁<:τ₂ τ₂<:τ₁)
<:-antisym (&imm ℓ₂:<:ℓ₁ τ₁<:τ₂) (&imm ℓ₁:<:ℓ₂ τ₂<:τ₁)
  rewrite :<:-antisym ℓ₂:<:ℓ₁ ℓ₁:<:ℓ₂ = cong (& _ imm) (<:-antisym τ₁<:τ₂ τ₂<:τ₁)
<:-antisym (&mut ℓ₂:<:ℓ₁) (&mut ℓ₁:<:ℓ₂) = cong (λ ℓ → & ℓ mut _) (:<:-antisym ℓ₁:<:ℓ₂ ℓ₂:<:ℓ₁)
<:-antisym (opt τ₁<:τ₂) (opt τ₂<:τ₁) = cong opt (<:-antisym τ₁<:τ₂ τ₂<:τ₁)
<:-antisym (rec τs₁<:τs₂) (rec τs₂<:τs₁) = cong rec (helper τs₁<:τs₂ τs₂<:τs₁)
  where
  helper : ∀ {n} {τs₁ τs₂ : Vec _ n} → All2 _<:_ τs₁ τs₂ → All2 _<:_ τs₂ τs₁ → τs₁ ≡ τs₂
  helper [] [] = refl
  helper (τ₁<:τ₂ ∷ H1) (τ₂<:τ₁ ∷ H2) rewrite <:-antisym τ₁<:τ₂ τ₂<:τ₁ = cong (_∷_ _) (helper H1 H2)
<:-antisym (μ τ₁<:τ₂) (μ τ₂<:τ₁) = cong μ (<:-antisym τ₁<:τ₂ τ₂<:τ₁)
<:-antisym var var = refl

<:-trans : ∀ {#s #u #x #ℓ} {τ₁ τ₂ τ₃ : Type #s #u #x #ℓ} → τ₁ <: τ₂ → τ₂ <: τ₃ → τ₁ <: τ₃
<:-trans int int = int
<:-trans (~ τ₁<:τ₂) (~ τ₂<:τ₃) = ~ (<:-trans τ₁<:τ₂ τ₂<:τ₃)
<:-trans (&imm ℓ₂:<:ℓ₁ τ₁<:τ₂) (&imm ℓ₃:<:ℓ₂ τ₂<:τ₃)
  = &imm (:<:-trans ℓ₃:<:ℓ₂ ℓ₂:<:ℓ₁) (<:-trans τ₁<:τ₂ τ₂<:τ₃)
<:-trans (&mut ℓ₂:<:ℓ₁) (&mut ℓ₃:<:ℓ₂) = &mut (:<:-trans ℓ₃:<:ℓ₂ ℓ₂:<:ℓ₁)
<:-trans (opt τ₁<:τ₂) (opt τ₂<:τ₃) = opt (<:-trans τ₁<:τ₂ τ₂<:τ₃)
<:-trans (rec τs₁<:τs₂) (rec τs₂<:τs₃) = rec (helper τs₁<:τs₂ τs₂<:τs₃)
  where
  helper : ∀ {n} {τs₁ τs₂ τs₃ : Vec _ n} → All2 _<:_ τs₁ τs₂ → All2 _<:_ τs₂ τs₃ → All2 _<:_ τs₁ τs₃
  helper [] [] = []
  helper (τ₁<:τ₂ ∷ H12) (τ₂<:τ₃ ∷ H23) = <:-trans τ₁<:τ₂ τ₂<:τ₃ ∷ helper H12 H23
<:-trans (μ τ₁<:τ₂) (μ τ₂<:τ₃) = μ (<:-trans τ₁<:τ₂ τ₂<:τ₃)
<:-trans var var = var

data _bound-by_ {#s #u #x #ℓ} : Type #s #u #x #ℓ → Life #x #ℓ → Set where
  int : ∀ {ℓ} → int bound-by ℓ
  ~ : ∀ {τ ℓ} → τ bound-by ℓ → ~ τ bound-by ℓ
  & : ∀ {ℓ′ m τ ℓ} → ℓ :<: ℓ′ → τ bound-by ℓ → & ℓ′ m τ bound-by ℓ
  opt : ∀ {τ ℓ} → τ bound-by ℓ → opt τ bound-by ℓ
  rec : ∀ {n τs ℓ} → All (λ τ → τ bound-by ℓ) {n} τs → rec τs bound-by ℓ
  μ : ∀ {τ ℓ} → τ bound-by ℓ → μ τ bound-by ℓ
  var : ∀ {s ℓ} → var s bound-by ℓ

bound-by-:<: : ∀ {#s #u #x #ℓ} {τ : Type #s #u #x #ℓ} {ℓ₁ ℓ₂ : Life #x #ℓ}
             → ℓ₁ :<: ℓ₂ → τ bound-by ℓ₂ → τ bound-by ℓ₁
bound-by-:<: ℓ₁:<:ℓ₂ int = int
bound-by-:<: ℓ₁:<:ℓ₂ (~ τ<ℓ₂) = ~ (bound-by-:<: ℓ₁:<:ℓ₂ τ<ℓ₂)
bound-by-:<: ℓ₁:<:ℓ₂ (& ℓ₂:<:ℓ′ τ<ℓ₂) = & (:<:-trans ℓ₁:<:ℓ₂ ℓ₂:<:ℓ′) (bound-by-:<: ℓ₁:<:ℓ₂ τ<ℓ₂)
bound-by-:<: ℓ₁:<:ℓ₂ (opt τ<ℓ₂) = opt (bound-by-:<: ℓ₁:<:ℓ₂ τ<ℓ₂)
bound-by-:<: ℓ₁:<:ℓ₂ (rec τs<ℓ₂) = rec (helper τs<ℓ₂)
  where
  helper : ∀ {n} {τs : Vec _ n} → All _ τs → All _ τs
  helper [] = []
  helper (τ<ℓ₂ ∷ τs<ℓ₂′) = bound-by-:<: ℓ₁:<:ℓ₂ τ<ℓ₂ ∷ helper τs<ℓ₂′
bound-by-:<: ℓ₁:<:ℓ₂ (μ τ<ℓ₂) = μ (bound-by-:<: ℓ₁:<:ℓ₂ τ<ℓ₂)
bound-by-:<: ℓ₁:<:ℓ₂ var = var

{-
{-
Types are indexed by the lifetime relation (so the lifetimes of & are always well-formed).
-}
data Type (#s #x : ℕ) : Set where
  int : Type #s #x
  ~ : Type #s #x → Type #s #x
  & : Life #x → Mut → Type #s #x → Type #s #x
  opt : Type #s #x → Type #s #x
  struct : Fin #s → Type #s #x

record Struct (#s : ℕ) : Set where
  constructor struct
  field
    -- TODO lifetime params with variance
    {#fields} : ℕ
    fields : Vec (Type #s 0) #fields
open Struct

Structs : ℕ → Set
Structs #s = Vec (Struct #s) #s

data NoUnboxed {#s #x : ℕ} (§ : Structs #s) : Fin #s → Type #s #x → Set where
  int : ∀ {s} → NoUnboxed § s int
  ~ : ∀ {s τ} → NoUnboxed § s (~ τ)
  & : ∀ {s ℓ μ τ} → NoUnboxed § s (& ℓ μ τ)
  opt : ∀ {s τ} → NoUnboxed § s τ → NoUnboxed § s (opt τ)
  struct : ∀ {s s′} → ¬ (s ≡ s′) → All (NoUnboxed § s) (fields (§ ! s′)) → NoUnboxed § s (struct s′)

record struct-ok {#s} (§ : Structs #s) (s : Fin #s) : Set where
  constructor struct
  field
    fields-ok : All (NoUnboxed § s) (fields (§ ! s))
open struct-ok

§-ok : ∀ {#s} → Structs #s → Set
§-ok {#s} § = All (struct-ok §) (range′ #s)

data UnboxedRec {#s #x : ℕ} (§ : Structs #s) : Fin #s → Type #s #x → Set where
  unboxed : ∀ {s} → UnboxedRec § s (struct s)
  opt : ∀ {s τ} → UnboxedRec § s τ → UnboxedRec § s (opt τ)
  struct : ∀ {s s′} → Any (UnboxedRec § s) (fields (§ ! s)) → UnboxedRec § s (struct s′)

data Unbounded {#s #x : ℕ} (§ : Structs #s) : Type #s #x → Set where
  opt : ∀ {τ} → Unbounded § τ → Unbounded § (opt τ)
  struct : ∀ {s} → Any (UnboxedRec § s) (fields (§ ! s)) → Unbounded § (struct s)

data Bounded {#s #x : ℕ} (§ : Structs #s) : Type #s #x → Set where
  int : Bounded § int
  ~ : ∀ {τ} → Bounded § (~ τ)
  & : ∀ {ℓ μ τ} → Bounded § (& ℓ μ τ)
  opt : ∀ {τ} → Bounded § τ → Bounded § (opt τ)
  struct : ∀ {s} → All (NoUnboxed § s) (fields (§ ! s)) → Bounded § (struct s)

  {-
private
  ~-inj : ∀ {#x #s} {τ₁ τ₂ : Type #x #s} → ~ τ₁ ≡ ~ τ₂ → τ₁ ≡ τ₂
  ~-inj refl = refl
  &-inj : ∀ {#x μ} {ℓ₁ ℓ₂ : Life #x} {τ₁ τ₂ : Type #x #s} → & ℓ₁ μ τ₁ ≡ & ℓ₂ μ τ₂ → ℓ₁ ≡ ℓ₂ × τ₁ ≡ τ₂
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
-}

-- A context is a vector of types (variables -> types)
Cxt : ℕ → ℕ → Set
Cxt #s #x = Vec (Type #s #x) #x

-- upshift and downshift for the indicies of types
↑#x-τ : ∀ {#s #x} → ℕ → Type #s #x → Type #s (S #x)
↑#x-τ c int = int
↑#x-τ c (~ τ) = ~ (↑#x-τ c τ)
↑#x-τ c (& ℓ μ τ) = & (↑#x-ℓ c ℓ) μ (↑#x-τ c τ)
↑#x-τ c (opt τ) = opt (↑#x-τ c τ)
↑#x-τ c (struct s) = struct s

data ↓#x-τ {#s #x} : ℕ → Type #s (S #x) → Type #s #x → Set where
  int : ∀ {c} → ↓#x-τ c int int
  ~ : ∀ {c τ τ′} → ↓#x-τ c τ τ′ → ↓#x-τ c (~ τ) (~ τ′)
  & : ∀ {c ℓ ℓ′ μ τ τ′} → ↓#x-ℓ c ℓ ℓ′ → ↓#x-τ c τ τ′ → ↓#x-τ c (& ℓ μ τ) (& ℓ′ μ τ′)
  opt : ∀ {c τ τ′} → ↓#x-τ c τ τ′ → ↓#x-τ c (opt τ) (opt τ′)
  struct : ∀ {c s} → ↓#x-τ c (struct s) (struct s)

field-types : ∀ {#s #x} → (§ : Structs #s) → (s : Fin #s) → Vec (Type #s #x) (#fields (§ ! s))
field-types § s = map (⇑′ (Type _) ↑#x-τ _ 0) (fields (§ ! s))

-- The subtyping relationship
data _<:_ {#s #x} : Type #s #x → Type #s #x → Set where
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
  -- TODO variance on lifetime params
  struct : ∀ {s} → struct s <: struct s

test-subtype-1 : int {0} {0} <: int
test-subtype-1 = int
test-subtype-2 : ¬ (& {0} {3} (val (fin 1)) mut int <: & (val (fin 2)) mut int)
test-subtype-2 (&mut (val-val (s<s (s<s ()))))
test-subtype-3 : & {0} {1} static mut int <: & (val fZ) mut int
test-subtype-3 = &mut val-static
test-subtype-4 : & {0} {3} (val (fin 2)) mut int <: & (val (fin 1)) mut int
test-subtype-4 = &mut (val-val (s<s z<s))
test-subtype-5 : opt (& {0} {3} (val (fin 2)) mut int) <: opt (& (val (fin 1)) mut int)
test-subtype-5 = opt (&mut (val-val (s<s z<s)))
test-subtype-6 : ~ (& {0} {3} (val (fin 2)) mut int) <: ~ (& (val (fin 1)) mut int)
test-subtype-6 = ~ (&mut (val-val (s<s z<s)))

-- Predicate for implicitly copyable types
data _⊢_Copy {#s #x} (§ : Structs #s) : Type #s #x → Set where
  int : § ⊢ int Copy
  &imm : ∀ {ℓ τ} → § ⊢ & ℓ imm τ Copy
  opt : ∀ {τ} → § ⊢ τ Copy → § ⊢ opt τ Copy
  struct : ∀ {s} → All (λ τ → § ⊢ τ Copy) (fields (§ ! s)) → § ⊢ struct s Copy

-- Predicate for affine types
data _⊢_Affine {#s #x} (§ : Structs #s) : Type #s #x → Set where
  ~Aff : ∀ {τ} → § ⊢ ~ τ Affine
  &mut : ∀ {ℓ τ} → § ⊢ & ℓ mut τ Affine
  opt : ∀ {τ} → § ⊢ τ Affine → § ⊢ opt τ Affine
  struct : ∀ {s} → Any (λ τ → § ⊢ τ Affine) (fields (§ ! s)) → § ⊢ struct s Affine

  {-
foo : ∀ {#s #x n} {τs : Vec (Type #s #x) n} (§ : Structs #s)
    → All (_⊢_Copy §) τs → Any (_⊢_Affine §) τs → ⊥
foo § (Hcopy ∷ all-copy) (Z Haff) = {!!}
foo § (Hcopy ∷ all-copy) (S any-aff) = foo § all-copy any-aff
-}

-- No type is both Copy and Affine
copy-aff-disjoint : ∀ {#s #x} (§ : Structs #s) (τ : Type #s #x) → ¬ (§ ⊢ τ Copy × § ⊢ τ Affine)
copy-aff-disjoint § int (Hcopy , ())
copy-aff-disjoint § (~ τ) (() , Haff)
copy-aff-disjoint § (& ℓ imm τ) (Hcopy , ())
copy-aff-disjoint § (& ℓ mut τ) (() , Haff)
copy-aff-disjoint § (opt τ) (opt Hcopy , opt Haff) = copy-aff-disjoint § τ (Hcopy , Haff)
copy-aff-disjoint § (struct s) (struct all-copy , struct any-aff) =
  handle-fields (fields (§ ! s)) (all-copy , any-aff)
  where
  handle-fields : ∀ {#x′ n} (τs : Vec (Type _ #x′) n) → ¬ (All (_⊢_Copy §) τs × Any (_⊢_Affine §) τs)
  handle-fields [] (copy , ())
  handle-fields (τ ∷ _) ((Hcopy ∷ _) , Z Haff) = copy-aff-disjoint § τ (Hcopy , Haff)
  handle-fields (_ ∷ τs) ((_ ∷ Hcopy) , S Haff) = handle-fields τs (Hcopy , Haff)

  {-
bnd-cop-aff-cover : ∀ {#s #x} (§ : Structs #s) (τ : Type #s #x) → Bounded § τ
                  → § ⊢ τ Copy + § ⊢ τ Affine
bnd-cop-aff-cover § int bnd = inl int
bnd-cop-aff-cover § (~ τ) bnd = inr ~Aff
bnd-cop-aff-cover § (& ℓ imm τ) bnd = inl &imm
bnd-cop-aff-cover § (& ℓ mut τ) bnd = inr &mut
bnd-cop-aff-cover § (opt τ) (opt bnd) with bnd-cop-aff-cover § τ bnd
bnd-cop-aff-cover § (opt τ) (opt bnd) | inl cop = inl (opt cop)
bnd-cop-aff-cover § (opt τ) (opt bnd) | inr aff = inr (opt aff)
bnd-cop-aff-cover § (struct s) (struct boxed) with handle-fields (fields (§ ! s)) boxed
  where
  handle-fields : ∀ {#x′ s n} (τs : Vec (Type _ #x′) n) → All (NoUnboxed § s) τs
                → (All (_⊢_Copy §) τs) + (Any (_⊢_Affine §) τs)
  handle-fields [] [] = inl []
  handle-fields (τ ∷ τs) (τ-bxd ∷ Hbxd) = {!!}
bnd-cop-aff-cover § (struct s) (struct boxed) | inl all-copy = inl (struct all-copy)
bnd-cop-aff-cover § (struct s) (struct boxed) | inr any-aff = inr (struct any-aff)
-}

  {-
cop-unb-dis : ∀ {#s #x} (§ : Structs #s) (τ : Type #s #x) → ¬ (§ ⊢ τ Copy × Unbounded § τ)
cop-unb-dis § (opt τ) (opt cop , opt unb) = cop-unb-dis § τ (cop , unb)
cop-unb-dis § (struct s) (struct cop , struct unb) = handle-fields (fields (§ ! s)) (cop , unb)
  where
  handle-fields : ∀ {#x′ n} (τs : Vec (Type _ #x′) n) → ¬ (All (_⊢_Copy §) τs × Any (UnboxedRec § s) τs)
  handle-fields [] (Hcop , ())
  handle-fields (τ ∷ _) ((Hcop ∷ _) , Z Hunbx) = cop-unbx-dis τ (Hcop , Hunbx)
    where
    cop-unbx-dis : ∀ {#x′ s} (τ : Type _ #x′) → ¬ (§ ⊢ τ Copy × UnboxedRec § s τ)
    cop-unbx-dis ._ (struct Hcop′ , unboxed) = {!!}
    cop-unbx-dis ._ (Hcop′ , opt Hunbx′) = {!!}
    cop-unbx-dis ._ (Hcop′ , struct x₂) = {!!}
  handle-fields (_ ∷ τs) ((_ ∷ Hcop) , S Hunb) = handle-fields τs (Hcop , Hunb)
  -}

  {-
copy-aff-covering : ∀ {#s #x} (§ : Structs #s) → §-ok § → (τ : Type #s #x) → § ⊢ τ Copy + § ⊢ τ Affine
copy-aff-covering § H§ int = inl int
copy-aff-covering § H§ (~ τ) = inr ~Aff
copy-aff-covering § H§ (& ℓ imm τ) = inl &imm
copy-aff-covering § H§ (& ℓ mut τ) = inr &mut
copy-aff-covering § H§ (opt τ) with copy-aff-covering § H§ τ
copy-aff-covering § H§ (opt τ) | inl copy = inl (opt copy)
copy-aff-covering § H§ (opt τ) | inr aff = inr (opt aff)
copy-aff-covering § H§ (struct s) with handle-fields (fields (§ ! s)) (fields-ok (H§ All! s))
  where
  handle-fields : ∀ {#x′ n} (τs : Vec (Type _ #x′) n) → All (NoUnboxed § _) τs → All (_⊢_Copy §) τs + Any (_⊢_Affine §) τs
  handle-fields τs xs = {!!}
  {-
  handle-fields [] = inl []
  handle-fields (τ ∷ τs) with copy-aff-covering § H§ τ | handle-fields τs
  handle-fields (τ ∷ τs) | inl τ-copy | inl τs-copy = inl (τ-copy ∷ τs-copy)
  handle-fields (τ ∷ τs) | inl τ-copy | inr τs-aff = inr (S τs-aff)
  handle-fields (τ ∷ τs) | inr τ-aff | _ = inr (Z τ-aff)
  -}
copy-aff-covering § H§ (struct s) | inl all-copy = inl (struct all-copy)
copy-aff-covering § H§ (struct s) | inr any-aff = inr (struct any-aff)
-}
  
{-
-- TODO requires well-formed proof
copy×affine≡⊥ : ∀ {#s #x} → (§ : Structs #s) (τ : Type #s #x) → ¬ (§ ⊢ τ Copy × § ⊢ τ Affine)
copy×affine≡⊥ § int (copy , ())
copy×affine≡⊥ § (~ τ) (() , aff)
copy×affine≡⊥ § (& ℓ imm τ) (copy , ())
copy×affine≡⊥ § (& ℓ mut τ) (() , aff)
copy×affine≡⊥ § (opt τ) (opt copy , opt aff) = copy×affine≡⊥ § τ (copy , aff)
copy×affine≡⊥ § (struct s) (struct all-copy , struct any-aff) with All-Any all-copy any-aff --= copy×affine≡⊥ § (fst (Any-All any-aff all-copy)) (swap (snd (Any-All any-aff all-copy)))
copy×affine≡⊥ § (struct s) (struct all-copy , struct any-aff) | τ , (copy , any) = {!!} --copy×affine≡⊥ § τ (copy , aff)

-- Every type is either Copy or Affine
copy+affine≡⊤ : ∀ {#s #x} → (§ : Structs #s) (τ : Type #s #x) → § ⊢ τ Copy + § ⊢ τ Affine
copy+affine≡⊤ § int = inl int
copy+affine≡⊤ § (~ τ) = inr ~Aff
copy+affine≡⊤ § (& ℓ imm τ) = inl &imm
copy+affine≡⊤ § (& ℓ mut τ) = inr &mut
copy+affine≡⊤ § (opt τ) with copy+affine≡⊤ § τ
copy+affine≡⊤ § (opt τ) | inl copy = inl (opt copy)
copy+affine≡⊤ § (opt τ) | inr aff = inr (opt aff)
copy+affine≡⊤ § (struct s) = {!!}
-}
-- Thus, Affine is a correct negation of Copy

-- Predicate for types which must drop heap memory
data _⊢_Drop {#s #x} (§ : Structs #s) : Type #s #x → Set where
  ~ : ∀ {τ} → § ⊢ ~ τ Drop
  opt : ∀ {τ} → § ⊢ τ Drop → § ⊢ opt τ Drop
  struct : ∀ {s} → Any (λ τ → § ⊢ τ Drop) (fields (§ ! s)) → § ⊢ struct s Drop

-- Predicate for types which do not need to drop heap memory
data _⊢_¬Drop {#s #x} (§ : Structs #s) : Type #s #x → Set where
  int : § ⊢ int ¬Drop
  & : ∀ {ℓ μ τ} → § ⊢ & ℓ μ τ ¬Drop
  opt : ∀ {τ} → § ⊢ τ ¬Drop → § ⊢ opt τ ¬Drop
  struct : ∀ {s} → All (λ τ → § ⊢ τ ¬Drop) (fields (§ ! s)) → § ⊢ struct s ¬Drop

  {-
-- No type is both Copy and Drop
drop×copy≡⊥ : ∀ {#s #x} → (τ : Type #s #x) → ¬ (τ Drop × τ Copy)
drop×copy≡⊥ int (() , copy)
drop×copy≡⊥ (~ τ) (drop , ())
drop×copy≡⊥ (& ℓ μ τ) (() , copy)
drop×copy≡⊥ (opt τ) (opt drop , opt copy) = drop×copy≡⊥ τ (drop , copy)
drop×copy≡⊥ τ pf = {!!}

-- No type is both Drop and ¬Drop
drop×¬drop≡⊥ : ∀ {#s #x} → (τ : Type #s #x) → ¬ (τ Drop × τ ¬Drop)
drop×¬drop≡⊥ int (() , ¬drop)
drop×¬drop≡⊥ (~ τ) (drop , ())
drop×¬drop≡⊥ (& ℓ μ τ) (() , ¬drop)
drop×¬drop≡⊥ (opt τ) (opt drop , opt ¬drop) = drop×¬drop≡⊥ τ (drop , ¬drop)
drop×¬drop≡⊥ τ pf = {!!}

-- Every type is either Drop or ¬Drop
drop+¬drop≡⊤ : ∀ {#s #x} → (τ : Type #s #x) → τ Drop + τ ¬Drop
drop+¬drop≡⊤ int = inr int
drop+¬drop≡⊤ (~ τ) = inl ~
drop+¬drop≡⊤ (& ℓ μ τ) = inr &
drop+¬drop≡⊤ (opt τ) with drop+¬drop≡⊤ τ
drop+¬drop≡⊤ (opt τ) | inl drop = inl (opt drop)
drop+¬drop≡⊤ (opt τ) | inr ¬drop = inr (opt ¬drop)
drop+¬drop≡⊤ τ = {!!}

-- Thus ¬Drop is a correct negation of Drop

-- nicer name for the above proof
_Drop? : ∀ {#s #x} → (τ : Type #s #x) → τ Drop + τ ¬Drop
_Drop? τ = drop+¬drop≡⊤ τ
-}

data _bound-by_ {#s #x} : Type #s #x → Life #x → Set where
  int : ∀ {ℓ} → int bound-by ℓ
  ~ : ∀ {τ ℓ} → τ bound-by ℓ → ~ τ bound-by ℓ
  & : ∀ {ℓ′ μ τ ℓ} → ℓ :<: ℓ′ → τ bound-by ℓ → & ℓ′ μ τ bound-by ℓ
  opt : ∀ {τ ℓ} → τ bound-by ℓ → opt τ bound-by ℓ
  -- TODO lifetime params
  struct : ∀ {s ℓ} → struct s bound-by ℓ
-}
