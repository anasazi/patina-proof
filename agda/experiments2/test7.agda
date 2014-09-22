open import Common
open import Life
open import Mut
module test7 where

{-
data Var : Set where
  cov : Var
  con : Var
  inv : Var

var¬ : Var → Var
var¬ cov = con
var¬ con = cov
var¬ inv = inv

_⊙_ : Var → Var → Var
cov ⊙ v = v
con ⊙ v = var¬ v
inv ⊙ v = inv

data _var≤_ : Var → Var → Set where
  refl : ∀ {v} → v var≤ v
  cov : inv var≤ cov
  con : inv var≤ con

data _⊢_var≤_ {#x #ℓ} (Ł : Vec Var #ℓ) : Life #x #ℓ → Var → Set where
  val : ∀ {x v} → Ł ⊢ val x var≤ v
  static : ∀ {v} → Ł ⊢ static var≤ v
  var : ∀ {ℓ v} → (Ł ! ℓ) var≤ v → Ł ⊢ var ℓ var≤ v

data _⊢_var=_ {#x #ℓ} (Ł : Vec Var #ℓ) : Life #x #ℓ → Var → Set where
  val : ∀ {x v} → Ł ⊢ val x var= v
  static : ∀ {v} → Ł ⊢ static var= v
  var : ∀ {ℓ v} → (Ł ! ℓ) ≡ v → Ł ⊢ var ℓ var= v

borrowee-var : Mut → Var → Var
borrowee-var imm v = var¬ v
borrowee-var mut v = inv

data Type (#s #u #x : ℕ) {#ℓ} (Ł : Vec Var #ℓ) (v : Var) : {κ : ℕ} → (K : Vec Var κ) → Set where
  int : Type #s #u #x Ł v []
  ~ : Type (plus #u #s) 0 #x Ł v [] → Type #s #u #x Ł v []
  & : (ℓ : Life #x #ℓ) (var-pf : Ł ⊢ ℓ var≤ var¬ v) (m : Mut)
    → Type (plus #u #s) 0 #x Ł (borrowee-var m v) []
    → Type #s #u #x Ł v []
  opt : Type #s #u #x Ł v [] → Type #s #u #x Ł v []
  rec : ∀ {n} (τs : Vec (Type #s #u #x Ł v []) n) → Type #s #u #x Ł v []
  μ : Type #s (S #u) #x Ł v [] → Type #s #u #x Ł v []
  var : Fin #s → Type #s #u #x Ł v []
  abs : ∀ {κ} → (Ł′ : Vec Var κ) → Type #s #u 0 {κ} Ł′ v [] → Type #s #u #x Ł v Ł′
  app : ∀ {κ K}
      → Type #s #u #x Ł v {κ} K
      → (ℓs : Vec (Life #x #ℓ) κ)
      → All2 (λ v′ ℓ → Ł ⊢ ℓ var= (v ⊙ v′)) K ℓs
      → Type #s #u #x Ł v []

srs-A : ∀ {#s #u #x #ℓ Ł} → Type #s #u #x {#ℓ} Ł cov []
srs-A = rec ([ int ])

srs-B : ∀ {#s #u #x #ℓ Ł} → Type #s #u #x {#ℓ} Ł cov ([ con ])
srs-B = abs ([ con ]) (rec ([ int ,, & (var fZ) (var refl) mut int ]))

srs-C : ∀ {#s #u #x #ℓ Ł} → Type #s #u #x {#ℓ} Ł cov ([ con ])
srs-C = abs ([ con ]) (rec ([ srs-A
                           ,, app srs-B ([ var fZ ]) (var refl ∷ []) ]))

srs-D : ∀ {#s #u #x #ℓ Ł} → Type #s #u #x {#ℓ} Ł cov ([ con ])
srs-D = abs ([ con ]) (rec ([ app srs-C ([ var fZ ]) (var refl ∷ [])
                           ,, srs-A
                           ,, app srs-C ([ var fZ ]) (var refl ∷ [])
                           ,, app srs-B ([ var fZ ]) (var refl ∷ []) ]))

srs-E : ∀ {#s #u #x #ℓ Ł} → Type #s #u #x {#ℓ} Ł cov []
srs-E = rec ([ ~ int ])

srs-List : ∀ {#s #u #x #ℓ Ł} → Type #s #u #x {#ℓ} Ł cov []
srs-List = μ (rec ([ int ,, opt (~ (var fZ)) ]))

srs-F-⊤ : ∀ {#s #u #x #ℓ Ł} → Type #s #u #x {#ℓ} Ł cov ([ con ])
srs-F-⊤ = abs ([ con ]) (app srs-B ([ var fZ ]) (var refl ∷ []))

τ-subst : ∀ {#s #u #x #ℓ Ł #ℓ′ Ł′ v κ K}
        → Vec (Life #x #ℓ) #ℓ′
        → Type #s #u 0 {#ℓ′} Ł′ v {κ} K
        → Type #s #u #x {#ℓ} Ł v K
τ-subst ℓs int = int
τ-subst ℓs (~ τ) = ~ (τ-subst ℓs τ)
τ-subst ℓs (& ℓ var-pf m τ) = & (subst-ℓ ℓs ℓ) {!!} m (τ-subst ℓs τ)
τ-subst ℓs (opt τ) = {!!}
τ-subst ℓs (rec τs) = {!!}
τ-subst ℓs (μ τ) = {!!}
τ-subst ℓs (var x) = {!!}
τ-subst ℓs (abs Ł′₁ τ) = {!!}
τ-subst ℓs (app τ ℓs₁ x) = {!!}

data _==>_ {#s #u #x #ℓ Ł v} : ∀ {κ K} → (τ₁ τ₂ : Type #s #u #x {#ℓ} Ł v {κ} K) → Set where
  refl : ∀ {κ K} {τ : Type _ _ _ _ _ {κ} K} → τ ==> τ
  ~ : ∀ {τ τ′} → τ ==> τ′ → ~ τ ==> ~ τ′
  & : ∀ {ℓ pf m τ τ′} → τ ==> τ′ → & ℓ pf m τ ==> & ℓ pf m τ′
  opt : ∀ {τ τ′} → τ ==> τ′ → opt τ ==> opt τ′
  rec : ∀ {n τs τs′} → All2 _==>_ {n} τs τs′ → rec τs ==> rec τs′
  μ : ∀ {τ τ′} → τ ==> τ′ → μ τ ==> μ τ′
  abs : ∀ {κ K τ τ′} → τ ==> τ′ → abs {κ = κ} K τ ==> abs K τ′
  app==> : ∀ {κ K τ τ′ ℓs pf} → τ ==> τ′ → app {κ = κ} {K = K} τ ℓs pf ==> app τ′ ℓs pf
  appabs : ∀ {κ K τ ℓs pf} → app (abs {κ = κ} K τ) ℓs pf ==> {!!}
  -}

{-
data Type (#s #u #x #ℓ : ℕ) : (κ : ℕ) → Set where
  int : Type #s #u #x #ℓ 0
  ~ : Type (plus #s #u) 0 #x #ℓ 0 → Type #s #u #x #ℓ 0
  & : (ℓ : Life #x #ℓ) → (m : Mut) → Type (plus #s #u) 0 #x #ℓ 0 → Type #s #u #x #ℓ 0
  opt : Type #s #u #x #ℓ 0 → Type #s #u #x #ℓ 0
  rec : ∀ {n} → (τs : Vec (Type #s #u #x #ℓ 0) n) → Type #s #u #x #ℓ 0
  μ : Type #s (S #u) #x #ℓ 0 → Type #s #u #x #ℓ 0
  var : Fin #s → Type #s #u #x #ℓ 0
  abs : ∀ {κ} → Type #s #u 0 κ 0 → Type #s #u #x #ℓ κ
  app : ∀ {κ} → Type #s #u #x #ℓ κ → Vec (Life #x #ℓ) κ → Type #s #u #x #ℓ 0
  -}

-- WORKS!
data Type (#s #u #x : ℕ) : Set where
  int : Type #s #u #x
  ~ : Type (plus #s #u) 0 #x → Type #s #u #x
  & : (ℓ : Life #x 0) → (m : Mut) → Type (plus #s #u) 0 #x → Type #s #u #x
  opt : Type #s #u #x → Type #s #u #x
  rec : ∀ {n} → (τs : Vec (Type #s #u #x) n) → Type #s #u #x
  μ : Type #s (S #u) #x → Type #s #u #x
  var : (s : Fin #s) → Type #s #u #x

↑#s-τ : ∀ {#s #u #x} → ℕ → Type #s #u #x → Type (S #s) #u #x
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

↑#u-τ : ∀ {#s #u #x} → ℕ → Type #s #u #x → Type #s (S #u) #x
↑#u-τ c int = int
↑#u-τ {#s} {#u} {#x} c (~ τ) = ~ (fix-+ (↑#s-τ (plus #u c) τ))
  where fix-+ = subst (λ s → Type s 0 #x) (sym (plus-S #s #u))
↑#u-τ {#s} {#u} {#x} c (& ℓ m τ) = & ℓ m (fix-+ (↑#s-τ (plus #u c) τ))
  where fix-+ = subst (λ s → Type s 0 #x) (sym (plus-S #s #u))
↑#u-τ c (opt τ) = opt (↑#u-τ c τ)
↑#u-τ c (rec τs) = rec (helper τs)
  where
  helper : ∀ {n} → Vec _ n → Vec _ n
  helper [] = []
  helper (τ ∷ τs′) = ↑#u-τ c τ ∷ helper τs′
↑#u-τ c (μ τ) = μ (↑#u-τ (S c) τ)
↑#u-τ c (var x) = var x

promote-closed : ∀ {#s #u #x} → Type 0 0 #x → Type #s #u #x
promote-closed {#s} {#u} τ = ⇑#s (⇑#u τ)
  where
  ⇑#s = ⇑′ (λ s → Type s #u _) ↑#s-τ #s 0
  ⇑#u = ⇑′ (λ u → Type 0 u _) ↑#u-τ #u 0

μ-subst[s] : ∀ {#s #u #x} → Type 0 0 #x → Type (S #s) #u #x → Type #s #u #x
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

μ-subst[u] : ∀ {#u #x} → Type 0 0 #x → Type 0 (S #u) #x → Type 0 #u #x
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

test-ℕ : Type 0 0 0
test-ℕ = μ (opt (~ (var fZ)))

test-ℕ-unroll : μ-subst[u] {#u = 0} test-ℕ (opt (~ (var fZ)))
              ≡ opt (~ (μ (opt (~ (var fZ)))))
test-ℕ-unroll = refl

data _Copy {#s #u #x} : Type #s #u #x → Set where
  int : int Copy
  &imm : ∀ {ℓ τ} → & ℓ imm τ Copy
  opt : ∀ {τ} → τ Copy → opt τ Copy
  rec : ∀ {n τs} → All _Copy {n} τs → rec τs Copy
  μ : ∀ {τ} → τ Copy → μ τ Copy

data _Move {#s #u #x} : Type #s #u #x → Set where
  ~ : ∀ {τ} → ~ τ Move
  &mut : ∀ {ℓ τ} → & ℓ mut τ Move
  opt : ∀ {τ} → τ Move → opt τ Move
  rec : ∀ {n τs} → Any _Move {n} τs → rec τs Move
  μ : ∀ {τ} → τ Move → μ τ Move

copy×move : ∀ {#s #u #x} (τ : Type #s #u #x) → ¬ (τ Copy × τ Move)
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

copy+move : ∀ {#u #x} (τ : Type 0 #u #x) → τ Copy + τ Move
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

data _Drop {#s #u #x} : Type #s #u #x → Set where
  ~ : ∀ {τ} → ~ τ Drop
  opt : ∀ {τ} → τ Drop → opt τ Drop
  rec : ∀ {n τs} → Any _Drop {n} τs → rec τs Drop
  μ : ∀ {τ} → τ Drop → μ τ Drop

data _Safe {#s #u #x} : Type #s #u #x → Set where
  int : int Safe
  & : ∀ {ℓ m τ} → & ℓ m τ Safe
  opt : ∀ {τ} → τ Safe → opt τ Safe
  rec : ∀ {n τs} → All _Safe {n} τs → rec τs Safe
  μ : ∀ {τ} → τ Safe → μ τ Safe

drop×safe : ∀ {#s #u #x} (τ : Type #s #u #x) → ¬ (τ Drop × τ Safe)
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

drop+safe : ∀ {#u #x} (τ : Type 0 #u #x) → τ Drop + τ Safe
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

data _<:_ {#s #u #x} : Type #s #u #x → Type #s #u #x → Set where
  int : int <: int
  ~ : ∀ {τ₁ τ₂} → τ₁ <: τ₂ → ~ τ₁ <: ~ τ₂
  &imm : ∀ {ℓ₁ ℓ₂ τ₁ τ₂} → ℓ₂ :<: ℓ₁ → τ₁ <: τ₂ → & ℓ₁ imm τ₁ <: & ℓ₂ imm τ₂
  &mut : ∀ {ℓ₁ ℓ₂ τ} → ℓ₂ :<: ℓ₁ → & ℓ₁ mut τ <: & ℓ₂ mut τ
  opt : ∀ {τ₁ τ₂} → τ₁ <: τ₂ → opt τ₁ <: opt τ₂
  rec : ∀ {n τs₁ τs₂} → All2 _<:_ {n} τs₁ τs₂ → rec τs₁ <: rec τs₂
  μ : ∀ {τ₁ τ₂} → τ₁ <: τ₂ → μ τ₁ <: μ τ₂
  var : ∀ {s} → var s <: var s

<:-refl : ∀ {#s #u #x} (τ : Type #s #u #x) → τ <: τ
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

<:-antisym : ∀ {#s #u #x} {τ₁ τ₂ : Type #s #u #x} → τ₁ <: τ₂ → τ₂ <: τ₁ → τ₁ ≡ τ₂
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

<:-trans : ∀ {#s #u #x} {τ₁ τ₂ τ₃ : Type #s #u #x} → τ₁ <: τ₂ → τ₂ <: τ₃ → τ₁ <: τ₃
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
