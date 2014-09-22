open import Common
{-
Lifetimes in Patina are either variables or values.
Variable lifetimes are the lifetime parameters of structs and functions.
Value lifetimes are concrete lifetimes created by blocks or are the static lifetime.

Since value lifetimes are created in a stack, there's a natural total ordering.
The shortest, youngest lifetime is on the top of the stack is less than the other
lifetimes on the stack (and so on). All the lifetimes on the stack are less than static.

How do variable lifetimes fit into this relation?

When lifetime parameters are used in a struct definition, the only concrete lifetime
that can appear is the static lifetime. Static and the variable lifetimes are all
unrelated to eachother, and the only way variables are used here is for substitution,
so the relation is basically irrelevant.

When lifetime parameters are used in a function definition, they occupy a similar role
as the static lifetime does. Any concrete lifetime created in the function's body is certainly
shorter than any lifetime that could be substituted for a parameter.
Thus, we consider any concrete lifetime (sans static) to be less than any lifetime variable.
Static and other lifetime variables are still unrelated to eachother.

If we use De Bruijn indicies for lifetime values (0 refers to the shortest lifetime),
then we can reduce the entire relation to simply two numbers:
1. The number of lifetime values (sans static), which is usually notated #ℓ
2. The number of lifetime variables, which is usually notated #Ł

Lifetime variables are also De Bruijn indicies, but are considered unordered or our purposes.

We index the type of lifetimes (Life) with these two numbers, which encodes the relation.
This has the benefit of making lifetimes correct by construction.
-}
module Life where

-- The type of lifetimes, indexed by:
-- + the number of lifetime values (#ℓ)
-- + the number of lifetime variables (#Ł)
-- which encodes the lifetime relation.
data Life (#x #ℓ : ℕ) : Set where
  -- A lifetime variabel is identified by some element of the finite set of size #Ł
  var : (ℓ : Fin #ℓ) → Life #x #ℓ
  -- The static lifetime is always in scope
  static : Life #x #ℓ
  -- A lifetime value is identified by some element of the finite set of size #ℓ
  val : (x : Fin #x) → Life #x #ℓ

  {-
private
  val-inj : ∀ {#x} {i j : Fin #x} → val i ≡ val j → i ≡ j
  val-inj refl = refl

  _=life=_ : ∀ {#x} → (ℓ₁ ℓ₂ : Life #x) → Dec (ℓ₁ ≡ ℓ₂)
  static =life= static = yes refl
  static =life= val x₂ = no (λ ())
  val x₁ =life= static = no (λ ())
  val x₁ =life= val x₂ with x₁ == x₂
  val x₁ =life= val .x₁ | yes refl = yes refl
  val x₁ =life= val x₂ | no neq = no (neq ∘ val-inj)

EqLife : ∀ {#x} → Eq (Life #x)
EqLife = record { _==_ = _=life=_ }
-}

-- upshifting and downshifting for lifetimes
↑#x-ℓ : ∀ {#x #ℓ} → ℕ → Life #x #ℓ → Life (S #x) #ℓ
--↑#x-ℓ : ∀ {#x} → ℕ → Life #x → Life (S #x)
↑#x-ℓ c static = static
↑#x-ℓ c (val x) = val (↑ c x)
↑#x-ℓ c (var ℓ) = var ℓ

data ↓#x-ℓ {#x #ℓ} : ℕ → Life (S #x) #ℓ → Life #x #ℓ → Set where
--data ↓#x-ℓ {#x} : ℕ → Life (S #x) → Life #x → Set where
  static : ∀ {c} → ↓#x-ℓ c static static
  val : ∀ {c x x′} → ↓ c x x′ → ↓#x-ℓ c (val x) (val x′)
  var : ∀ {c ℓ} → ↓#x-ℓ c (var ℓ) (var ℓ)

↑#ℓ-ℓ : ∀ {#x #ℓ} → ℕ → Life #x #ℓ → Life #x (S #ℓ)
↑#ℓ-ℓ c static = static
↑#ℓ-ℓ c (val x) = val x
↑#ℓ-ℓ c (var ℓ) = var (↑ c ℓ)

  {-
Lifes : ℕ → ℕ → Set
Lifes #ℓ #x = Vec (Life #ℓ) #x
-}

-- The ordering relationship on lifetimes.
data _:<:_ {#x #ℓ : ℕ} : Life #x #ℓ → Life #x #ℓ → Set where
--data _:<:_ {#x : ℕ} : Life #x → Life #x → Set where
  -- The relationship is reflexive for all three constructors
  var-refl : ∀ {ℓ} → var ℓ :<: var ℓ
  static-refl : static :<: static

  var-static : ∀ {ℓ} → var ℓ :<: static
  -- Values are less than both static and any variable
  val-var : ∀ {x ℓ} → val x :<: var ℓ
  val-static : ∀ {x} → val x :<: static
  -- A lower (newer) value is less than a larger (older) value
  val-val : ∀ {ℓ₁ ℓ₂} → asℕ ℓ₁ ≤ asℕ ℓ₂ → val ℓ₁ :<: val ℓ₂

:<:-refl : ∀ {#x #ℓ} (ℓ : Life #x #ℓ) → ℓ :<: ℓ
:<:-refl (var ℓ) = var-refl
:<:-refl static = static-refl
:<:-refl (val x) = val-val (≤-refl (asℕ x))

:<:-antisym : ∀ {#x #ℓ} {ℓ₁ ℓ₂ : Life #x #ℓ} → ℓ₁ :<: ℓ₂ → ℓ₂ :<: ℓ₁ → ℓ₁ ≡ ℓ₂
:<:-antisym var-refl var-refl = refl
:<:-antisym static-refl static-refl = refl
:<:-antisym var-static ()
:<:-antisym val-var ()
:<:-antisym val-static ()
:<:-antisym (val-val x₁≤x₂) (val-val x₂≤x₁) = cong val (asℕ-inj (≤-antisym x₁≤x₂ x₂≤x₁))

:<:-trans : ∀ {#x #ℓ} {ℓ₁ ℓ₂ ℓ₃ : Life #x #ℓ} → ℓ₁ :<: ℓ₂ → ℓ₂ :<: ℓ₃ → ℓ₁ :<: ℓ₃
:<:-trans var-refl var-refl = var-refl
:<:-trans var-refl var-static = var-static
:<:-trans static-refl static-refl = static-refl
:<:-trans var-static static-refl = var-static
:<:-trans val-var var-refl = val-var
:<:-trans val-var var-static = val-static
:<:-trans val-static static-refl = val-static
:<:-trans (val-val x₁≤x₂) val-var = val-var
:<:-trans (val-val x₁≤x₂) val-static = val-static
:<:-trans (val-val x₁≤x₂) (val-val x₂≤x₃) = val-val (≤-trans x₁≤x₂ x₂≤x₃)

  {-
--test-sublife-1 : 0 , 10 ∣ var fZ <: var fZ
--test-sublife-1 = var-refl
--test-sublife-2 : ¬ (0 , 10 ∣ var fZ <: var (fin 1))
--test-sublife-2 ()
test-sublife-3 : static {10} :<: static
test-sublife-3 = static-refl
--test-sublife-4 : ¬ (Z , 10 ∣ static <: var fZ)
--test-sublife-4 ()
--test-sublife-5 : ¬ (Z , 10 ∣ var fZ <: static)
--test-sublife-5 ()
--test-sublife-6 : 10 , 10 ∣ val fZ <: var fZ
--test-sublife-6 = val-var
test-sublife-7 : val {10} fZ :<: static
test-sublife-7 = val-static
--test-sublife-8 : ¬ (10 , 10 ∣ var fZ <: val fZ)
--test-sublife-8 ()
test-sublife-9 : val {10} (fin 3) :<: val (fin 8)
test-sublife-9 = val-val (s<s (s<s (s<s z<s)))
test-sublife-10 : ¬ (val {10} (fin 8) :<: val (fin 3))
test-sublife-10 (val-val (s<s (s<s (s<s (s<s ())))))
-}

subst-ℓ : ∀ {#x #ℓ #ℓ′} → Vec (Life #x #ℓ) #ℓ′ → Life 0 #ℓ′ → Life #x #ℓ
subst-ℓ ℓs (var ℓ) = ℓs ! ℓ
subst-ℓ ℓs static = static
subst-ℓ ℓs (val ())
