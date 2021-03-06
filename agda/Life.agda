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
data Life (#x : ℕ) : Set where
  -- A lifetime variabel is identified by some element of the finite set of size #Ł
  --var : Fin #Ł → Life #ℓ
  -- The static lifetime is always in scope
  static : Life #x
  -- A lifetime value is identified by some element of the finite set of size #ℓ
  val : Fin #x → Life #x

private
  val-inj : ∀ {#x} {i j : Fin #x} → val i ≡ val j → i ≡ j
  val-inj refl = refl

instance
  _=life=_ : ∀ {#x} → (ℓ₁ ℓ₂ : Life #x) → Dec (ℓ₁ ≡ ℓ₂)
  static =life= static = yes refl
  static =life= val x₂ = no (λ ())
  val x₁ =life= static = no (λ ())
  val x₁ =life= val x₂ with x₁ == x₂
  val x₁ =life= val .x₁ | yes refl = yes refl
  val x₁ =life= val x₂ | no neq = no (neq ∘ val-inj)

  EqLife : ∀ {#x} → Eq (Life #x)
  EqLife = record { _==_ = _=life=_ }

-- upshifting and downshifting for lifetimes
↑#x-ℓ : ∀ {#x} → ℕ → Life #x → Life (S #x)
↑#x-ℓ c static = static
↑#x-ℓ c (val x) = val (↑ c x)

data ↓#x-ℓ {#x} : ℕ → Life (S #x) → Life #x → Set where
  static : ∀ {c} → ↓#x-ℓ c static static
  val : ∀ {c x x′} → ↓ c x x′ → ↓#x-ℓ c (val x) (val x′)

  {-
Lifes : ℕ → ℕ → Set
Lifes #ℓ #x = Vec (Life #ℓ) #x
-}

-- The ordering relationship on lifetimes.
data _:<:_ {#x : ℕ} : Life #x → Life #x → Set where
  -- The relationship is reflexive for all three constructors
  --var-refl : ∀ {Ł} → #ℓ , #Ł ∣ var Ł <: var Ł
  static-refl : static :<: static
  -- Values are less than both static and any variable
  --val-var : ∀ {ℓ Ł} → #ℓ , #Ł ∣ val ℓ <: var Ł
  val-static : ∀ {x} → val x :<: static
  -- A lower (newer) value is less than a larger (older) value
  val-val : ∀ {ℓ₁ ℓ₂} → asℕ ℓ₁ ≤ asℕ ℓ₂ → val ℓ₁ :<: val ℓ₂

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
