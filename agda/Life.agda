open import Common

module Life where

data Life (#ℓ : ℕ) : Set where
  --var : Fin #Ł → Life #ℓ
  static : Life #ℓ
  val : Fin #ℓ → Life #ℓ

data _∣_<:_ (#ℓ : ℕ) : Life #ℓ → Life #ℓ → Set where
  --var-refl : ∀ {Ł} → #ℓ , #Ł ∣ var Ł <: var Ł
  static-refl : #ℓ ∣ static <: static
  --val-var : ∀ {ℓ Ł} → #ℓ , #Ł ∣ val ℓ <: var Ł
  val-static : ∀ {ℓ} → #ℓ  ∣ val ℓ <: static
  val-val : ∀ {ℓ₁ ℓ₂} → asℕ ℓ₁ ≤ asℕ ℓ₂ → #ℓ ∣ val ℓ₁ <: val ℓ₂

--test-sublife-1 : 0 , 10 ∣ var fZ <: var fZ
--test-sublife-1 = var-refl
--test-sublife-2 : ¬ (0 , 10 ∣ var fZ <: var (fin 1))
--test-sublife-2 ()
test-sublife-3 : Z ∣ static <: static
test-sublife-3 = static-refl
--test-sublife-4 : ¬ (Z , 10 ∣ static <: var fZ)
--test-sublife-4 ()
--test-sublife-5 : ¬ (Z , 10 ∣ var fZ <: static)
--test-sublife-5 ()
--test-sublife-6 : 10 , 10 ∣ val fZ <: var fZ
--test-sublife-6 = val-var
test-sublife-7 : 10 ∣ val fZ <: static
test-sublife-7 = val-static
--test-sublife-8 : ¬ (10 , 10 ∣ var fZ <: val fZ)
--test-sublife-8 ()
test-sublife-9 : 10 ∣ val (fin 3) <: val (fin 8)
test-sublife-9 = val-val (s<s (s<s (s<s z<s)))
test-sublife-10 : ¬ (10 ∣ val (fin 8) <: val (fin 3))
test-sublife-10 (val-val (s<s (s<s (s<s (s<s ())))))
