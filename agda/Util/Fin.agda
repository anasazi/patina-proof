open import Util.Nat
open import Util.Decidable
open import Util.Equality
open import Util.Function
open import Util.Product
open import Util.Bool
module Util.Fin where

data Fin : ℕ → Set where
  fZ : ∀ {n} → Fin (S n)
  fS : ∀ {n} → Fin n → Fin (S n)

fS-inj : ∀ {n} {a b : Fin n} → fS a ≡ fS b → a ≡ b
fS-inj refl = refl

instance
  _=Fin=_ : ∀ {n} (a b : Fin n) → Dec (a ≡ b)
  fZ =Fin= fZ = yes refl
  fZ =Fin= fS b = no (λ ())
  fS a =Fin= fZ = no (λ ())
  fS a =Fin= fS b with a =Fin= b
  fS a =Fin= fS b | yes pf = yes (cong fS pf)
  fS a =Fin= fS b | no ¬pf = no (¬pf ∘ fS-inj)

  EqFin : ∀ {n} → Eq (Fin n)
  EqFin = record { _==_ = _=Fin=_ }

ℕ→Fin : ∀ {m} (n : ℕ) {n<m : IsTrue (lessNat n m)} → Fin m
ℕ→Fin {Z} n {}
ℕ→Fin {S m} Z = fZ
ℕ→Fin {S m} (S n) {n<m} = fS (ℕ→Fin n {n<m})

fin = ℕ→Fin

fin′ : ∀ {m n} (n<m : n < m) → Fin m
fin′ z<s = fZ
fin′ (s<s pf) = fS (fin′ pf)

fin′′ : ∀ {m} (n : ℕ) {n<m : IsYes (n <? m) } → Fin m 
fin′′ _ {pf} = fin′ (toWitness pf)

Fin→ℕ : ∀ {m} → Fin m → ℕ
Fin→ℕ fZ = 0
Fin→ℕ (fS f) = S (Fin→ℕ f)

asℕ = Fin→ℕ

expand : ∀ {n} m → Fin n → Fin (plus n m)
expand m fZ = fZ
expand m (fS f) = fS (expand m f)

expand′ : ∀ {n} m → Fin n → Fin (plus m n)
expand′ {n} m f rewrite plus-comm m n = expand m f

expand-spec : ∀ {n} (f : Fin n) (m : ℕ) → asℕ f ≡ asℕ (expand m f)
expand-spec fZ m = refl
expand-spec (fS f) m rewrite expand-spec f m = refl

raise : ∀ {n} m → Fin n → Fin (plus m n)
raise Z f = f
raise (S m) f = fS (raise m f)

raise′ : ∀ {n} m → Fin n → Fin (plus n m)
raise′ {n} m f rewrite plus-comm n m = raise m f

raise-spec : ∀ {n} (f : Fin n) (m : ℕ) → plus (asℕ f) m ≡ asℕ (raise m f)
raise-spec f Z = plus-0-r (asℕ f)
raise-spec f (S m) rewrite plus-S (asℕ f) m = cong S (raise-spec f m)

fplus : ∀ {m n} → (i : Fin m) → (j : Fin n) → Fin (plus m n)
fplus {S m} fZ j = expand′ (S m) j
fplus {S m} (fS i) j = fS (fplus i j)

fplus′ : ∀ {m n} → (i : Fin m) → (j : Fin n) → Fin (plus n m)
fplus′ {m} {n} i j rewrite plus-comm n m = fplus i j

data f+ : ∀ {i} → Fin (S i) → ℕ → Fin (S i) → Set where
  f+z : ∀ {i f} → f+ {i} f 0 f
  z+s : ∀ {i f n}
      → f+ {i} fZ n f
      → f+ {S i} fZ (S n) (fS f)
  s+s : ∀ {i f n f′}
      → f+ {i} f (S n) f′
      → f+ {S i} (fS f) (S n) (fS f′) 

      {-
data f↑ {i} : Fin (S i) → (n : ℕ) → Fin (S (plus n i)) → Set where
  fZ↑ : ∀ {n} → f↑ fZ n fZ
  fS↑ : ∀ {f n} → f↑ {!!} {!!} {!!} → f↑ (fS f) (S n) {!!}
  -}

private
  open import Util.Empty
  test-f+-1 : f+ {2} fZ 1 (fS fZ)
  test-f+-1 = z+s f+z
  test-f+-2 : f+ {2} fZ 2 (fS (fS fZ)) 
  test-f+-2 = z+s (z+s f+z)
  test-f+-3 : f+ {2} (fS fZ) 1 (fS (fS fZ))
  test-f+-3 = s+s (z+s f+z)

↑ : ∀ {i} → ℕ → Fin i → Fin (S i)
↑ c f with asℕ f <? c
↑ c f | yes f<c = expand′ 1 f
↑ c f | no  f≥c = raise 1 f

{-
↑d : ∀ {i} → (d : ℕ) → ℕ → Fin i → Fin (plus d i)
↑d Z c f = f
↑d (S d) c f = ↑ c (↑d d c f)

↑d-test-1 : ↑d 3 0 (fin {1} 0) ≡ fin {4} 3
↑d-test-1 = refl
↑d-test-2 : ↑d 3 1 (fin {1} 0) ≡ fin {4} 0
↑d-test-2 = refl
↑d-test-3 : ↑d 3 2 (fin {5} 3) ≡ fin {8} 6
↑d-test-3 = refl
-}

⇑ : ∀ {i} (P : ℕ → Set) (f : ∀ {n} → ℕ → P n → P (S n)) → (d : ℕ) → ℕ → P i → P (plus d i)
⇑ P f Z c i = i
⇑ P f (S d) c i = f c (⇑ P f d c i)

⇑′ : ∀ {i} (P : ℕ → Set) (f : ∀ {n} → ℕ → P n → P (S n)) → (d : ℕ) → ℕ → P i → P (plus i d)
⇑′ {i} P f d c pi rewrite plus-comm i d = ⇑ P f d c pi

data ↓ : ∀ {i} → ℕ → Fin (S i) → Fin i → Set where
  Z : ∀ {i c} → ↓ {S i} (S c) fZ fZ
  S< : ∀ {n c f f′} → asℕ (fS f) < S c → ↓ c f f′ → ↓ {S n} (S c) (fS f) (fS f′) 
  S≥ : ∀ {n c f} → asℕ (fS f) ≥ c → ↓ {S n} c (fS f) f

  {-
↑-fin : ∀ {i} → (d : ℕ) → ℕ → Fin i → Fin (plus d i)
↑-fin d c f with asℕ f <? c
↑-fin d c f | yes f<c = expand′ d f
↑-fin d c f | no  f≥c = raise d f

data ↓ : ∀ {n} → Fin (S n) → Fin n → Set where
  S : ∀ {n i} → ↓ {S n} (fS i) i 

test-↓-1 : ↓ {10} (fin 3) (fin 2)
test-↓-1 = S
test-↓-2 : ∀ {n} → ¬ (Σ[ i ∈ Fin n ] ↓ {n} fZ i)
test-↓-2 (i , ())

data ↓c : ∀ {n} → ℕ → Fin (S n) → Fin n → Set where
  Z : ∀ {n c} → ↓c {S n} (S c) fZ fZ
  S< : ∀ {n i c j} → asℕ (fS i) < (S c) → ↓c c i j → ↓c {S n} (S c) (fS i) (fS j)
  S≥ : ∀ {n i c} → asℕ (fS i) ≥ c → ↓c {S n} c (fS i) i

test-↓c-1 : ↓c {10} 1 fZ fZ
test-↓c-1 = Z
test-↓c-2 : ∀ {n} → ¬ (Σ[ i ∈ Fin n ] ↓c 0 fZ i)
test-↓c-2 (i , ())
test-↓c-3 : ↓c {10} 4 (fin 3) (fin 3)
test-↓c-3 = S< (s<s (s<s (s<s z<s))) (S< (s<s (s<s z<s)) (S< (s<s z<s) Z))
test-↓c-4 : ↓c {10} 3 (fin 3) (fin 2)
test-↓c-4 = S≥ (s<s (s<s (s<s z<s)))
test-↓c-5 : ↓c 0 (fin {10} 3) (fin 2)
test-↓c-5 = S≥ z<s
-}
