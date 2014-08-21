open import Common
open import Life
open import Mut
module Loan where

data Loan : Set where
  free : Loan
  loan : Mut → Loan

data Free : Loan → Set where
  free : Free free

data NotMut : Loan → Set where
  free : NotMut free
  imm : NotMut (loan imm)

record Bank (#ℓ {- #Ł -} : ℕ) : Set where
  constructor bank
  field
    val-loans : Vec Loan #ℓ
    static-loan : Loan
    --var-loans : ?
open Bank

↑-#ℓ-ln : ∀ {#ℓ} → (d : ℕ) → ℕ → Vec Loan #ℓ → Vec Loan (plus d #ℓ)
↑-#ℓ-ln d c [] rewrite plus-0-r d = rep free d
↑-#ℓ-ln d Z (ln ∷ lns) = rep free d ++ (ln ∷ lns)
↑-#ℓ-ln {S #ℓ} d (S c) (ln ∷ lns) rewrite plus-S d #ℓ = ln ∷ (↑-#ℓ-ln d c lns)

data ↓1-#ℓ-ln : ∀ {#ℓ} → ℕ → Vec Loan (S #ℓ) → Vec Loan #ℓ → Set where
  Z : ∀ {#ℓ x xs} → ↓1-#ℓ-ln {#ℓ} 0 (x ∷ xs) xs
  S : ∀ {#ℓ c x xs xs′}
    → ↓1-#ℓ-ln {S #ℓ} c xs xs′
    → ↓1-#ℓ-ln (S c) (x ∷ xs) (x ∷ xs′)

↑-#ℓ-b : ∀ {#ℓ} → (d : ℕ) → ℕ → Bank #ℓ → Bank (plus d #ℓ)
↑-#ℓ-b d c (bank val-loans static-loan) = bank (↑-#ℓ-ln d c val-loans) static-loan

↓1-#ℓ-b : ∀ {#ℓ} → ℕ → Bank (S #ℓ) → Bank #ℓ → Set
↓1-#ℓ-b c (bank vals stat) (bank vals′ stat′) = stat ≡ stat′ × ↓1-#ℓ-ln c vals vals′

data MostRecentBorrowImm : ∀ {#ℓ} → Vec Loan #ℓ → Set where
  [] : MostRecentBorrowImm []
  imm : ∀ {n} {xs : Vec Loan n} → MostRecentBorrowImm (loan imm ∷ xs)
  _∷_ : ∀ {n x} {xs : Vec Loan n}
      → NotMut x
      → MostRecentBorrowImm xs
      → MostRecentBorrowImm (x ∷ xs)

record Unborrowed {#ℓ : ℕ} (B : Bank #ℓ) : Set where
  constructor unborrowed
  field
    vals-free : All Free (val-loans B)
    static-free : Free (static-loan B)

bank-def : ∀ #ℓ → Bank #ℓ
bank-def #ℓ = bank (rep free #ℓ) free

record Readable {#ℓ : ℕ} (B : Bank #ℓ) : Set where
  constructor readable
  field
    vals-not-mut : MostRecentBorrowImm (val-loans B)
    static-not-mut : NotMut (static-loan B)

borrow : ∀ {#ℓ} → Bank #ℓ → Life #ℓ → Mut → Bank #ℓ
borrow (bank val-loans _) static μ = bank val-loans (loan μ)
borrow (bank val-loans static-loan) (val ℓ) μ = bank (set val-loans ℓ (loan μ)) static-loan
