open import Common
open import Life
open import Mut
{-
A Bank represents the loan state *for a particular Path*.
It's represented as a mapping from lifetimes to Free/Mut/Imm.

We need only record one loan type per lifetime b/c reborrowing at the same lifetime
is a monotonic operation (free -> mut -> imm).

Although this format does have a lot of unnecessary frees,
it makes adding, writing to, and removing lifetimes very easy.
-}
module Loan where

-- A Loan is basically a Maybe Mut
data Loan : Set where
  free : Loan
  loan : Mut → Loan

-- A predicate for whether a Loan is free
data Free : Loan → Set where
  free : Free free

-- A predicate for whether a Loan is not Mut
data NotMut : Loan → Set where
  free : NotMut free
  imm : NotMut (loan imm)

-- The set of loan information for a particular path
record Bank (#ℓ {- #Ł -} : ℕ) : Set where
  constructor bank
  field
    val-loans : Vec Loan #ℓ
    static-loan : Loan
    --var-loans : ?
open Bank

-- upshift and downshift for loans and banks
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

-- constructs the default Bank (all unborrowed)
bank-def : ∀ #ℓ → Bank #ℓ
bank-def #ℓ = bank (rep free #ℓ) free

-- A predicate on a Bank for whether this path is unborrowed (all loans are free)
record Unborrowed {#ℓ : ℕ} (B : Bank #ℓ) : Set where
  constructor unborrowed
  field
    vals-free : All Free (val-loans B)
    static-free : Free (static-loan B)

record NoMuts {#ℓ} (B : Bank #ℓ) : Set where
  constructor nomuts
  field
    vals-no-muts : All NotMut (val-loans B)
    static-no-mut : NotMut (static-loan B)

-- A predicate for a vector of loans checking whether the most recent loan was immutable
-- (i.e. the path is frozen). Also true if no loans are given out.
data MostRecentBorrowImm : ∀ {#ℓ} → Vec Loan #ℓ → Set where
  [] : MostRecentBorrowImm []
  imm : ∀ {n} {xs : Vec Loan n} → MostRecentBorrowImm (loan imm ∷ xs)
  _∷_ : ∀ {n x} {xs : Vec Loan n}
      → NotMut x
      → MostRecentBorrowImm xs
      → MostRecentBorrowImm (x ∷ xs)

-- A predicate on a Bank for whether a path is readable (not mutably borrowed)
record Readable {#ℓ : ℕ} (B : Bank #ℓ) : Set where
  constructor readable
  field
    vals-not-mut : MostRecentBorrowImm (val-loans B)
    static-not-mut : NotMut (static-loan B)

-- Borrow a path for a given lifetime and mutability (write that mutability into the lifetime slot)
make-loan : ∀ {#ℓ} → Bank #ℓ → Life #ℓ → Mut → Bank #ℓ
make-loan (bank val-loans _) static μ = bank val-loans (loan μ)
make-loan (bank val-loans static-loan) (val ℓ) μ = bank (set val-loans ℓ (loan μ)) static-loan
