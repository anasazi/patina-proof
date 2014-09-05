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
record Bank (#x {- #Ł -} : ℕ) : Set where
  constructor bank
  field
    val-loans : Vec Loan #x
    static-loan : Loan
    --var-loans : ?
open Bank

-- upshift and downshift for loans and banks
↑-#x-ln : ∀ {#x} → (d : ℕ) → ℕ → Vec Loan #x → Vec Loan (plus d #x)
↑-#x-ln d c [] rewrite plus-0-r d = rep free d
↑-#x-ln d Z (ln ∷ lns) = rep free d ++ (ln ∷ lns)
↑-#x-ln {S #x} d (S c) (ln ∷ lns) rewrite plus-S d #x = ln ∷ (↑-#x-ln d c lns)

data ↓1-#x-ln : ∀ {#x} → ℕ → Vec Loan (S #x) → Vec Loan #x → Set where
  Z : ∀ {#x x xs} → ↓1-#x-ln {#x} 0 (x ∷ xs) xs
  S : ∀ {#x c x xs xs′}
    → ↓1-#x-ln {S #x} c xs xs′
    → ↓1-#x-ln (S c) (x ∷ xs) (x ∷ xs′)

↑-#x-b : ∀ {#x} → (d : ℕ) → ℕ → Bank #x → Bank (plus d #x)
↑-#x-b d c (bank val-loans static-loan) = bank (↑-#x-ln d c val-loans) static-loan

↓1-#x-b : ∀ {#x} → ℕ → Bank (S #x) → Bank #x → Set
↓1-#x-b c (bank vals stat) (bank vals′ stat′) = stat ≡ stat′ × ↓1-#x-ln c vals vals′

-- constructs the default Bank (all unborrowed)
bank-def : ∀ #x → Bank #x
bank-def #x = bank (rep free #x) free

-- A predicate on a Bank for whether this path is unborrowed (all loans are free)
record Unborrowed {#x : ℕ} (B : Bank #x) : Set where
  constructor unborrowed
  field
    vals-free : All Free (val-loans B)
    static-free : Free (static-loan B)

record NoMuts {#x} (B : Bank #x) : Set where
  constructor nomuts
  field
    vals-no-muts : All NotMut (val-loans B)
    static-no-mut : NotMut (static-loan B)

-- A predicate for a vector of loans checking whether the most recent loan was immutable
-- (i.e. the path is frozen). Also true if no loans are given out.
data MostRecentBorrowImm : ∀ {#x} → Vec Loan #x → Set where
  [] : MostRecentBorrowImm []
  imm : ∀ {n} {xs : Vec Loan n} → MostRecentBorrowImm (loan imm ∷ xs)
  _∷_ : ∀ {n x} {xs : Vec Loan n}
      → NotMut x
      → MostRecentBorrowImm xs
      → MostRecentBorrowImm (x ∷ xs)

-- A predicate on a Bank for whether a path is readable (not mutably borrowed)
record Readable {#x : ℕ} (B : Bank #x) : Set where
  constructor readable
  field
    vals-not-mut : MostRecentBorrowImm (val-loans B)
    static-not-mut : NotMut (static-loan B)

-- Borrow a path for a given lifetime and mutability (write that mutability into the lifetime slot)
make-loan : ∀ {#x} → Bank #x → Life #x → Mut → Bank #x
make-loan (bank val-loans _) static μ = bank val-loans (loan μ)
make-loan (bank val-loans static-loan) (val ℓ) μ = bank (set val-loans ℓ (loan μ)) static-loan
