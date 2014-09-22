open import Common
open import Life
open import Mut

module test where

data Safe : Set where
  safe : Safe
  unsafe : Safe

data IsSafe : Safe → Set where
  safe : IsSafe safe

resetSafe : (#s : ℕ) → Vec Safe #s
resetSafe #s = rep safe #s

data _suff-for_ : Safe → Safe → Set where
  safe : ∀ {s} → safe suff-for s
  unsafe : unsafe suff-for unsafe

_sufficient-for_ : ∀ {n} → Vec Safe n → Vec Safe n → Set
xs sufficient-for ys = All2 _suff-for_ xs ys

data Var : Set where
  cov : Var
  con : Var
  inv : Var

data Type {#s} (#x #ℓ : ℕ) (Φ : Vec Safe #s) : Set where
  int : Type #x #ℓ Φ
  ~ : Type #x #ℓ (resetSafe #s) → Type #x #ℓ Φ
  & : Life #x #ℓ → Mut → Type #x #ℓ (resetSafe #s) → Type #x #ℓ Φ
  opt : Type #x #ℓ Φ → Type #x #ℓ Φ
  struct : ∀ {n} → (s : Fin #s) → IsSafe (Φ ! s) → Vec (Life #x #ℓ) n → Type #x #ℓ Φ

record Struct (#s : ℕ) : Set where
  constructor struct
  field
    {#params #fields} : ℕ
    params : Vec Var #params
    env : Vec Safe #s
    fields : Vec (Type 0 #params env) #fields

data _⊢_type {#s} (srs : Vec (Struct #s) #s) {#x #ℓ} {Φ : Vec Safe #s} : Type #x #ℓ Φ → Set where
  int : srs ⊢ int type
  ~ : ∀ {τ} → srs ⊢ τ type → srs ⊢ ~ τ type
  & : ∀ {ℓ μ τ} → srs ⊢ τ type → srs ⊢ & ℓ μ τ type
  opt : ∀ {τ} → srs ⊢ τ type → srs ⊢ opt τ type
  struct : ∀ {s} {ℓs : Vec (Life #x #ℓ) (Struct.#params (srs ! s))}
         → (pf : IsSafe (Φ ! s))
         → srs ⊢ struct s pf ℓs type

         {-
⊢_structs : ∀ {#s} → Vec (Struct #s) #s → Set
⊢_structs srs = ∀ s → Struct.env (srs ! s) ! s ≡ unsafe
                    × All (λ τ → srs ⊢ τ type) (Struct.fields (srs ! s))
                    -}
record ⊢_structs {#s} (srs : Vec (Struct #s) #s) : Set where
  constructor structs-ok
  field
    self-unsafe : ∀ s → Struct.env (srs ! s) ! s ≡ unsafe
    fields-ok : ∀ s → All (λ τ → srs ⊢ τ type) (Struct.fields (srs ! s))

srs-fail : Vec (Struct 2) 2
srs-fail = [  struct [] ([ unsafe ,, safe ]) ([ struct (fin 1) safe [] ])
           ,, struct [] ([ safe ,, unsafe ]) ([ struct (fin 0) safe [] ])
           ]

srs-fail-pf : ¬ ⊢ srs-fail structs
srs-fail-pf (structs-ok self-unsafe fields-ok) = {!!}

--data Struct {#s} : (Φ : Vec Safe #s) → Set
--data Struct {#s} (Φ : Vec Safe #s) (Ł : Vec ℕ #s) (#ℓ : ℕ) : Set

--data Struct {#s} : Vec Safe #s → Set

{-
record Struct (#s : ℕ) : Set

data Type {#s} (#x #ℓ : ℕ) (Φ : Vec Safe #s) (srs : Vec {!!} #s) : Set
--data Type {#s} (#x #ℓ : ℕ) (Φ : Vec Safe #s) (srs : Vec (Σ Vec Safe #s ** (λ Φ′ → Struct Φ′)) #s) : Set

record Struct #s where
  constructor struct
  field
    {#params #fields} : ℕ
    Φ : Vec Safe #s
    params : Vec Var #params
    fields : Vec (Type 0 #params (unsafe ∷ Φ) ({!!} ∷ {!!})) #fields
open Struct

data Type {#s} #x #ℓ Φ srs where
  int : Type #x #ℓ Φ srs
  ~ : Type #x #ℓ (resetSafe #s) srs → Type #x #ℓ Φ srs
  & : Life #x #ℓ → Mut → Type #x #ℓ (resetSafe #s) srs → Type #x #ℓ Φ srs
  opt : Type #x #ℓ Φ srs → Type #x #ℓ Φ srs
-}
--  rec : (sr : Struct Φ) → Vec (Life #x #ℓ) (#params sr) → Type #x #ℓ Φ
--  struct : Struct Φ → Vec {!!} {!!} → Type #x #ℓ Φ
  -- structural, track Vec (Σ (Vec Safe #s) ** (Vec Var ℓ × Vec (Type 0 ℓ (unsafe ∷ Φ) (ℓ ∷ Ł))))
  -- when using name, check that current environment is sufficient for recorded environment
  -- then unroll by promoting the recorded types
  {-
  name : (s : Fin #s) → IsSafe (Φ ! s) → Vec (Life #x #ℓ) (Ł ! s) → Type #x #ℓ Φ Ł
  rec : ∀ {ℓ n}
      → Vec Var ℓ
      → Vec (Type 0 ℓ (unsafe ∷ Φ) (ℓ ∷ Ł)) n
      → Vec (Life #x #ℓ) ℓ
      → Type #x #ℓ Φ Ł
      -}
--  struct : ∀ {#ℓ′} → Struct Φ Ł #ℓ′ → Vec (Life #x #ℓ) #ℓ′ → Type #x #ℓ Φ Ł
 -- struct : Struct Φ → Vec (Life #x #ℓ) {!Ł ! !} → Type #x #ℓ Φ Ł

 {-
record StructRec (#s : ℕ) : Set where
  constructor struct
  field
    {#params #fields} : ℕ
    params : Vec Var #params
    env : Vec Safe #s
    fields : Vec (Type 0 #params env) #fields

data Struct {#s} where
  name : ∀ {Φ} → (s : Fin #s) → IsSafe (Φ ! s) → {!!} → Struct Φ
  rec : ∀ {Φ} → StructRec #s → {!!} → Struct Φ
  -}

 {-
record Struct {#s} (Φ : Vec Safe #s) : Set
record Struct {#s} Φ where
  constructor struct
  field
    {#params #fields} : ℕ
    params : Vec Var #params
    fields : Vec (Type 0 #params (unsafe ∷ Φ)) #fields
    -}

 {-
data Struct {#s} (Φ : Vec Safe #s) (Ł : Vec ℕ #s) #ℓ where
  name : (s : Fin #s) → IsSafe (Φ ! s) → Ł ! s ≡ #ℓ → Struct Φ Ł #ℓ
  rec : ∀ {n} → Vec Var #ℓ → Vec (Type 0 #ℓ (unsafe ∷ Φ) (#ℓ ∷ Ł)) n → Struct Φ Ł #ℓ
  -}

  {-
data Struct {#s} where
  name : ∀ {Φ} → (s : Fin #s) → IsSafe (Φ ! s) → Struct Φ
  rec : ∀ {Φ ℓ n} → Vec Var ℓ → Vec (Type 0 ℓ (unsafe ∷ Φ) {!!}) n → Struct Φ
  -}

  {-
srs-A : Type 0 0 [] []
srs-A = struct (rec [] ([ int ])) []

srs-B : Type 0 0 [] []
srs-B = struct (rec ([ con ]) ([ int ,, & (var fZ) mut int ])) ([ static ])

srs-C : Type 0 0 [] []
srs-C = struct (rec ([ con ])
                    ([ struct (rec [] ([ int ])) []
                    ,, struct (rec ([ con ]) ([ int ,, & (var fZ) mut int ])) ([ var fZ ]) ]))
               ([ static ])

srs-E : Type 0 0 [] []
srs-E = struct (rec [] ([ ~ int ])) []

srs-List : Type 0 0 [] []
srs-List = struct (rec [] ([ int ,, opt (~ (struct (name fZ safe refl) [])) ])) []
-}

  {-
srs-A : Struct 0 []
srs-A = rec ([ int ])

srs-B : Struct 0 []
srs-B = rec ([ int ,, & static mut int ])

srs-C : Struct 0 []
srs-C = rec ([ struct (rec ([ int ]))
            ,, struct (rec ([ int ,, & static mut int ])) ])

srs-E : Struct 0 []
srs-E = rec ([ ~ int ])

srs-List : Struct 0 []
srs-List = rec ([ int ,, opt (~ (struct (name fZ safe))) ])
-}
