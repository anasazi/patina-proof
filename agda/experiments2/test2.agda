open import Common
open import Life
open import Mut
module test2 where

data Safe : Set where
  safe : Safe
  unsafe : Safe

data IsSafe : Safe → Set where
  safe : IsSafe safe

safe? : (s : Safe) → Dec (IsSafe s)
safe? safe = yes safe
safe? unsafe = no (λ ())

resetSafe : (#s : ℕ) → Vec Safe #s
resetSafe #s = rep safe #s

data Var : Set where
  cov : Var
  con : Var
  inv : Var

data _var-≤_ : Var → Var → Set where
  refl : ∀ {v} → v var-≤ v
  cov : inv var-≤ cov
  con : inv var-≤ con

data _⊢_var-≤_ {#x #ℓ} (Ł : Vec Var #ℓ) : Life #x #ℓ → Var → Set where
  val : ∀ {x v} → Ł ⊢ val x var-≤ v
  static : ∀ {v} → Ł ⊢ static var-≤ v
  var : ∀ {ℓ v} → (Ł ! ℓ) var-≤ v → Ł ⊢ var ℓ var-≤ v

data _⊢_var-=_ {#x #ℓ} (Ł : Vec Var #ℓ) : Life #x #ℓ → Var → Set where
  val : ∀ {x v} → Ł ⊢ val x var-= v
  static : ∀ {v} → Ł ⊢ static var-= v
  var : ∀ {ℓ v} → (Ł ! ℓ) ≡ v → Ł ⊢ var ℓ var-= v

var-¬ : Var → Var
var-¬ cov = con
var-¬ con = cov
var-¬ inv = inv

_⊙_ : Var → Var → Var
cov ⊙ v = v
con ⊙ v = var-¬ v
inv ⊙ v = inv

data Type {#s} (#x #ℓ : ℕ) (Ł : Vec Var #ℓ) (K : Vec ℕ #s) (Φ : Vec Safe #s) : Var → Set where
  int : ∀ {v} → Type #x #ℓ Ł K Φ v
  ~ : ∀ {v} → Type #x #ℓ Ł K (resetSafe #s) v → Type #x #ℓ Ł K Φ v
  &imm : ∀ {v}
       → (ℓ : Life #x #ℓ) → Ł ⊢ ℓ var-≤ var-¬ v
       → Type #x #ℓ Ł K (resetSafe #s) (var-¬ v)
       → Type #x #ℓ Ł K Φ v
  &mut : ∀ {v}
       → (ℓ : Life #x #ℓ) → Ł ⊢ ℓ var-≤ var-¬ v
       → Type #x #ℓ Ł K (resetSafe #s) inv
       → Type #x #ℓ Ł K Φ v
  opt : ∀ {v} → Type #x #ℓ Ł K Φ v → Type #x #ℓ Ł K Φ v
  rec : ∀ {#params #fields v}
      → (Łs : Vec Var #params)
      → Vec (Type 0 #params Łs (#params ∷ K) (unsafe ∷ Φ) cov) #fields
      → (ℓs : Vec (Life #x #ℓ) #params)
      → All2 (λ v′ ℓ → Ł ⊢ ℓ var-= (v ⊙ v′)) Łs ℓs
      → Type #x #ℓ Ł K Φ v
  name : ∀ {v} → (s : Fin #s) → IsSafe (Φ ! s) → Vec (Life #x #ℓ) (K ! s) → Type #x #ℓ Ł K Φ v

subst-τ : ∀ {#s #x #ℓ #params Ł K Φ v}
        → Vec (Life #x #ℓ) #params
        → (Ł′ : Vec Var #ℓ)
        → Type {#s} 0 #params Ł K Φ v
        → Type #x #ℓ Ł′ K Φ v
subst-τ ℓs Ł′ int = int
subst-τ ℓs Ł′ (~ τ) = ~ (subst-τ ℓs Ł′ τ)
subst-τ ℓs Ł′ (&imm ℓ pf τ) = &imm (subst-ℓ ℓ ℓs) {!!} (subst-τ ℓs Ł′ τ)
subst-τ ℓs Ł′ (&mut ℓ pf τ) = &mut (subst-ℓ ℓ ℓs) {!!} (subst-τ ℓs Ł′ τ)
subst-τ ℓs Ł′ (opt τ) = opt (subst-τ ℓs Ł′ τ)
subst-τ ℓs Ł′ (rec Łs τs ℓs′ pfs) = rec Łs τs {!!} {!!}
subst-τ ℓs Ł′ (name s pf ℓs′) = name {!!} {!!} {!!}

srs-A : Type 0 0 [] [] [] cov
srs-A = rec [] ([ int ]) [] []

srs-B : Type 0 0 [] [] [] cov
srs-B = rec ([ con ]) ([ int ,, &mut (var fZ) (var refl) int ]) ([ static ]) (static ∷ [])

srs-C : Type 0 0 [] [] [] cov
srs-C = rec ([ con ])
            ([ rec [] ([ int ]) [] []
            ,, rec ([ con ]) ([ int ,, &mut (var fZ) (var refl) int ]) ([ var fZ ]) (var refl ∷ []) ])
            ([ static ])
            (static ∷ [])

srs-List : Type 0 0 [] [] [] cov
srs-List = rec [] ([ int ,, opt (~ (name fZ safe [])) ]) [] []

srs-F-⊤ : Type 0 0 [] [] [] cov
srs-F-⊤ = rec ([ con ])
              ([ rec ([ con ])
                     ([ int ,, &mut (var fZ) (var refl) int ])
                     ([ var fZ ])
                     (var refl ∷ []) ])
              ([ static ])
              (static ∷ [])

record Struct : Set where
  constructor struct
  field
    {#s} : ℕ
    kinds : Vec ℕ #s
    safes : Vec Safe #s
    {#params #fields} : ℕ
    params : Vec Var #params
    fields : Vec (Type 0 #params params (#params ∷ kinds) (unsafe ∷ safes) cov) #fields

name-field-types : ∀ {#s #x #ℓ} (§ : Vec Struct #s) (s : Fin #s)
                 → Vec (Life #x #ℓ) (Struct.#params (§ ! s))
                 → (Ł : Vec Var #ℓ)
                 → (K : Vec ℕ #s)
                 → (Φ : Vec Safe #s)
                 → Vec (Type #x #ℓ Ł K Φ cov) (Struct.#fields (§ ! s))
name-field-types § s ℓs Ł K Φ = map {!!} (Struct.fields (§ ! s))

data _⊢_Copy {#s #x #ℓ Ł K Φ v} (§ : Vec Struct #s) : Type {#s} #x #ℓ Ł K Φ v → Set where
  int : § ⊢ int Copy
  &imm : ∀ {ℓ pf τ} → § ⊢ &imm ℓ pf τ Copy
  opt : ∀ {τ} → § ⊢ τ Copy → § ⊢ opt τ Copy
  rec : ∀ {#Ł #f Łs τs ℓs pfs}
      → All (λ τ → (struct K Φ Łs τs ∷ §) ⊢ τ Copy) τs
      → § ⊢ rec {#params = #Ł} {#fields = #f} Łs τs ℓs pfs Copy
  name : ∀ {s pf ℓs}
       -- drop prefix from § ?
       --→ All (λ τ → {!!} ⊢ τ Copy) (Struct.fields (§ ! s))
       -- shift up τ to accomadate new structs?
       → All (λ τ → § ⊢ {!!} Copy) (Struct.fields (§ ! s))
       → § ⊢ name s pf ℓs Copy

data _⊢_Affine {#s #x #ℓ Ł K Φ v} (§ : Vec Struct #s) : Type {#s} #x #ℓ Ł K Φ v → Set where
  ~aff : ∀ {τ} → § ⊢ ~ τ Affine
  &mut : ∀ {ℓ pf τ} → § ⊢ &mut ℓ pf τ Affine
  opt : ∀ {τ} → § ⊢ τ Affine → § ⊢ opt τ Affine
  rec : ∀ {#Ł #f Łs τs ℓs pfs}
      → Any (λ τ → (struct K Φ Łs τs ∷ §) ⊢ τ Affine) τs
      → § ⊢ rec {#params = #Ł} {#fields = #f} Łs τs ℓs pfs Affine
  name : ∀ {s pf ℓs}
       → Any {!!} (Struct.fields (§ ! s))
       → § ⊢ name s pf ℓs Affine
