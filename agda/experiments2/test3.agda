open import Common
open import Life
open import Mut
module test3 where

data Safe : Set where
  safe : Safe
  unsafe : Safe

data _suff-for_ : Safe → Safe → Set where
  safe : ∀ {s} → safe suff-for s
  unsafe : unsafe suff-for unsafe

data Var : Set where
  cov : Var
  con : Var
  inv : Var

data Type (#s #x #ℓ : ℕ) : Set where
  int : Type #s #x #ℓ
  ~ : Type #s #x #ℓ → Type #s #x #ℓ
  & : Life #x #ℓ → Mut → Type #s #x #ℓ → Type #s #x #ℓ
  opt : Type #s #x #ℓ → Type #s #x #ℓ
  struct : ∀ {n} → Fin #s → Vec (Life #x #ℓ) n → Type #s #x #ℓ

record Struct (#s : ℕ) : Set where
  constructor struct
  field
    {#ℓ n} : ℕ
    params : Vec Var #ℓ
    env : Vec Safe #s
    fields : Vec (Type #s 0 #ℓ) n

Structs : ℕ → Set
Structs #s = Vec (Struct #s) #s

Safes : ℕ → Set
Safes #s = Vec Safe #s

_all-suff-for_ : ∀ {#s} → Safes #s → Safes #s → Set
xs all-suff-for ys = All2 _suff-for_ xs ys

reset : (#s : ℕ) → Safes #s
reset #s = rep safe #s 

data _,_⊢_type {#s} (§ : Structs #s) (Φ : Safes #s) {#x #ℓ} : Type #s #x #ℓ → Set where
  int : § , Φ ⊢ int type
  ~ : ∀ {τ} → § , reset #s ⊢ τ type → § , Φ ⊢ ~ τ type
  & : ∀ {ℓ μ τ} → § , reset #s ⊢ τ type → § , Φ ⊢ & ℓ μ τ type
  opt : ∀ {τ} → § , Φ ⊢ τ type → § , Φ ⊢ opt τ type
  struct : ∀ {s ℓs}
         → Φ all-suff-for Struct.env (§ ! s)
         → § , Φ ⊢ struct {n = Struct.#ℓ (§ ! s)} s ℓs type

record _⊢_struct {#s} (§ : Structs #s) (s : Fin #s) : Set where
  constructor struct-ok
  field
    self-safe : Struct.env (§ ! s) ! s ≡ safe
    fields-ok : All (λ τ → § , set (Struct.env (§ ! s)) s unsafe ⊢ τ type) (Struct.fields (§ ! s))
open _⊢_struct

⊢_structs : ∀ {#s} → Structs #s → Set
⊢ § structs = All (λ s → § ⊢ s struct) (range′ _)

srs : Structs 5
srs = [  struct [] ([ safe ,, unsafe ,, unsafe ,, unsafe ,, unsafe ]) ([ int ])
      ,, struct ([ con ]) ([ unsafe ,, safe ,, unsafe ,, unsafe ,, unsafe ])
                ([ int ,, & (var fZ) mut int ])
      ,, struct ([ con ]) ([ safe ,, safe ,, safe ,, unsafe ,, unsafe ])
                ([ struct (fin 0) [] ,, struct (fin 1) ([ var fZ ]) ])
      ,, struct ([ con ]) ([ safe ,, safe ,, safe ,, safe ,, unsafe ])
                ([ struct (fin 2) ([ var fZ ]) ,, struct (fin 0) []
                ,, struct (fin 2) ([ var fZ ]) ,, struct (fin 1) ([ var fZ ]) ])
      ,, struct [] ([ unsafe ,, unsafe ,, unsafe ,, unsafe ,, safe ]) ([ ~ int ]) 
      ]

srs-ok : ⊢ srs structs
srs-ok = struct-ok refl (int ∷ [])
       ∷ struct-ok refl (int ∷ & int ∷ [])
       ∷ struct-ok refl (struct (safe ∷ safe ∷ unsafe ∷ unsafe ∷ unsafe ∷ [])
                       ∷ struct (safe ∷ safe ∷ unsafe ∷ unsafe ∷ unsafe ∷ [])
                       ∷ [])
       ∷ struct-ok refl (struct (safe ∷ safe ∷ safe ∷ unsafe ∷ unsafe ∷ [])
                       ∷ struct (safe ∷ safe ∷ safe ∷ unsafe ∷ unsafe ∷ [])
                       ∷ struct (safe ∷ safe ∷ safe ∷ unsafe ∷ unsafe ∷ [])
                       ∷ struct (safe ∷ safe ∷ safe ∷ unsafe ∷ unsafe ∷ [])
                       ∷ [])
       ∷ struct-ok refl (~ int ∷ [])
       ∷ []

list : Structs 1
list = struct [] (safe ∷ []) ([ int ,, opt (~ (struct fZ [])) ]) ∷ []

list-ok : ⊢ list structs
list-ok = struct-ok refl (int ∷ opt (~ (struct (safe ∷ []))) ∷ []) ∷ []

infin : Structs 1
infin = struct [] (safe ∷ []) ([ struct fZ [] ]) ∷ []

infin-¬ok : ¬ (⊢ infin structs)
infin-¬ok (struct-ok refl (struct (() ∷ []) ∷ []) ∷ [])

mutinfin : Structs 2
mutinfin = [  struct [] ([ safe ,, safe ]) ([ struct (fin 1) [] ])
           ,, struct [] ([ safe ,, safe ]) ([ struct (fin 0) [] ])
           ]

mutinfin-¬ok : ¬ (⊢ mutinfin structs)
mutinfin-¬ok (struct-ok refl (struct (() ∷ x₁) ∷ []) ∷ x₂ ∷ [])

data _⊢_Copy {#s #x #ℓ} (§ : Structs #s) : Type #s #x #ℓ → Set where
  int : § ⊢ int Copy
  &imm : ∀ {ℓ τ} → § ⊢ & ℓ imm τ Copy
  opt : ∀ {τ} → § ⊢ τ Copy → § ⊢ opt τ Copy
  struct : ∀ {s ℓs}
         → All (λ τ → § ⊢ τ Copy) (Struct.fields (§ ! s))
         → § ⊢ struct {n = Struct.#ℓ (§ ! s)} s ℓs Copy

data _⊢_Affine {#s #x #ℓ} (§ : Structs #s) : Type #s #x #ℓ → Set where
  ~Aff : ∀ {τ} → § ⊢ ~ τ Affine
  &mut : ∀ {ℓ τ} → § ⊢ & ℓ mut τ Affine
  opt : ∀ {τ} → § ⊢ τ Affine → § ⊢ opt τ Affine
  struct : ∀ {s ℓs}
         → Any (λ τ → § ⊢ τ Affine) (Struct.fields (§ ! s))
         → § ⊢ struct {n = Struct.#ℓ (§ ! s)} s ℓs Affine

cop-aff-dis : ∀ {#s #x #ℓ} (§ : Structs #s) (Φ : Safes #s) (τ : Type #s #x #ℓ)
            → ⊢ § structs
            → § , Φ ⊢ τ type
            → ¬ (§ ⊢ τ Copy × § ⊢ τ Affine)
cop-aff-dis § Φ .int H§ int (cop , ())
cop-aff-dis § Φ ._ H§ (~ Hτ) (() , aff)
cop-aff-dis § Φ ._ H§ (& Hτ) (&imm , ())
cop-aff-dis § Φ ._ H§ (opt Hτ) (opt cop , opt aff) = cop-aff-dis § Φ _ H§ Hτ (cop , aff)
cop-aff-dis § Φ (struct s ℓs) H§ (struct suff) (struct all-cop , struct any-aff) =
  handle-fields (set (Struct.env (§ ! s)) s unsafe)
                (Struct.fields (§ ! s))
                (subst
                   (λ s′ →
                      All (_,_⊢_type § (set (Struct.env (§ ! s′)) s′ unsafe))
                      (Struct.fields (§ ! s′)))
                   (range′-spec s) (fields-ok (H§ All! s)))
                (all-cop , any-aff)
  where
  handle-fields : ∀ {#ℓ′ n} (Φ : Safes _) (τs : Vec (Type _ 0 #ℓ′) n)
                → All (λ τ → § , Φ ⊢ τ type) τs
                → ¬ (All (_⊢_Copy §) τs × Any (_⊢_Affine §) τs)
  handle-fields Φ′ [] Hτs (cop , ())
  handle-fields Φ′ (τ ∷ _) (Hτ ∷ _) ((cop ∷ _) , Z aff) = cop-aff-dis § Φ′ τ H§ Hτ (cop , aff)
  handle-fields Φ′ (_ ∷ τs) (_ ∷ Hτs) ((_ ∷ cop) , S aff) = handle-fields Φ′ τs Hτs (cop , aff)

cop-aff-cover : ∀ {#s #x #ℓ} (§ : Structs #s) (Φ : Safes #s) (τ : Type #s #x #ℓ)
              → ⊢ § structs
              → § , Φ ⊢ τ type
              → § ⊢ τ Copy + § ⊢ τ Affine
cop-aff-cover § Φ int H§ Hτ = inl int
cop-aff-cover § Φ (~ τ) H§ Hτ = inr ~Aff
cop-aff-cover § Φ (& ℓ imm τ) H§ Hτ = inl &imm
cop-aff-cover § Φ (& ℓ mut τ) H§ Hτ = inr &mut
cop-aff-cover § Φ (opt τ) H§ (opt Hτ) with cop-aff-cover § Φ τ H§ Hτ
cop-aff-cover § Φ (opt τ) H§ (opt Hτ) | inl cop = inl (opt cop)
cop-aff-cover § Φ (opt τ) H§ (opt Hτ) | inr aff = inr (opt aff)
cop-aff-cover § Φ (struct s ℓs) H§ (struct suff) with
  handle-fields (set (Struct.env (§ ! s)) s unsafe)
                (Struct.fields (§ ! s))
                (subst
                   (λ s′ →
                      All (_,_⊢_type § (set (Struct.env (§ ! s′)) s′ unsafe))
                      (Struct.fields (§ ! s′)))
                   (range′-spec s) (fields-ok (H§ All! s)))
  where
  handle-fields : ∀ {#ℓ′ n} (Φ : Safes _) (τs : Vec (Type _ 0 #ℓ′) n)
                → All (λ τ → § , Φ ⊢ τ type) τs
                → All (_⊢_Copy §) τs + Any (_⊢_Affine §) τs
  handle-fields Φ′ [] Hτs = inl []
  handle-fields Φ′ (τ ∷ τs) (Hτ ∷ Hτs) with cop-aff-cover § Φ′ τ H§ Hτ
  ... | here = {!!}
cop-aff-cover § Φ (struct s ℓs) H§ (struct suff) | inl all-cop = inl (struct all-cop)
cop-aff-cover § Φ (struct s ℓs) H§ (struct suff) | inr any-aff = inr (struct any-aff)
