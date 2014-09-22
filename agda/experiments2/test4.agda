open import Common
open import Mut
open import Life
module test4 where

data Var : Set where
  cov : Var
  con : Var
  inv : Var

data Type {#s} (K : Vec ℕ #s) (#x #ℓ : ℕ) : Set where
  int : Type K #x #ℓ
  ~ : Type K #x #ℓ → Type K #x #ℓ
  & : Life #x #ℓ → Mut → Type K #x #ℓ → Type K #x #ℓ
  opt : Type K #x #ℓ → Type K #x #ℓ
  struct : (s : Fin #s) → Vec (Life #x #ℓ) (K ! s) → Type K #x #ℓ

record Struct {#s} (K : Vec ℕ #s) : Set where
  constructor struct
  field
    {#ℓ n} : ℕ
    params : Vec Var #ℓ
    fields : Vec (Type K 0 #ℓ) n

Structs : ∀ {#s} → Vec ℕ #s → Set
Structs {#s} K = Vec (Struct K) #s

data _⊢_Copy {#s K #x #ℓ} (§ : Structs {#s} K) : Type K #x #ℓ → Set where
  int : § ⊢ int Copy
  &imm : ∀ {ℓ τ} → § ⊢ & ℓ imm τ Copy
  opt : ∀ {τ} → § ⊢ τ Copy → § ⊢ opt τ Copy
  struct : ∀ {s ℓs} → All (λ τ → § ⊢ τ Copy) (Struct.fields (§ ! s)) → § ⊢ struct s ℓs Copy

data _⊢_Affine {#s K #x #ℓ} (§ : Structs {#s} K) : Type K #x #ℓ → Set where
  ~Aff : ∀ {τ} → § ⊢ ~ τ Affine
  &mut : ∀ {ℓ τ} → § ⊢ & ℓ mut τ Affine
  opt : ∀ {τ} → § ⊢ τ Affine → § ⊢ opt τ Affine
  struct : ∀ {s ℓs} → Any (λ τ → § ⊢ τ Affine) (Struct.fields (§ ! s)) → § ⊢ struct s ℓs Affine

_⊢_type : ∀ {#s K #x #ℓ} → Structs {#s} K → Type K #x #ℓ → Set
§ ⊢ τ type = § ⊢ τ Copy + § ⊢ τ Affine

record _⊢_struct {#s K} (§ : Structs {#s} K) (sr : Struct K) : Set where
  constructor struct
  field
    fields-ok : All (λ τ → § ⊢ τ type) (Struct.fields sr)
open _⊢_struct

record _⊢_structs {#s} (K : Vec ℕ #s) (§ : Structs {#s} K) : Set where
  constructor structs
  field
    kinds-ok : All2 (λ #ℓ sr → Struct.#ℓ sr ≡ #ℓ) K §
    structs-ok : All (λ sr → § ⊢ sr struct) §
open _⊢_structs

srs : Structs ([ 0 ,, 1 ,, 1 ,, 1 ,, 0 ])
srs = [  struct [] ([ int ])
      ,, struct ([ con ]) ([ int ,, & (var fZ) mut int ])
      ,, struct ([ con ]) ([ struct (fin 0) [] ,, struct (fin 1) ([ var fZ ]) ])
      ,, struct ([ con ]) ([ struct (fin 2) ([ var fZ ]) ,, struct (fin 0) []
                          ,, struct (fin 2) ([ var fZ ]) ,, struct (fin 1) ([ var fZ ]) ])
      ,, struct [] ([ ~ int ])
      ]

srs-ok : ([ 0 ,, 1 ,, 1 ,, 1 ,, 0 ]) ⊢ srs structs
srs-ok = structs (refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ [])
                 ( struct (inl int ∷ [])
                 ∷ struct (inl int ∷ inr &mut ∷ [])
                 ∷ struct (inl (struct (int ∷ [])) ∷ inr (struct (S (Z &mut))) ∷ [])
                 ∷ struct ( inr (struct (S (Z (struct (S (Z &mut))))))
                          ∷ inl (struct (int ∷ []))
                          ∷ inr (struct (S (Z (struct (S (Z &mut))))))
                          ∷ inr (struct (S (Z &mut)))
                          ∷ [])
                 ∷ struct (inr ~Aff ∷ [])
                 ∷ [])

list : Structs ([ 0 ])
list = [ struct [] ([ int ,, opt (~ (struct fZ [])) ]) ]

list-ok : ([ 0 ]) ⊢ list structs
list-ok = structs (refl ∷ []) (struct (inl int ∷ inr (opt ~Aff) ∷ []) ∷ [])

mk-wf-pf : ∀ {#s K #x #ℓ} (§ : Structs {#s} K) (H§ : K ⊢ § structs) (τ : Type K #x #ℓ) → § ⊢ τ type
mk-wf-pf § H§ int = inl int
mk-wf-pf § H§ (~ τ) = inr ~Aff
mk-wf-pf § H§ (& ℓ imm τ) = inl &imm
mk-wf-pf § H§ (& ℓ mut τ) = inr &mut
mk-wf-pf § H§ (opt τ) with mk-wf-pf § H§ τ
mk-wf-pf § H§ (opt τ) | inl cop = inl (opt cop)
mk-wf-pf § H§ (opt τ) | inr aff = inr (opt aff)
mk-wf-pf § H§ (struct s ℓs) with helper (Struct.fields (§ ! s)) (fields-ok (structs-ok H§ All! s)) 
  where
  helper : ∀ {#ℓ′ n} (τs : Vec (Type _ 0 #ℓ′) n) → All (λ τ → § ⊢ τ type) τs
         → All (λ τ → § ⊢ τ Copy) τs + Any (λ τ → § ⊢ τ Affine) τs
  helper .[] [] = inl []
  helper ._ (inl cop ∷ wfs) with helper _ wfs
  helper ._ (inl cop ∷ wfs) | inl all-cop = inl (cop ∷ all-cop)
  helper ._ (inl cop ∷ wfs) | inr any-aff = inr (S any-aff)
  helper ._ (inr aff ∷ wfs) = inr (Z aff)
mk-wf-pf § H§ (struct s ℓs) | inl all-cop = inl (struct all-cop)
mk-wf-pf § H§ (struct s ℓs) | inr any-aff = inr (struct any-aff)

data _⊢_Drop {#s K #x #ℓ} (§ : Structs {#s} K) : Type K #x #ℓ → Set where
  ~ : ∀ {τ} → § ⊢ ~ τ Drop
  opt : ∀ {τ} → § ⊢ τ Drop → § ⊢ opt τ Drop
  struct : ∀ {s ℓs} → Any (λ τ → § ⊢ τ Drop) (Struct.fields (§ ! s)) → § ⊢ struct s ℓs Drop

data _⊢_¬Drop {#s K #x #ℓ} (§ : Structs {#s} K) : Type K #x #ℓ → Set where
  int : § ⊢ int ¬Drop
  & : ∀ {ℓ μ τ} → § ⊢ & ℓ μ τ ¬Drop
  opt : ∀ {τ} → § ⊢ τ ¬Drop → § ⊢ opt τ ¬Drop
  struct : ∀ {s ℓs} → All (λ τ → § ⊢ τ ¬Drop) (Struct.fields (§ ! s)) → § ⊢ struct s ℓs ¬Drop

drop-¬drop-dis : ∀ {#s K #x #ℓ} (§ : Structs {#s} K) (τ : Type K #x #ℓ) → ¬ (§ ⊢ τ Drop × § ⊢ τ ¬Drop)
drop-¬drop-dis § int (() , ¬drop)
drop-¬drop-dis § (~ τ) (drop , ())
drop-¬drop-dis § (& ℓ μ τ) (() , ¬drop)
drop-¬drop-dis § (opt τ) (opt drop , opt ¬drop) = drop-¬drop-dis § τ (drop , ¬drop)
drop-¬drop-dis § (struct s ℓs) (struct any-drop , struct all-¬drop)
  = helper (Struct.fields (§ ! s)) (any-drop , all-¬drop)
  where
  helper : ∀ {#ℓ′ n} → (τs : Vec (Type _ 0 #ℓ′) n)
         → ¬ (Any (λ τ → § ⊢ τ Drop) τs × All (λ τ → § ⊢ τ ¬Drop) τs)
  helper [] (() , _)
  helper (τ ∷ _) (Z Hdrop , (H¬drop ∷ _)) = drop-¬drop-dis § τ (Hdrop , H¬drop)
  helper (_ ∷ τs) (S Hdrop , (_ ∷ H¬drop)) = helper τs (Hdrop , H¬drop)

drop-¬drop-cover : ∀ {#s K #x #ℓ}
                 → (§ : Structs {#s} K) → K ⊢ § structs
                 → {τ : Type K #x #ℓ} → § ⊢ τ type
                 → § ⊢ τ Drop + § ⊢ τ ¬Drop
drop-¬drop-cover § H§ (inl int) = inr int
drop-¬drop-cover § H§ (inl &imm) = inr &
drop-¬drop-cover § H§ (inl (opt cop)) with drop-¬drop-cover § H§ (inl cop)
drop-¬drop-cover § H§ (inl (opt cop)) | inl drop = inl (opt drop)
drop-¬drop-cover § H§ (inl (opt cop)) | inr ¬drop = inr (opt ¬drop)
drop-¬drop-cover § H§ {struct s _} (inl (struct all-cop))
  with helper (fields-ok (structs-ok H§ All! s))
  where
  helper : ∀ {#ℓ′ n} {τs : Vec (Type _ 0 #ℓ′) n}
         → All (λ τ → § ⊢ τ type) τs
         → Any (λ τ → § ⊢ τ Drop) τs + All (λ τ → § ⊢ τ ¬Drop) τs
  helper [] = inr []
  helper (wf ∷ wfs) = {!!}
drop-¬drop-cover § H§ {struct s x} (inl (struct all-cop)) | inl any-drop = inl (struct any-drop)
drop-¬drop-cover § H§ {struct s x} (inl (struct all-cop)) | inr all-¬drop = inr (struct all-¬drop)
drop-¬drop-cover § H§ (inr x) = {!!}                 
  {-
drop-¬drop-cover : ∀ {#s K #x #ℓ}
                 → (§ : Structs {#s} K) → K ⊢ § structs
                 → (τ : Type K #x #ℓ)
                 → § ⊢ τ Drop + § ⊢ τ ¬Drop
drop-¬drop-cover § H§ int = inr int
drop-¬drop-cover § H§ (~ τ) = inl ~
drop-¬drop-cover § H§ (& ℓ μ τ) = inr &
drop-¬drop-cover § H§ (opt τ) with drop-¬drop-cover § H§ τ
drop-¬drop-cover § H§ (opt τ) | inl drop = inl (opt drop)
drop-¬drop-cover § H§ (opt τ) | inr ¬drop = inr (opt ¬drop)
drop-¬drop-cover § H§ (struct s ℓs) = {!!}
  where
  helper : {!!} → {!!}
  helper = {!!}
  -}
{-
drop-¬drop-cover § H§ (opt τ) (inl (opt cop)) with drop-¬drop-cover § H§ τ (inl cop)
drop-¬drop-cover § H§ (opt τ) (inl (opt cop)) | inl drop = inl (opt drop)
drop-¬drop-cover § H§ (opt τ) (inl (opt cop)) | inr ¬drop = inr (opt ¬drop)
drop-¬drop-cover § H§ (opt τ) (inr (opt aff)) with drop-¬drop-cover § H§ τ (inr aff)
drop-¬drop-cover § H§ (opt τ) (inr (opt aff)) | inl drop = inl (opt drop)
drop-¬drop-cover § H§ (opt τ) (inr (opt aff)) | inr ¬drop = inr (opt ¬drop)
drop-¬drop-cover § H§ (struct s ℓs) (inl (struct all-cop)) = {!!}
drop-¬drop-cover § H§ (struct s ℓs) (inr (struct any-aff)) = {!!}
-}
