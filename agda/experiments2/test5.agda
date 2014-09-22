open import Common
open import Life
open import Mut
module test5 where

data Type (#s #x #ℓ : ℕ) : (K : ℕ) → Set where
  int : Type #s #x #ℓ 0
  ~ : Type #s #x #ℓ 0 → Type #s #x #ℓ 0
  & : Life #x #ℓ → Mut → Type #s #x #ℓ 0 → Type #s #x #ℓ 0
  opt : Type #s #x #ℓ 0 → Type #s #x #ℓ 0
  rec : ∀ {n} → Vec (Type #s #x #ℓ 0) n → Type #s #x #ℓ 0
  μ : Type (S #s) #x #ℓ 0 → Type #s #x #ℓ 0
  var : Fin #s → Type #s #x #ℓ 0
  abs : ∀ {κ} → Type #s 0 κ 0 → Type #s #x #ℓ κ
  app : ∀ {κ} → Type #s #x #ℓ κ → Vec (Life #x #ℓ) κ → Type #s #x #ℓ 0

subst-τ : ∀ {#s #x #ℓ #ℓ′ κ} → Vec (Life #x #ℓ) #ℓ′ → Type #s 0 #ℓ′ κ → Type #s #x #ℓ κ
subst-τ ℓs int = int
subst-τ ℓs (~ τ) = ~ (subst-τ ℓs τ)
subst-τ ℓs (& ℓ m τ) = & (subst-ℓ ℓs ℓ) m (subst-τ ℓs τ)
subst-τ ℓs (opt τ) = opt (subst-τ ℓs τ)
subst-τ ℓs (rec τs) = rec (helper τs)
  where
  helper : ∀ {n} → Vec _ n → Vec _ n
  helper [] = []
  helper (τ ∷ τs′) = subst-τ ℓs τ ∷ helper τs′
subst-τ ℓs (μ τ) = μ (subst-τ ℓs τ)
subst-τ ℓs (var s) = var s
subst-τ ℓs (abs τ) = abs τ
subst-τ ℓs (app τ ℓs′) = app (subst-τ ℓs τ) (map (subst-ℓ ℓs) ℓs′)

data _==>_ {#s #x #ℓ} : ∀ {κ} → Type #s #x #ℓ κ → Type #s #x #ℓ κ → Set where
  refl : ∀ {κ} {τ : Type _ _ _ κ} → τ ==> τ
  ~ : ∀ {τ τ′} → τ ==> τ′ → ~ τ ==> ~ τ′
  & : ∀ {ℓ m τ τ′} → τ ==> τ′ → & ℓ m τ ==> & ℓ m τ′
  opt : ∀ {τ τ′} → τ ==> τ′ → opt τ ==> opt τ′
  rec : ∀ {n τs τs′} → All2 _==>_ {n} τs τs′ → rec τs ==> rec τs′
  μ : ∀ {τ τ′} → τ ==> τ′ → μ τ ==> μ τ′
  abs : ∀ {κ τ τ′} → τ ==> τ′ → abs {κ = κ} τ ==> abs τ′
  app==> : ∀ {κ τ τ′ ℓs} → τ ==> τ′ → (app {κ = κ} τ ℓs) ==> (app τ′ ℓs)
  appabs : ∀ {κ τ ℓs} → (app (abs {κ = κ} τ) ℓs) ==> subst-τ ℓs τ

srs-A : ∀ {#s #x #ℓ} → Type #s #x #ℓ 0
srs-A = rec ([ int ])

srs-B : ∀ {#s #x #ℓ} → Type #s #x #ℓ 1
srs-B = abs (rec ([ int ,, & (var fZ) mut int ]))

srs-C : ∀ {#s #x #ℓ} → Type #s #x #ℓ 1
srs-C = abs (rec ([ srs-A ,, app srs-B ([ var fZ ]) ]))

srs-D : ∀ {#s #x #ℓ} → Type #s #x #ℓ 1
srs-D = abs (rec ([ app srs-C ([ var fZ ]) ,, srs-A
                 ,, app srs-C ([ var fZ ]) ,, app srs-B ([ var fZ ]) ]))

srs-E : ∀ {#s #x #ℓ} → Type #s #x #ℓ 0
srs-E = rec ([ ~ int ])

srs-List : ∀ {#s #x #ℓ} → Type #s #x #ℓ 0
srs-List = μ (rec ([ int ,, opt (~ (var fZ)) ]))

data Safe : Set where
  safe : Safe
  unsafe : Safe

Safes : ℕ → Set
Safes #s = Vec Safe #s

reset : ∀ {#s} → Safes #s
reset = rep safe _

data _⊢_type {#s #x #ℓ} (§ : Safes #s) : ∀ {κ} → Type #s #x #ℓ κ → Set where 
  int : § ⊢ int type
  ~ : ∀ {τ} → reset ⊢ τ type → § ⊢ ~ τ type
  & : ∀ {ℓ m τ} → reset ⊢ τ type → § ⊢ & ℓ m τ type
  opt : ∀ {τ} → § ⊢ τ type → § ⊢ opt τ type
  rec : ∀ {n τs} → All (λ τ → § ⊢ τ type) {n} τs → § ⊢ rec τs type
  μ : ∀ {τ} → (unsafe ∷ §) ⊢ τ type → § ⊢ μ τ type
  var : ∀ {s} → § ! s ≡ safe → § ⊢ var s type
  abs : ∀ {κ τ} → § ⊢ τ type → § ⊢ abs {κ = κ} τ type
  app : ∀ {κ τ ℓs} → § ⊢ τ type → § ⊢ app {κ = κ} τ ℓs type

data _nuopi_ {#s #x #ℓ} (s : Fin #s) : ∀ {κ} → Type #s #x #ℓ κ → Set where
  int : s nuopi int
  ~ : ∀ {τ} → s nuopi ~ τ
  & : ∀ {ℓ m τ} → s nuopi & ℓ m τ
  opt : ∀ {τ} → s nuopi τ → s nuopi opt τ
  rec : ∀ {n τs} → All (λ τ → s nuopi τ) {n} τs → s nuopi rec τs
  μ : ∀ {τ} → fS s nuopi τ → s nuopi μ τ
  var : ∀ {s′} → ¬ (s ≡ s′) → s nuopi var s′
  abs : ∀ {κ τ} → s nuopi τ → s nuopi abs {κ = κ} τ
  app : ∀ {κ τ ℓs} → s nuopi τ → s nuopi app {κ = κ} τ ℓs

data _wf {#s #x #ℓ} : ∀ {κ} → Type #s #x #ℓ κ → Set where
  int : int wf
  ~ : ∀ {τ} → τ wf → ~ τ wf
  & : ∀ {ℓ m τ} → τ wf → & ℓ m τ wf
  opt : ∀ {τ} → τ wf → opt τ wf
  rec : ∀ {n τs} → All _wf {n} τs → rec τs wf
  μ : ∀ {τ} → fZ nuopi τ → τ wf → μ τ wf

data _Copy {#s #x #ℓ} : ∀ {κ} → Type #s #x #ℓ κ → Set where
  int : int Copy
  &imm : ∀ {ℓ τ} → & ℓ imm τ Copy
  opt : ∀ {τ} → τ Copy → opt τ Copy
  rec : ∀ {n τs} → All _Copy {n} τs → rec τs Copy
  μ : ∀ {τ} → τ Copy → μ τ Copy
  abs : ∀ {κ τ} → τ Copy → abs {κ = κ} τ Copy
  app : ∀ {κ τ ℓs} → τ Copy → app {κ = κ} τ ℓs Copy

record Mu : Set where
  constructor mu
  field
    {#s #x #ℓ} : ℕ
    structs : Vec Mu #s
    body : Type (S #s) #x #ℓ 0

data _⊢_Copy {#s #x #ℓ} (§ : Vec Mu #s) : ∀ {κ} → Type #s #x #ℓ κ → Set where
  int : § ⊢ int Copy
  &imm : ∀ {ℓ τ} → § ⊢ & ℓ imm τ Copy
  opt : ∀ {τ} → § ⊢ τ Copy → § ⊢ opt τ Copy
  rec : ∀ {n τs} → All (_⊢_Copy §) {n} τs → § ⊢ rec τs Copy
  μ : ∀ {τ} → (mu § τ ∷ §) ⊢ τ Copy → § ⊢ μ τ Copy
  var : ∀ {s} → Mu.structs (§ ! s) ⊢ μ (Mu.body (§ ! s)) Copy → § ⊢ var s Copy
  abs : ∀ {κ τ} → § ⊢ τ Copy → § ⊢ abs {κ = κ} τ Copy
  app : ∀ {κ τ ℓs} → § ⊢ τ Copy → § ⊢ app {κ = κ} τ ℓs Copy

test-1 : ([ mu [] (rec ([ int {_} {0} {0} ])) ]) ⊢ var {_} {0} {0} fZ Copy
test-1 = var (μ (rec (int ∷ [])))

data _Move {#s #x #ℓ} : ∀ {κ} → Type #s #x #ℓ κ → Set where
  ~ : ∀ {τ} → ~ τ Move
  &mut : ∀ {ℓ τ} → & ℓ mut τ Move
  opt : ∀ {τ} → τ Move → opt τ Move
  rec : ∀ {n τs} → Any _Move {n} τs → rec τs Move
  μ : ∀ {τ} → τ Move → μ τ Move
  abs : ∀ {κ τ} → τ Move → abs {κ = κ} τ Move
  app : ∀ {κ τ ℓs} → τ Move → app {κ = κ} τ ℓs Move

data _⊢_Move {#s #x #ℓ} (§ : Vec Mu #s) : ∀ {κ} → Type #s #x #ℓ κ → Set where
  ~ : ∀ {τ} → § ⊢ ~ τ Move
  &mut : ∀ {ℓ τ} → § ⊢ & ℓ mut τ Move
  opt : ∀ {τ} → § ⊢ τ Move → § ⊢ opt τ Move
  rec : ∀ {n τs} → Any (_⊢_Move §) {n} τs → § ⊢ rec τs Move
  μ : ∀ {τ} → (mu § τ ∷ §) ⊢ τ Move → § ⊢ μ τ Move
  var : ∀ {s} → Mu.structs (§ ! s) ⊢ μ (Mu.body (§ ! s)) Move → § ⊢ var s Move
  abs : ∀ {κ τ} → § ⊢ τ Move → § ⊢ abs {κ = κ} τ Move
  app : ∀ {κ τ ℓs} → § ⊢ τ Move → § ⊢ app {κ = κ} τ ℓs Move

copy-move-disjoint : ∀ {#s #x #ℓ κ} → (τ : Type #s #x #ℓ κ) → ¬ (τ Copy × τ Move)
copy-move-disjoint int (copy , ())
copy-move-disjoint (~ τ) (() , move)
copy-move-disjoint (& ℓ imm τ) (copy , ())
copy-move-disjoint (& ℓ mut τ) (() , move)
copy-move-disjoint (opt τ) (opt copy , opt move) = copy-move-disjoint τ (copy , move)
copy-move-disjoint (rec τs) (rec all-copy , rec any-move) = helper τs (all-copy , any-move)
  where
  helper : ∀ {n} (τs : Vec _ n) → ¬ (All _ τs × Any _ τs)
  helper [] (all , ())
  helper (τ ∷ τs′) ((copy ∷ all) , Z move) = copy-move-disjoint τ (copy , move)
  helper (τ ∷ τs′) ((copy ∷ all) , S any) = helper τs′ (all , any)
copy-move-disjoint (μ τ) (μ copy , μ move) = copy-move-disjoint τ (copy , move)
copy-move-disjoint (var s) (() , ())
copy-move-disjoint (abs τ) (abs copy , abs move) = copy-move-disjoint τ (copy , move)
copy-move-disjoint (app τ ℓs) (app copy , app move) = copy-move-disjoint τ (copy , move)

c×m≡⊥ : ∀ {#s #x #ℓ κ} § (τ : Type #s #x #ℓ κ) → ¬ (§ ⊢ τ Copy × § ⊢ τ Move)
c×m≡⊥ § int (copy , ())
c×m≡⊥ § (~ τ) (() , move)
c×m≡⊥ § (& ℓ imm τ) (copy , ())
c×m≡⊥ § (& ℓ mut τ) (() , move)
c×m≡⊥ § (opt τ) (opt copy , opt move) = c×m≡⊥ § τ (copy , move)
c×m≡⊥ § (rec []) (rec _ , rec ())
c×m≡⊥ § (rec (τ ∷ _)) (rec (copy ∷ _) , rec (Z move)) = c×m≡⊥ § τ (copy , move)
c×m≡⊥ § (rec (_ ∷ τs)) (rec (_ ∷ copy) , rec (S move)) = c×m≡⊥ § (rec τs) (rec copy , rec move)
c×m≡⊥ § (μ τ) (μ copy , μ move) = c×m≡⊥ (mu § τ ∷ §) τ (copy , move)
c×m≡⊥ § (var s) (var copy , var move) = c×m≡⊥ (Mu.structs (§ ! s)) (μ (Mu.body (§ ! s))) (copy , move)
c×m≡⊥ § (abs τ) (abs copy , abs move) = c×m≡⊥ § τ (copy , move)
c×m≡⊥ § (app τ ℓs) (app copy , app move) = c×m≡⊥ § τ (copy , move)

{-
c+m≡⊤ : ∀ {#s #x #ℓ κ} § (τ : Type #s #x #ℓ κ) → § ⊢ τ Copy + § ⊢ τ Move
c+m≡⊤ § int = inl int
c+m≡⊤ § (~ τ) = inr ~
c+m≡⊤ § (& ℓ imm τ) = inl &imm
c+m≡⊤ § (& ℓ mut τ) = inr &mut
c+m≡⊤ § (opt τ) = {!!}
c+m≡⊤ § (rec τs) = {!!}
c+m≡⊤ § (μ τ) = {!!}
c+m≡⊤ § (var s) with c+m≡⊤ (Mu.structs (§ ! s)) (μ (Mu.body (§ ! s)))
... | ih = {!!}
c+m≡⊤ § (abs τ) = {!!}
c+m≡⊤ § (app τ ℓs) = {!!}
-}

foo : ∀ {#s #x #ℓ} § (s : Fin #s) (mu : Mu)
    → § ⊢ var {_} {#x} {#ℓ} s type
    → Σ _ ** λ §′ → §′ ⊢ μ (Mu.body mu) type
foo § s (mu structs body) (var x) = {!!} , μ {!!}

wf→c+m : ∀ {#s #x #ℓ κ} § μs (τ : Type #s #x #ℓ κ) → § ⊢ τ type → μs ⊢ τ Copy + μs ⊢ τ Move
wf→c+m § μs int int = inl int
wf→c+m § μs (~ τ) (~ wf) = inr ~
wf→c+m § μs (& ℓ imm τ) (& wf) = inl &imm
wf→c+m § μs (& ℓ mut τ) (& wf) = inr &mut
wf→c+m § μs (opt τ) (opt wf) = {!!}
wf→c+m § μs (rec τs) (rec all-wf) = {!!}
wf→c+m § μs (μ τ) (μ wf) = {!!}
wf→c+m § μs (var s) (var s-safe) with wf→c+m (rev (take (Mu.#s (μs ! s)) (rev {!§!}))) (Mu.structs (μs ! s)) (μ (Mu.body (μs ! s))) {!!}
... | ih = {!!}
wf→c+m § μs (abs τ) (abs wf) = {!!}
wf→c+m § μs (app τ ℓs) (app wf) = {!!}

data _Drop {#s #x #ℓ} : ∀ {κ} → Type #s #x #ℓ κ → Set where
  ~ : ∀ {τ} → ~ τ Drop
  opt : ∀ {τ} → τ Drop → opt τ Drop
  rec : ∀ {n τs} → Any _Drop {n} τs → rec τs Drop
  μ : ∀ {τ} → τ Drop → μ τ Drop
  abs : ∀ {κ τ} → τ Drop → abs {κ = κ} τ Drop
  app : ∀ {κ τ ℓs} → τ Drop → app {κ = κ} τ ℓs Drop

data _¬Drop {#s #x #ℓ} : ∀ {κ} → Type #s #x #ℓ κ → Set where
  int : int ¬Drop
  & : ∀ {ℓ m τ} → & ℓ m τ ¬Drop
  opt : ∀ {τ} → τ ¬Drop → opt τ ¬Drop
  rec : ∀ {n τs} → All _¬Drop {n} τs → rec τs ¬Drop
  μ : ∀ {τ} → τ ¬Drop → μ τ ¬Drop
  abs : ∀ {κ τ} → τ ¬Drop → abs {κ = κ} τ ¬Drop
  app : ∀ {κ τ ℓs} → τ ¬Drop → app {κ = κ} τ ℓs ¬Drop

drop-¬drop-disjoint : ∀ {#s #x #ℓ κ} → (τ : Type #s #x #ℓ κ) → ¬ (τ Drop × τ ¬Drop)
drop-¬drop-disjoint int (() , ¬drop)
drop-¬drop-disjoint (~ τ) (drop , ())
drop-¬drop-disjoint (& ℓ m τ) (() , ¬drop)
drop-¬drop-disjoint (opt τ) (opt drop , opt ¬drop) = drop-¬drop-disjoint τ (drop , ¬drop)
drop-¬drop-disjoint (rec τs) (rec any-drop , rec all-¬drop) = helper τs (any-drop , all-¬drop)
  where
  helper : ∀ {n} (τs : Vec _ n) → ¬ (Any _ τs × All _ τs)
  helper [] (() , all)
  helper (τ ∷ τs′) (Z drop , (¬drop ∷ all)) = drop-¬drop-disjoint τ (drop , ¬drop)
  helper (τ ∷ τs′) (S any , (¬drop ∷ all)) = helper τs′ (any , all)
drop-¬drop-disjoint (μ τ) (μ drop , μ ¬drop) = drop-¬drop-disjoint τ (drop , ¬drop)
drop-¬drop-disjoint (var s) (() , ())
drop-¬drop-disjoint (abs τ) (abs drop , abs ¬drop) = drop-¬drop-disjoint τ (drop , ¬drop)
drop-¬drop-disjoint (app τ ℓs) (app drop , app ¬drop) = drop-¬drop-disjoint τ (drop , ¬drop)

copy+move→drop+¬drop : ∀ {#s #x #ℓ κ} (τ : Type #s #x #ℓ κ)
                     → τ Copy + τ Move
                     → τ Drop + τ ¬Drop
copy+move→drop+¬drop int c+m = inr int
copy+move→drop+¬drop (~ τ) c+m = inl ~
copy+move→drop+¬drop (& ℓ m τ) c+m = inr &
copy+move→drop+¬drop (opt τ) (inl (opt copy)) with copy+move→drop+¬drop τ (inl copy)
... | inl drop = inl (opt drop)
... | inr ¬drop = inr (opt ¬drop)
copy+move→drop+¬drop (opt τ) (inr (opt move)) with copy+move→drop+¬drop τ (inr move)
... | inl drop = inl (opt drop)
... | inr ¬drop = inr (opt ¬drop)
copy+move→drop+¬drop (rec τs) (inl (rec all-copy)) with helper τs all-copy
  where
  helper : ∀ {n} (τs : Vec _ n) → All _ τs → Any _Drop τs + All _¬Drop τs
  helper [] [] = inr []
  helper (τ ∷ τs′) (copy ∷ all) with copy+move→drop+¬drop τ (inl copy)
  ... | inl drop = inl (Z drop)
  ... | inr ¬drop with helper τs′ all
  ... | inl any-drop = inl (S any-drop)
  ... | inr all-drop = inr (¬drop ∷ all-drop)
... | inl any-drop = inl (rec any-drop)
... | inr all-¬drop = inr (rec all-¬drop)
copy+move→drop+¬drop (rec τs) (inr (rec any-move)) = {!!}
copy+move→drop+¬drop (μ τ) (inl (μ copy)) with copy+move→drop+¬drop τ (inl copy)
... | inl drop = inl (μ drop)
... | inr ¬drop = inr (μ ¬drop)
copy+move→drop+¬drop (μ τ) (inr (μ move)) with copy+move→drop+¬drop τ (inr move)
... | inl drop = inl (μ drop)
... | inr ¬drop = inr (μ ¬drop)
copy+move→drop+¬drop (var s) (inl ())
copy+move→drop+¬drop (var s) (inr ())
copy+move→drop+¬drop (abs τ) (inl (abs copy)) with copy+move→drop+¬drop τ (inl copy)
... | inl drop = inl (abs drop)
... | inr ¬drop = inr (abs ¬drop)
copy+move→drop+¬drop (abs τ) (inr (abs move)) with copy+move→drop+¬drop τ (inr move)
... | inl drop = inl (abs drop)
... | inr ¬drop = inr (abs ¬drop)
copy+move→drop+¬drop (app τ ℓs) (inl (app copy)) with copy+move→drop+¬drop τ (inl copy)
... | inl drop = inl (app drop)
... | inr ¬drop = inr (app ¬drop)
copy+move→drop+¬drop (app τ ℓs) (inr (app move)) with copy+move→drop+¬drop τ (inr move)
... | inl drop = inl (app drop)
... | inr ¬drop = inr (app ¬drop)


{-
data Var : Set where
  cov : Var
  con : Var
  inv : Var

data Type (#s #x : ℕ) : (#ℓ K : ℕ) → Set where
  int : ∀ {#ℓ} → Type #s #x #ℓ 0
  ~ : ∀ {#ℓ} → Type #s #x #ℓ 0 → Type #s #x #ℓ 0
  & : ∀ {#ℓ} → Life #x #ℓ → Mut → Type #s #x #ℓ 0 → Type #s #x #ℓ 0
  opt : ∀ {#ℓ} → Type #s #x #ℓ 0 → Type #s #x #ℓ 0
  rec : ∀ {#ℓ n} → Vec (Type #s #x #ℓ 0) n → Type #s #x #ℓ 0
  μ : ∀ {#ℓ} → Type (S #s) #x #ℓ 0 → Type #s #x #ℓ 0
  var : ∀ {#ℓ} → Fin #s → Type #s #x #ℓ 0
  abs : (κ : ℕ) → Type #s #x κ 0 → Type #s #x 0 κ
  _app_ : ∀ {#ℓ κ} → Type #s #x 0 κ → Vec (Life #x #ℓ) κ → Type #s #x #ℓ 0

foo : ∀ {n} → Fin n → Fin (S n) → Fin (S n) → Fin n
foo v c f with asℕ f <? asℕ c
foo v c f | yes f<c = {!!}
foo v c f | no  f≥c = {!!}

subst-τ : ∀ {#s #x #ℓ #ℓ′ κ} → Type #s #x #ℓ′ κ → Vec (Life #x #ℓ) #ℓ′ → Type #s #x #ℓ κ
subst-τ int ℓs = int
subst-τ (~ τ) ℓs = ~ (subst-τ τ ℓs)
subst-τ (& ℓ m τ) ℓs = {!!}
subst-τ (opt τ) ℓs = opt (subst-τ τ ℓs)
subst-τ (rec τs) ℓs = rec (helper ℓs τs)
  where
  helper : ∀ {#s #x #ℓ #ℓ′ κ n} → Vec (Life #x #ℓ) #ℓ′
         → Vec (Type #s #x #ℓ′ κ) n → Vec (Type #s #x #ℓ κ) n
  helper ℓs [] = []
  helper ℓs (τ ∷ τs′) = subst-τ τ ℓs ∷ helper ℓs τs′
subst-τ (μ τ) ℓs = μ {!!}
subst-τ (var s) ℓs = var s
subst-τ (abs κ τ) ℓs = {!!}
subst-τ (τ app ℓs′) ℓs = {!!}

data _==>_ {#s #x} : ∀ {#ℓ κ} → Type #s #x #ℓ κ → Type #s #x #ℓ κ → Set where
  refl : ∀ {#ℓ κ} {τ : Type _ _ #ℓ κ} → τ ==> τ
  ~ : ∀ {#ℓ} {τ τ′ : Type _ _ #ℓ _} → τ ==> τ′ → ~ τ ==> ~ τ′
  & : ∀ {#ℓ ℓ m} {τ τ′ : Type _ _ #ℓ _} → τ ==> τ′ → & ℓ m τ ==> & ℓ m τ′
  opt : ∀ {#ℓ} {τ τ′ : Type _ _ #ℓ _} → τ ==> τ′ → opt τ ==> opt τ′
  rec : ∀ {#ℓ n} {τs τs′ : Vec (Type _ _ #ℓ 0) n}
      → All2 (λ τ τ′ → τ ==> τ′) τs τs′
      → rec τs ==> rec τs′
  μ : ∀ {#ℓ} {τ τ′ : Type _ _ #ℓ _} → τ ==> τ′ → μ τ ==> μ τ′
  abs : ∀ {κ τ τ′} → τ ==> τ′ → abs κ τ ==> abs κ τ′
  app==> : ∀ {#ℓ κ} {τ τ′} {ℓs : Vec (Life #x #ℓ) κ} → τ ==> τ′ → (τ app ℓs) ==> (τ′ app ℓs)
  appabs : ∀ {#ℓ κ τ} {ℓs : Vec (Life #x #ℓ) κ} → (abs κ τ app ℓs) ==> {!!}
  -}

  {-
data Type (#x #ℓ #s : ℕ) : (K : ℕ) → Set where
  int : Type #x #ℓ #s 0
  ~ : Type #x #ℓ #s 0 → Type #x #ℓ #s 0
  & : Life #x #ℓ → Mut → Type #x #ℓ #s 0 → Type #x #ℓ #s 0
  opt : Type #x #ℓ #s 0 → Type #x #ℓ #s 0
  rec : ∀ {n} → Vec (Type #x #ℓ #s 0) n → Type #x #ℓ #s 0
  μ : Type #x #ℓ (S #s) 0 → Type #x #ℓ #s 0
  var : Fin #s → Type #x #ℓ #s 0
  abs : (κ : ℕ) → Type #x κ #s 0 → Type #x 0 #s κ
  _app_ : ∀ {κ} → Type #x #ℓ #s κ → Vec (Life #x #ℓ) κ → Type #x #ℓ #s 0

data _==>_ {#x #ℓ #s} : ∀ {κ} → Type #x #ℓ #s κ → Type #x #ℓ #s κ → Set where
  refl : ∀ {κ} {τ : Type _ _ _ κ} → τ ==> τ
  ~ : ∀ {τ τ′} → τ ==> τ′ → ~ τ ==> ~ τ′
  & : ∀ {ℓ m τ τ′} → τ ==> τ′ → & ℓ m τ ==> & ℓ m τ′
  opt : ∀ {τ τ′} → τ ==> τ′ → opt τ ==> opt τ′
  rec : ∀ {n} {τs τs′ : Vec _ n} → All2 (λ τ τ′ → τ ==> τ′) τs τs′ → rec τs ==> rec τs′
  μ : ∀ {τ τ′} → τ ==> τ′ → μ τ ==> μ τ′
  abs : ∀ {κ τ τ′} → τ ==> τ′ → abs κ τ ==> abs κ τ′
  app==> : ∀ {κ τ τ′} {ℓs : Vec _ κ} → τ ==> τ′ → (τ app ℓs) ==> (τ′ app ℓs)
  appabs : ∀ {κ τ ℓs} → (abs κ τ app ℓs) ==> {!!}
  {-
  app==> : ∀ {ℓ κ} {τ τ′ : Type _ _ _ (S κ)} → τ ==> τ′ → (τ app ℓ) ==> (τ′ app ℓ)
  appabs : ∀ {ℓ τ} → (abs τ app ℓ) ==> {!!}
  -}
  -}

  {-
data Type (#x #ℓ #s : ℕ) : (K : ℕ) → Set where
  int : Type #x #ℓ #s 0
  ~ : Type #x #ℓ #s 0 → Type #x #ℓ #s 0
  & : Life #x #ℓ → Mut → Type #x #ℓ #s 0 → Type #x #ℓ #s 0
  opt : Type #x #ℓ #s 0 → Type #x #ℓ #s 0
  rec : ∀ {n} → Vec (Type #x #ℓ #s 0) n → Type #x #ℓ #s 0
  μ : Type #x #ℓ (S #s) 0 → Type #x #ℓ #s 0
  var : Fin #s → Type #x #ℓ #s 0
  abs : ∀ {κ} → Type #x (S #ℓ) #s κ → Type #x #ℓ #s (S κ)
  _app_ : ∀ {κ} → Type #x #ℓ #s (S κ) → Life #x #ℓ → Type #x #ℓ #s κ

[_↦_]_ : ∀ {#x #ℓ #s κ} → Fin (S #ℓ) → Life #x #ℓ → Type #x (S #ℓ) #s κ → Type #x #ℓ #s κ
[ Ł ↦ ℓ ] int = int
[ Ł ↦ ℓ ] ~ τ = ~ ([ Ł ↦ ℓ ] τ)
[ Ł ↦ ℓ ] & (var ℓ′) m τ with asℕ Ł <? asℕ ℓ′
[ Ł ↦ ℓ ] & (var ℓ′) m τ | yes Ł<ℓ′ = & {!!} m ([ Ł ↦ ℓ ] τ)
[ Ł ↦ ℓ ] & (var ℓ′) m τ | no  Ł≥ℓ′ = & {!!} m ([ Ł ↦ ℓ ] τ)
[ Ł ↦ ℓ ] & static m τ = & static m ([ Ł ↦ ℓ ] τ)
[ Ł ↦ ℓ ] & (val x) m τ = & (val x) m ([ Ł ↦ ℓ ] τ)
[ Ł ↦ ℓ ] opt τ = opt ([ Ł ↦ ℓ ] τ)
[ Ł ↦ ℓ ] rec τs = {!!}
[ Ł ↦ ℓ ] μ τ = μ ([ Ł ↦ ℓ ] τ)
[ Ł ↦ ℓ ] var s = var s
[ Ł ↦ ℓ ] abs τ = abs ([ fS Ł ↦ ↑#ℓ-ℓ 1 ℓ ] τ)
[ Ł ↦ ℓ ] (τ app ℓ′) = {!!}

  {-
[_]_ : ∀ {#x #ℓ #s κ} → Life #x #ℓ → Type #x (S #ℓ) #s κ → Type #x #ℓ #s κ
[ ℓ ] int = int
[ ℓ ] ~ τ = ~ ([ ℓ ] τ)
[ ℓ ] & (var fZ) m τ = & ℓ m ([ ℓ ] τ)
[ ℓ ] & (var (fS ℓ′)) m τ = & (var ℓ′) m ([ ℓ ] τ)
[ ℓ ] & static m τ = & static m ([ ℓ ] τ)
[ ℓ ] & (val x) m τ = & (val x) m ([ ℓ ] τ)
[ ℓ ] opt τ = opt ([ ℓ ] τ)
[ ℓ ] rec τs = rec {!!}
[ ℓ ] μ τ = μ {!!}
[ ℓ ] var s = var s
[ ℓ ] abs τ = abs {!!}
[ ℓ ] (τ app ℓ′) = {!!} app {!!}
-}

data _==>_ {#x #ℓ #s} : ∀ {κ} → Type #x #ℓ #s κ → Type #x #ℓ #s κ → Set where
  refl : ∀ {κ} {τ : Type _ _ _ κ} → τ ==> τ
  ~ : ∀ {τ τ′} → τ ==> τ′ → ~ τ ==> ~ τ′
  & : ∀ {ℓ m τ τ′} → τ ==> τ′ → & ℓ m τ ==> & ℓ m τ′
  opt : ∀ {τ τ′} → τ ==> τ′ → opt τ ==> opt τ′
  rec : ∀ {n} {τs τs′ : Vec _ n} → All2 (λ τ τ′ → τ ==> τ′) τs τs′ → rec τs ==> rec τs′
  μ : ∀ {τ τ′} → τ ==> τ′ → μ τ ==> μ τ′
  abs : ∀ {κ} {τ τ′ : Type _ _ _ κ} → τ ==> τ′ → abs τ ==> abs τ′
  app==> : ∀ {ℓ κ} {τ τ′ : Type _ _ _ (S κ)} → τ ==> τ′ → (τ app ℓ) ==> (τ′ app ℓ)
  appabs : ∀ {ℓ τ} → (abs τ app ℓ) ==> {!!}

srs-A : ∀ {#x #ℓ #s} → Type #x #ℓ #s 0
srs-A = rec ([ int ])

srs-B : ∀ {#x #ℓ #s} → Type #x #ℓ #s 1
srs-B = abs (rec ([ int ,, & (var fZ) mut int ]))

srs-C : ∀ {#x #ℓ #s} → Type #x #ℓ #s 1
srs-C = abs (rec ([ srs-A ,, srs-B app var fZ ]))

srs-D : ∀ {#x #ℓ #s} → Type #x #ℓ #s 1
srs-D = abs (rec ([ srs-C app var fZ ,, srs-A ,, srs-C app var fZ ,, srs-B app var fZ ]))

srs-E : ∀ {#x #ℓ #s} → Type #x #ℓ #s 0
srs-E = rec ([ ~ int ])

srs-List : ∀ {#x #ℓ #s} → Type #x #ℓ #s 0
srs-List = μ (rec ([ int ,, opt (~ (var fZ)) ]))
-}

{-
normalize-τ : ∀ {#x #ℓ #s} → Type #x #ℓ #s 0 → Type #x #ℓ #s 0
normalize-τ int = int
normalize-τ (~ τ) = ~ (normalize-τ τ)
normalize-τ (& ℓ m τ) = & ℓ m (normalize-τ τ)
normalize-τ (opt τ) = opt (normalize-τ τ)
normalize-τ (rec τs) = rec (helper τs)
  where
  helper : ∀ {#x #ℓ #s n} → Vec (Type #x #ℓ #s 0) n → Vec (Type #x #ℓ #s 0) n
  helper [] = []
  helper (τ′ ∷ τs′) = normalize-τ τ′ ∷ helper τs′
normalize-τ (μ τ) = μ (normalize-τ τ)
normalize-τ (var s) = var s
normalize-τ (τ app ℓ) = {!!}
-}

  {-
data Type (#x : ℕ) : (#ℓ #s : ℕ) → Set where
  int : ∀ {#ℓ #s} → Type #x #ℓ #s
  ~ : ∀ {#ℓ #s} → Type #x #ℓ #s → Type #x #ℓ #s
  & : ∀ {#ℓ #s} → Life #ℓ #x → Mut → Type #x #ℓ #s → Type #x #ℓ #s
  opt : ∀ {#ℓ #s} → Type #x #ℓ #s → Type #x #ℓ #s
  rec : ∀ {#ℓ #s n} → Vec (Type #x #ℓ #s) n → Type #x #ℓ #s
  μ : ∀ {#ℓ #s} → Type #x #ℓ (S #s) → Type #x #ℓ #s
  var : ∀ {#ℓ #s} → Fin #s → Type #x #ℓ #s
  abs : ∀ {#ℓ #s} → Type #x (S #ℓ) #s → Type #x (S #ℓ) #s
  app : ∀ {#ℓ #s} → Type #x (S #ℓ) #s → Life #x #ℓ → Type #x #ℓ #s

srs-A : Type 0 0 0
srs-A = rec ([ int ])

srs-B : Type 0 1 0
srs-B = abs (rec ([ int ,, & {!!} mut int ]))
-}

{-
Vars : ℕ → Set
Vars #ℓ = Vec Var #ℓ

data Type (#x : ℕ) : {#ℓ : ℕ} → Vars #ℓ → (#s : ℕ) → Set where
  int : ∀ {#s} → Type #x [] #s
  ~ : ∀ {#ℓ V #s} → Type #x V #s → Type #x {#ℓ} V #s
  μ : ∀ {#ℓ V #s} → Type #x V (S #s) → Type #x {#ℓ} V #s
  var : ∀ {#ℓ V #s} → Fin #s → Type #x {#ℓ} V (S #s)
  abs : ∀ {#ℓ V #s} → (v : Var) → Type #x (v ∷ V) #s → Type #x {!!} #s
  -}

  {-
data Type (#x : ℕ) : (#ℓ #s : ℕ) → Set where
  int : ∀ {#s} → Type #x #ℓ #s
  ~ : ∀ {#s} → Type #x #ℓ #s → Type #x #ℓ #s
  & : ∀ {#s} → Life #x #ℓ → Mut → Type #x #ℓ #s → Type #x #ℓ #s
  opt : ∀ {#s} → Type #x #ℓ #s → Type #x #ℓ #s
  rec : ∀ {#s n} → Vec (Type #x #ℓ #s) n → Type #x #ℓ #s
  μ : ∀ {#s} → Type #x #ℓ (S #s) → Type #x #ℓ #s
  var : ∀ {#s} → Fin #s → Type #x #ℓ (S #s)
  abs : ∀ {#s} → Type #x (S #ℓ) #s → Type #x #ℓ #s
  app : ∀ {#s} → Type #x (S #ℓ) #s → Life #x #ℓ → Type #x #ℓ #s
-}
