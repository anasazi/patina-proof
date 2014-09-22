open import Common
open import Life
open import Mut
module test6 where

data Type (#s #x : ℕ) : Set where
  int : Type #s #x
  ~ : Type #s #x → Type #s #x
  & : Life #x 0 → Mut → Type #s #x → Type #s #x
  opt : Type #s #x → Type #s #x
  rec : ∀ {n} → Vec (Type #s #x) n → Type #s #x
  μ : Type (S #s) #x → Type #s #x
  var : Fin #s → Type #s #x

↑#s-τ : ∀ {#s #x} → ℕ → Type #s #x → Type (S #s) #x
↑#s-τ c int = int
↑#s-τ c (~ τ) = ~ (↑#s-τ c τ)
↑#s-τ c (& ℓ m τ) = & ℓ m (↑#s-τ c τ)
↑#s-τ c (opt τ) = opt (↑#s-τ c τ)
↑#s-τ c (rec τs) = rec (helper τs)
  where
  helper : ∀ {n} → Vec _ n → Vec _ n
  helper [] = []
  helper (τ ∷ τs′) = ↑#s-τ c τ ∷ helper τs′
↑#s-τ c (μ τ) = μ (↑#s-τ (S c) τ)
↑#s-τ c (var s) = var (↑ c s)

μsubst : ∀ {#s #x} → Type #s #x → Type (S #s) #x → Type #s #x
μsubst τ′ int = int
μsubst τ′ (~ τ) = ~ (μsubst τ′ τ)
μsubst τ′ (& ℓ m τ) = & ℓ m (μsubst τ′ τ)
μsubst τ′ (opt τ) = opt (μsubst τ′ τ)
μsubst τ′ (rec τs) = rec (helper τs)
  where
  helper : ∀ {n} → Vec _ n → Vec _ n
  helper [] = []
  helper (τ ∷ τs′) = μsubst τ′ τ ∷ helper τs′
μsubst τ′ (μ τ) = μ (μsubst (↑#s-τ 0 τ′) τ)
μsubst {#s} τ′ (var s) with asℕ s <? #s
μsubst τ′ (var fZ) | yes z<s = var fZ
μsubst τ′ (var (fS s)) | yes (s<s s<#s) = var s
μsubst τ′ (var s) | no _ = τ′

unroll : ∀ {#s #x} → Type (S #s) #x → Type #s #x
unroll τ = μsubst (μ τ) τ

data _⊢_wf {#s #x : ℕ} (♭s : Fin (S #s)) : Type #s #x → Set where
  int : ♭s ⊢ int wf
  ~ : ∀ {τ} → fin 0 ⊢ τ wf → ♭s ⊢ ~ τ wf
  & : ∀ {ℓ m τ} → fin 0 ⊢ τ wf → ♭s ⊢ & ℓ m τ wf
  opt : ∀ {τ} → ♭s ⊢ τ wf → ♭s ⊢ opt τ wf
  rec : ∀ {n τs} → All (λ τ → ♭s ⊢ τ wf) {n} τs → ♭s ⊢ rec τs wf
  μ : ∀ {τ} → fin 1 ⊢ τ wf → ♭s ⊢ μ τ wf
  var : ∀ {s} → asℕ s ≥ asℕ ♭s → ♭s ⊢ var s wf

μsubst-preserves-wf : ∀ {#s #x ♭s} (τ′ : Type #s #x) → {!!} ⊢ τ′ wf → (τ : Type (S #s) #x) → fS ♭s ⊢ τ wf → ♭s ⊢ μsubst τ′ τ wf
μsubst-preserves-wf τ′ wf′ int int = int
μsubst-preserves-wf τ′ wf′ (~ τ) (~ wf) = ~ (μsubst-preserves-wf {!!} {!!} τ {!wf!})
μsubst-preserves-wf τ′ wf′ (& ℓ m τ) wf = {!!}
μsubst-preserves-wf τ′ wf′ (opt τ) wf = {!!}
μsubst-preserves-wf τ′ wf′ (rec τs) wf = {!!}
μsubst-preserves-wf τ′ wf′ (μ τ) wf = {!!}
μsubst-preserves-wf τ′ wf′ (var s) wf = {!!}

srs-A : Type 0 0
srs-A = rec ([ int ])

srs-E : Type 0 0
srs-E = rec ([ ~ int ])

srs-List : Type 0 0
srs-List = μ (rec ([ int ,, opt (~ (var fZ)) ]))

srs-infin : Type 0 0
srs-infin = μ (var fZ)

srs-infin2 : Type 0 0
srs-infin2 = μ (rec ([ int ,, var fZ ]))

wf-A : fZ ⊢ srs-A wf
wf-A = rec (int ∷ [])

wf-E : fZ ⊢ srs-E wf
wf-E = rec (~ int ∷ [])

wf-List : fZ ⊢ srs-List wf
wf-List = μ (rec (int ∷ opt (~ (var z<s)) ∷ []))

¬wf-infin : ¬ (fZ ⊢ srs-infin wf)
¬wf-infin (μ (var (s<s ())))

¬wf-infin2 : ¬ (fZ ⊢ srs-infin2 wf)
¬wf-infin2 (μ (rec (int ∷ var (s<s ()) ∷ [])))
