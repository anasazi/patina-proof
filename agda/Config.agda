open import Common
open import Type
open import Layout
open import Shape
open import Stmt
open import Trace
module Config where

record Config {#f} (F : Funcs #f) : Set where
  constructor config
  field
    {#x #a #ℓ} : ℕ
    Γ : Context #ℓ #x
    M : Mem #x #a
    t : Trace #f #x #ℓ

data Finished {#f} {F : Funcs #f} : Config F → Set where
  finished : ∀ {#x #a #ℓ} {Γ : Context #ℓ #x} {M : Mem #x #a} → Finished (config Γ M ∅)

record cok {#f} (F : Funcs #f) (C : Config F) : Set where
  constructor config
  field
    -- TODO proof that F is ok
    {Δ} : State (Config.#ℓ C) (Config.#x C)
    Γ⊢Δ : Config.Γ C ⊢ Δ state
    Δ⊢M : Δ ⊢ Config.M C mem-state
    NG : NoGarbage (Config.M C)
    ⊢t : tok F {#ℓ′ = 0} (Config.Γ C) Δ (Config.t C) []

record cev {#f} (F : Funcs #f) (C₁ C₂ : Config F) : Set where
  constructor config
  field
    ev : tev F (Config.Γ C₁) (Config.M C₁) (Config.t C₁) (Config.Γ C₂) (Config.M C₂) (Config.t C₂)

progress : ∀ {#f} (F : Funcs #f) (C : Config F) → cok F C
         → Finished C + (Σ[ C′ ∈ Config F ] cev F C C′)
progress F (config .[] (.[] , H) .∅) (config [] [] [] ∅) = inl finished
progress F (config .[] (.[] , H) .∅) (config [] [] (() ∷ NG) ∅)
progress F (config Γ M ._) (config Γ⊢Δ Δ⊢M NG (sok >> ⊢t)) = {!!}
progress F (config ._ M ._) (config Γ⊢Δ Δ⊢M NG (sok ∶ dropped pop ⊢t)) = {!!}
progress F (config Γ M ._) (config Γ⊢Δ Δ⊢M NG (sok ∶ ↓state , ↓ctx end ⊢t)) = {!!}

preservation : ∀ {#f} (F : Funcs #f) (C C′ : Config F) → cok F C → cev F C C′ → cok F C′
preservation F (config Γ M .(skip >> t′)) (config .Γ .M t′) (config Γ⊢Δ Δ⊢M NG (skip >> ⊢t)) (config skip>>) = config Γ⊢Δ Δ⊢M NG ⊢t
preservation F (config ._ ._ .(skip pop t′)) (config Γ′ ._ t′) Cok (config (skippop ↓stack ↓heap)) = {!!}
preservation F (config Γ M .(skip end t′)) (config Γ′ .M t′) Cok (config (skipend ↓ctx)) = {!!}
preservation F (config Γ M ._) (config Γ′ M′ t′) Cok (config (⟶>> sok)) = {!!}
preservation F (config Γ M ._) (config Γ′ M′ t′) Cok (config (⟶pop sok)) = {!!}
preservation F (config Γ M ._) (config Γ′ M′ t′) Cok (config (⟶end sok)) = {!!}
