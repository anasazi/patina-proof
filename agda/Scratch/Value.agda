open import Common

module Value where

data Value : (#v : ℕ) → Set where
  void : ∀ {#v} → Value #v
  int : ∀ {#v} → ℕ → Value #v
  ptr : ∀ {#v} → Fin #v → Value #v

↑-val-v : ∀ {#v} → (d : ℕ) → ℕ → Value #v → Value (plus d #v)
↑-val-v d c void = void
↑-val-v d c (int n) = int n
↑-val-v d c (ptr α) with asℕ α <? c
↑-val-v d c (ptr α) | yes α<c = ptr (expand′ d α)
↑-val-v d c (ptr α) | no  α≥c = ptr (raise d α)

{-
private
  copy : ∀ {#v} → Vec (Value #v) #v → Fin #v → Fin #v → Vec (Value #v) #v
  copy H αᵢ αₒ = set H αₒ (H ! αᵢ)

  copyn : ∀ {#v n} → Vec (Value #v) #v → Vec (Fin #v) n
        → Vec (Fin #v) n → Vec (Value #v) #v
  copyn H [] [] = H
  copyn H (αᵢ ∷ αsᵢ) (αₒ ∷ αsₒ) = copyn (copy H αᵢ αₒ) αsᵢ αsₒ

  contig : ∀ {m} n → Fin m → Vec (Fin (plus n m)) n
  contig n f = map (fplus′ f) (range′ n)

  test-contig : contig {5} 3 (fin 1) ≡ ([ fin 1 ,, fin 2 ,, fin 3 ])
  test-contig = refl

  contig′ : ∀ {m} n → (i : Fin m) → (plus n (asℕ i) ≤ m) → Vec (Fin m) n
  contig′ Z i pf = []
  contig′ (S n) i pf = snoc (contig′ n i (Sn-<-m pf)) (fin′ (S-< pf)) --(fin′ (Sn-<-m pf))

  test-contig′ : contig′ {5} 3 (fin 1) (s<s (s<s (s<s (s<s z<s)))) ≡ ([ fin 1 ,, fin 2 ,, fin 3 ])
  test-contig′ = refl
  -}

  --contig′ : ∀ {m} n → Fin (S m) → Vec (Fin (plus n m)) n
  --contig′ n f = {!!}

  {-
memcopy : ∀ {#v} n → (i o : Fin #v) → plus n (asℕ i) ≤ #v → plus n (asℕ o) ≤ #v
        → Vec (Value #v) #v → Vec (Value #v) #v
memcopy n i o ipf opf H = copyn H (contig′ n i ipf) (contig′ n o opf)
-}

  {-
memcopy : ∀ {#v} (n-1 : ℕ) → Vec (Value (plus (S n-1) #v)) (plus (S n-1) #v)
        → Fin (S #v) → Fin (S #v)
        → Vec (Value (plus (S n-1) #v)) (plus (S n-1) #v)
memcopy n-1 H ai ao = copyn H {!contig (S n-1) ai!} {!!}
-}

  {-
memcopy : ∀ {#v} (n : ℕ) → Vec (Value (plus n #v)) (plus n #v)
        → Fin (S #v) → Fin (S #v) → Vec (Value (plus n #v)) (plus n #v)
memcopy n H αᵢ αₒ = copyn H {!contig n αᵢ!} {!!}
-}

{-
memcopy : ∀ {#v : ℕ} (n : ℕ) {o : ℕ} {pf : IsYes (plus n o == #v)}
        → Vec (Value #v) #v
        → Fin o → Fin o
        → Vec (Value #v) #v
memcopy n {_} {pf} H αᵢ αₒ = copyn H (f (contig n αᵢ)) (f (contig n αₒ))
  where f = transport (λ x → Vec (Fin x) n) (toWitness pf)
  -}

data mc {#v n} : Fin (S n) → Vec (Value #v) #v → Fin #v
               → Fin #v → Vec (Value #v) #v → Set where
  mcZ : ∀ {H i o} → mc fZ H i o H
  mcS : ∀ {f H i o}
      → mc (expand′ 1 f) (set H {!expand′ !} {!!}) {!!} {!!} {!!}
      → mc (fS f) H i o {!!}

  {-
data mc {#v n} : Fin (S n) → Vec (Value (plus n #v)) (plus n #v)
               → Fin #v → Fin #v → Vec (Value (plus n #v)) (plus n #v) → Set where
  mcZ : ∀ {H i o} → mc fZ H i o H
  mcS : ∀ {z H i o}
      → mc (expand′ 1 z) (set H (expand′ n o) (H ! expand′ n i)) {!!} {!!} {!!}
      → mc (fS z) H i o {!!} 
      -}

  {-
data mc {#v} : (n : ℕ) → Vec (Value (plus n #v)) (plus n #v)
             → Fin #v → Fin #v
             → Vec (Value (plus n #v)) (plus n #v) → Set where
  mcZ : ∀ {H αᵢ αₒ} → mc 0 H αᵢ αₒ H
  mcS : ∀ {n Hᵢ αᵢ αₒ Hₒ}
      → mc n (copy {!Hᵢ!} {!!} {!!}) {!!} {!!} {!!}
      → mc (S n) Hᵢ αᵢ αₒ Hₒ
      -}
             {-
  mcZ : ∀ {H αᵢ αₒ} → mc H αᵢ αₒ 0 H
  mcS : ∀ {Hᵢ αᵢ αₒ n Hₒ}
      → mc (copy Hᵢ αᵢ αₒ) {!!} {!!} n {!!}
      → mc Hᵢ αᵢ αₒ (S n) {!!}
      -}
      {-
private
  test-memcopy-1 : memcopy 1 (fin 0) (fin 1) (s<s z<s) (s<s (s<s z<s)) ([ int 0 ,, void ]) ≡ ([ int 0 ,, int 0 ])
  test-memcopy-1 = refl
  -}

--test-memcopy-1 : memcopy 1 ([ int 0 ,, void ]) (fin 0) (fin 1) ≡ ([ int 0 ,, int 0 ])
--test-memcopy-1 = {!!}

{-
private
  test-memcopy-1 : memcopy 1 ([ int 0 ,, int 1 ,, void ,, void ]) (fin 0) (fin 2)
                 ≡ ([ int 0 ,, int 1 ,, int 0 ,, void ])
  test-memcopy-1 = refl
  test-memcopy-2 : memcopy 1 ([ int 0 ,, int 1 ,, int 0 ,, void ]) (fin 2) (fin 3)
                 ≡ ([ int 0 ,, int 1 ,, int 0 ,, int 0 ])
  test-memcopy-2 = {!!}
  {-
  test-memcopy-2 : memcopy 2 ([ int 0 ,, int 1 ,, void ,, void ]) (fin 0) {!!}
                 ≡ ([ int 0 ,, int 1 ,, int 0 ,, int 1 ])
  test-memcopy-2 = {!!}
  -}

  -}
