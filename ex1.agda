{-
-- ## Section 1
-- natural deduction for classical and minimal propositional logic
-}

open import common

{-
-- ### Sub Section 1.1 classical logic
-}

infixr 40 _\/_
infixr 35 _/\_
infixr 30 _⇒_

data Formula (N : Nat) : Set where
  var : Fin N → Formula N
  ⊤ : Formula N
  ⊥ : Formula N
  _⇒_ :  Formula N → Formula N → Formula N
  _/\_ : Formula N → Formula N → Formula N
  _\/_ : Formula N → Formula N → Formula N

-- 1.1.d
data Ground {N : Nat} : Formula N → Set where
  ⊤ : Ground ⊤
  ⊥ : Ground ⊥
  _⇒_ : {ϕ ψ : Formula N} → Ground ϕ → Ground ψ → Ground (ϕ ⇒ ψ)
  _/\_ : {ϕ ψ : Formula N} → Ground ϕ → Ground ψ → Ground (ϕ /\ ψ)
  _\/_ : {ϕ ψ : Formula N} → Ground ϕ → Ground ψ → Ground (ϕ \/ ψ)
infixr 50 ~_
~_ : {N : Nat} → Formula N → Formula N
~_ = _⇒ ⊥

data GValue {N : Nat} : {ϕ : Formula N} (gϕ : Ground ϕ) (b : Bool) → Set where
  t⊤ : GValue ⊤ True
  f⊥ : GValue ⊥ False
  t/\t : {ϕ : Formula N} {gϕ : Ground ϕ} {ψ : Formula N} {gψ : Ground ψ}
       → GValue gϕ True → GValue gψ True → GValue (gϕ /\ gψ) True
  t/\f : {ϕ : Formula N} {gϕ : Ground ϕ} {ψ : Formula N} {gψ : Ground ψ}
       → GValue gϕ True → GValue gψ False → GValue (gϕ /\ gψ) False
  f/\t : {ϕ : Formula N} {gϕ : Ground ϕ} {ψ : Formula N} {gψ : Ground ψ}
       → GValue gϕ False → GValue gψ True → GValue (gϕ /\ gψ) False
  f/\f : {ϕ : Formula N} {gϕ : Ground ϕ} {ψ : Formula N} {gψ : Ground ψ}
       → GValue gϕ False → GValue gψ False → GValue (gϕ /\ gψ) False
  t\/t : {ϕ : Formula N} {gϕ : Ground ϕ} {ψ : Formula N} {gψ : Ground ψ}
       → GValue gϕ True → GValue gψ True → GValue (gϕ \/ gψ) True
  t\/f : {ϕ : Formula N} {gϕ : Ground ϕ} {ψ : Formula N} {gψ : Ground ψ}
       → GValue gϕ True → GValue gψ False → GValue (gϕ \/ gψ) True
  f\/t : {ϕ : Formula N} {gϕ : Ground ϕ} {ψ : Formula N} {gψ : Ground ψ}
       → GValue gϕ False → GValue gψ True → GValue (gϕ \/ gψ) True
  f\/f : {ϕ : Formula N} {gϕ : Ground ϕ} {ψ : Formula N} {gψ : Ground ψ}
       → GValue gϕ False → GValue gψ False → GValue (gϕ \/ gψ) False
  t=>t : {ϕ : Formula N} {gϕ : Ground ϕ} {ψ : Formula N} {gψ : Ground ψ}
       → GValue gϕ True → GValue gψ True → GValue (gϕ ⇒ gψ) True
  t=>f : {ϕ : Formula N} {gϕ : Ground ϕ} {ψ : Formula N} {gψ : Ground ψ}
       → GValue gϕ True → GValue gψ False → GValue (gϕ ⇒ gψ) False
  f=>t : {ϕ : Formula N} {gϕ : Ground ϕ} {ψ : Formula N} {gψ : Ground ψ}
       → GValue gϕ False → GValue gψ True → GValue (gϕ ⇒ gψ) True
  f=>f : {ϕ : Formula N} {gϕ : Ground ϕ} {ψ : Formula N} {gψ : Ground ψ}
       → GValue gϕ False → GValue gψ False → GValue (gϕ ⇒ gψ) True

GValueDec : {N : Nat} {ϕ : Formula N} (gϕ : Ground ϕ) → GValue gϕ True ⊎ GValue gϕ False
GValueDec ⊤ = left t⊤
GValueDec ⊥ = right f⊥
GValueDec (ϕ ⇒  ψ) with GValueDec ϕ | GValueDec ψ
... | left  tϕ | left  tψ = left (t=>t tϕ tψ)
... | left  tϕ | right fψ = right (t=>f tϕ fψ)
... | right fϕ | left  tψ = left (f=>t fϕ tψ)
... | right fϕ | right fψ = left (f=>f fϕ fψ)
GValueDec (ϕ /\ ψ) with GValueDec ϕ | GValueDec ψ
... | left  tϕ | left  tψ = left (t/\t tϕ tψ)
... | left  tϕ | right fψ = right (t/\f tϕ fψ)
... | right fϕ | left  tψ = right (f/\t fϕ tψ)
... | right fϕ | right fψ = right (f/\f fϕ fψ)
GValueDec (ϕ \/ ψ) with GValueDec ϕ | GValueDec ψ
... | left  tϕ | left  tψ = left (t\/t tϕ tψ)
... | left  tϕ | right fψ = left (t\/f tϕ fψ)
... | right fϕ | left  tψ = left (f\/t fϕ tψ)
... | right fϕ | right fψ = right (f\/f fϕ fψ)

build-literal : {N : Nat} → Bool → Fin N → Formula N
build-literal True x = var x
build-literal False x = ~ (var x)

-- in agda-stdlib (_∷_) has precedence 5
Context : Nat → Set
Context N = List (Formula N)

Assignment : Nat → Set
Assignment N = Σ λ (a : List Bool) → length a ≡ N

value : {N : Nat} → Assignment N → Fin N → Bool
value ⟨ values , refl ⟩ x = let ⟨ i , i<N ⟩ = Fin→Nat x
                             in fromJust (values ! i) (valid-index values i<N)

Assignment→Context : {N : Nat} → Assignment N → Context N
Assignment→Context {N} ⟨ values , _ ⟩ = zip-map build-literal values (enumerate N)

Assignment-Context-Locate : {N : Nat} (v : Assignment N) (x : Fin N)
                          → (build-literal (value v x) x) ∈ (Assignment→Context v)
Assignment-Context-Locate {N} ⟨ values , refl ⟩ x =
  let ⟨ i , i<N ⟩ = Fin→Nat x
      vars = enumerate N
      zip-map-idx-eq = zip-map-idx build-literal values vars i
      values!i = values ! i
      just-values!i = valid-index values i<N
      fmap-build-eq = cong2 (fmap2 build-literal) (Just-fromJust values!i just-values!i) (Nat→Fin x)
   in idx→mem ⟨ i , trans zip-map-idx-eq fmap-build-eq ⟩
   
-- truth value semantics
data Eval {N : Nat} (v : Assignment N) : (ϕ : Formula N) (b : Bool) → Set where
  t⊤ : Eval v ⊤ True
  f⊥ : Eval v ⊥ False
  tvar : {x : Fin N} → value v x ≡ True  → Eval v (var x) True
  fvar : {x : Fin N} → value v x ≡ False → Eval v (var x) False
  t/\t : {ϕ : Formula N} {ψ : Formula N} → Eval v ϕ True  → Eval v ψ True  → Eval v (ϕ /\ ψ) True 
  t/\f : {ϕ : Formula N} {ψ : Formula N} → Eval v ϕ True  → Eval v ψ False → Eval v (ϕ /\ ψ) False
  f/\t : {ϕ : Formula N} {ψ : Formula N} → Eval v ϕ False → Eval v ψ True  → Eval v (ϕ /\ ψ) False
  f/\f : {ϕ : Formula N} {ψ : Formula N} → Eval v ϕ False → Eval v ψ False → Eval v (ϕ /\ ψ) False
  t\/t : {ϕ : Formula N} {ψ : Formula N} → Eval v ϕ True  → Eval v ψ True  → Eval v (ϕ \/ ψ) True 
  t\/f : {ϕ : Formula N} {ψ : Formula N} → Eval v ϕ True  → Eval v ψ False → Eval v (ϕ \/ ψ) True 
  f\/t : {ϕ : Formula N} {ψ : Formula N} → Eval v ϕ False → Eval v ψ True  → Eval v (ϕ \/ ψ) True 
  f\/f : {ϕ : Formula N} {ψ : Formula N} → Eval v ϕ False → Eval v ψ False → Eval v (ϕ \/ ψ) False
  t=>t : {ϕ : Formula N} {ψ : Formula N} → Eval v ϕ True  → Eval v ψ True  → Eval v (ϕ ⇒ ψ) True 
  t=>f : {ϕ : Formula N} {ψ : Formula N} → Eval v ϕ True  → Eval v ψ False → Eval v (ϕ ⇒ ψ) False
  f=>t : {ϕ : Formula N} {ψ : Formula N} → Eval v ϕ False → Eval v ψ True  → Eval v (ϕ ⇒ ψ) True 
  f=>f : {ϕ : Formula N} {ψ : Formula N} → Eval v ϕ False → Eval v ψ False → Eval v (ϕ ⇒ ψ) True 

-- the boolean semantics is deterministic
Eval-Unique : {N : Nat} {v : Assignment N} {ϕ : Formula N} → Eval v ϕ True → Eval v ϕ False → Empty
Eval-Unique (tvar v=t) (fvar v=f) = aux v=t v=f
  where aux : {b : Bool} → b ≡ True → b ≡ False → Empty
        aux {True} refl ()
        aux {False} () refl
Eval-Unique (t/\t t₀ t₁) (t/\f t'₀ f'₁) = Eval-Unique t₁ f'₁
Eval-Unique (t/\t t₀ t₁) (f/\t f'₀ t'₁) = Eval-Unique t₀ f'₀
Eval-Unique (t/\t t₀ t₁) (f/\f f'₀ f'₁) = Eval-Unique t₀ f'₀
Eval-Unique (t\/t t₀ t₁) (f\/f f'₀ f'₁) = Eval-Unique t₀ f'₀
Eval-Unique (t\/f t₀ t₁) (f\/f f'₀ f'₁) = Eval-Unique t₀ f'₀
Eval-Unique (f\/t f₀ t₁) (f\/f f'₀ f'₁) = Eval-Unique t₁ f'₁
Eval-Unique (t=>t t₀ t₁) (t=>f t'₀ f'₁) = Eval-Unique t₁ f'₁
Eval-Unique (f=>t f₀ t₁) (t=>f t'₀ f'₁) = Eval-Unique t₁ f'₁
Eval-Unique (f=>f f₀ f₁) (t=>f t'₀ f'₁) = Eval-Unique t'₀ f₀


-- compute boolean value
eval : {N : Nat} (v : Assignment N) (ϕ : Formula N) → Σ (Eval v ϕ)
eval v (var x) = aux (value v x) refl
  where aux : (b : Bool) → value v x ≡ b → Σ (Eval v (var x))
        aux True  eq = ⟨ True  , tvar eq ⟩
        aux False eq = ⟨ False , fvar eq ⟩
eval v ⊤ = ⟨ True , t⊤ ⟩
eval v ⊥ = ⟨ False , f⊥ ⟩
eval v (ϕ ⇒  ψ) with eval v ϕ | eval v ψ
... | ⟨ True  , tϕ ⟩ | ⟨ True  , tψ ⟩ = ⟨ True  , t=>t tϕ tψ ⟩
... | ⟨ True  , tϕ ⟩ | ⟨ False , fψ ⟩ = ⟨ False , t=>f tϕ fψ ⟩
... | ⟨ False , fϕ ⟩ | ⟨ True  , tψ ⟩ = ⟨ True  , f=>t fϕ tψ ⟩
... | ⟨ False , fϕ ⟩ | ⟨ False , fψ ⟩ = ⟨ True  , f=>f fϕ fψ ⟩
eval v (ϕ /\ ψ) with eval v ϕ | eval v ψ
... | ⟨ True  , tϕ ⟩ | ⟨ True  , tψ ⟩ = ⟨ True  , t/\t tϕ tψ ⟩
... | ⟨ True  , tϕ ⟩ | ⟨ False , fψ ⟩ = ⟨ False , t/\f tϕ fψ ⟩
... | ⟨ False , fϕ ⟩ | ⟨ True  , tψ ⟩ = ⟨ False , f/\t fϕ tψ ⟩
... | ⟨ False , fϕ ⟩ | ⟨ False , fψ ⟩ = ⟨ False , f/\f fϕ fψ ⟩
eval v (ϕ \/ ψ) with eval v ϕ | eval v ψ
... | ⟨ True  , tϕ ⟩ | ⟨ True  , tψ ⟩ = ⟨ True  , t\/t tϕ tψ ⟩
... | ⟨ True  , tϕ ⟩ | ⟨ False , fψ ⟩ = ⟨ True  , t\/f tϕ fψ ⟩
... | ⟨ False , fϕ ⟩ | ⟨ True  , tψ ⟩ = ⟨ True  , f\/t fϕ tψ ⟩
... | ⟨ False , fϕ ⟩ | ⟨ False , fψ ⟩ = ⟨ False , f\/f fϕ fψ ⟩

module ND-classical where
  infix 3 _⊢_
  -- A sequent of classical logic natural deduction
  data _⊢_ {N : Nat} : Context N → Formula N → Set where
    -- prove true in any context
    ⊢-true : {Γ : Context N} → Γ ⊢ ⊤
    -- assumption
    ⊢-ax : {Γ : Context N} {ϕ : Formula N} → ϕ ∈ Γ → Γ ⊢ ϕ
    -- implication introduction
    ⊢-intr : {Γ : Context N} {ϕ ψ : Formula N} → ϕ ∷ Γ ⊢ ψ → Γ ⊢ ϕ ⇒ ψ
    -- implication elimination
    ⊢-elim : {Γ : Context N} {ϕ ψ : Formula N} → Γ ⊢ ϕ ⇒ ψ → Γ ⊢ ϕ → Γ ⊢ ψ
    -- proof by contradiction
    ⊢-pbc : {Γ : Context N} {ϕ : Formula N} → ~ ϕ ∷ Γ ⊢ ⊥ → Γ ⊢ ϕ
    -- conjunction introduction
    ⊢-conj : {Γ : Context N} {ϕ ψ : Formula N} → Γ ⊢ ϕ → Γ ⊢ ψ → Γ ⊢ ϕ /\ ψ
    -- conjunction elimination left/right
    ⊢-proj0 : {Γ : Context N} {ϕ ψ : Formula N} → Γ ⊢ ϕ /\ ψ → Γ ⊢ ϕ
    ⊢-proj1 : {Γ : Context N} {ϕ ψ : Formula N} → Γ ⊢ ϕ /\ ψ → Γ ⊢ ψ
    -- disjunction introduction left/right
    ⊢-inj0 : {Γ : Context N} {ϕ ψ : Formula N} → Γ ⊢ ϕ → Γ ⊢ ϕ \/ ψ
    ⊢-inj1 : {Γ : Context N} {ϕ ψ : Formula N} → Γ ⊢ ψ → Γ ⊢ ϕ \/ ψ
    -- disjunction elimination
    ⊢-case : {Γ : Context N} {γ ϕ ψ : Formula N} → Γ ⊢ ϕ \/ ψ → Γ ⊢ ϕ ⇒ γ → Γ ⊢ ψ ⇒ γ → Γ ⊢ γ

  -- law of excluded middle for classical logic
  ⊢-lem : {N : Nat} {Γ : Context N} (ϕ : Formula N) → Γ ⊢ ϕ \/ (~ ϕ)
  ⊢-lem {N} {Γ} ϕ = ⊢-pbc ~lem⊢
    where ~lem⊢ : ~ (ϕ \/ (~ ϕ)) ∷ Γ ⊢ ⊥
          ~lem⊢ = let ~[ϕ+ϕ']⊢~[ϕ+ϕ']   = ⊢-ax (here refl)
                      ~[ϕ+ϕ'],ϕ⊢~[ϕ+ϕ'] = ⊢-ax (there (here refl))
                      ~[ϕ+ϕ'],ϕ⊢ϕ+ϕ'    = ⊢-inj0 (⊢-ax (here refl))
                      ~[ϕ+ϕ'],ϕ⊢        = ⊢-elim ~[ϕ+ϕ'],ϕ⊢~[ϕ+ϕ'] ~[ϕ+ϕ'],ϕ⊢ϕ+ϕ'
                      ~[ϕ+ϕ']⊢~ϕ        = ⊢-intr ~[ϕ+ϕ'],ϕ⊢
                      ~[ϕ+ϕ']⊢ϕ+ϕ'      = ⊢-inj1 ~[ϕ+ϕ']⊢~ϕ
                      ~[ϕ+ϕ']⊢          = ⊢-elim ~[ϕ+ϕ']⊢~[ϕ+ϕ'] ~[ϕ+ϕ']⊢ϕ+ϕ'
                   in ~[ϕ+ϕ']⊢

  -- b.1
  example-1 : {N : Nat} {Γ : Context N} (ϕ : Formula N) → Γ ⊢ ϕ ⇒ ϕ
  example-1 ϕ = ⊢-intr (⊢-ax (here refl))

  -- b.2
  example-2 : {N : Nat} {Γ : Context N} {ϕ : Formula N} → ϕ ∷ Γ ⊢ ~ ~ ϕ
  example-2 = ⊢-intr let ⊢ϕ⇒⊥ = ⊢-ax (here refl)
                         ⊢ϕ   = ⊢-ax (there (here refl))
                      in ⊢-elim ⊢ϕ⇒⊥ ⊢ϕ

  -- b.3
  example-3 : {N : Nat} → ~ ~ ⊥ ∷ [] ⊢ ⊥ {N}
  example-3 = let ⊢⊥⇒⊥       = ⊢-intr (⊢-ax (here refl))
                  ⊢~⊥⇒⊥ = ⊢-ax (here refl)
               in ⊢-elim ⊢~⊥⇒⊥ ⊢⊥⇒⊥

  -- b.4
  -- double-negation-elimination is non-intuitionistic, need PBC
  example-4 : {N : Nat} {Γ : Context N} {ϕ : Formula N} → Γ ⊢ ~ ~ ϕ ⇒ ϕ
  example-4 = let ⊢~ϕ  = ⊢-ax (here refl)
                  ⊢~~ϕ = ⊢-ax (there (here refl))
                  ⊢⊥ = ⊢-elim ⊢~~ϕ ⊢~ϕ
               in ⊢-intr (⊢-pbc ⊢⊥)

  -- c
  weaken : {N : Nat} {Γ Δ : Context N} {ϕ : Formula N} → Γ ⊆ Δ → Γ ⊢ ϕ → Δ ⊢ ϕ
  weaken Γ⊆Δ ⊢-true = ⊢-true
  weaken Γ⊆Δ (⊢-ax ϕ∈Γ) = ⊢-ax (Γ⊆Δ ϕ∈Γ)
  weaken Γ⊆Δ (⊢-intr ϕ,Γ⊢ψ) = let ϕ,Γ⊆ϕ,Δ = ∷-subset Γ⊆Δ in ⊢-intr (weaken ϕ,Γ⊆ϕ,Δ ϕ,Γ⊢ψ)
  weaken Γ⊆Δ (⊢-elim Γ⊢ϕ⇒ψ Γ⊢ϕ) = let Δ⊢ϕ⇒ψ = weaken Γ⊆Δ Γ⊢ϕ⇒ψ
                                      Δ⊢ϕ   = weaken Γ⊆Δ Γ⊢ϕ
                                   in ⊢-elim Δ⊢ϕ⇒ψ Δ⊢ϕ
  weaken Γ⊆Δ (⊢-pbc ~ϕ,Γ⊢⊥) = let ~ϕ,Γ⊆~ϕ,Δ = ∷-subset Γ⊆Δ
                                  ~ϕ,Δ⊢⊥    = weaken ~ϕ,Γ⊆~ϕ,Δ ~ϕ,Γ⊢⊥
                               in ⊢-pbc ~ϕ,Δ⊢⊥
  weaken Γ⊆Δ (⊢-conj Γ⊢ϕ Γ⊢ψ) = let Δ⊢ϕ = weaken Γ⊆Δ Γ⊢ϕ
                                    Δ⊢ψ = weaken Γ⊆Δ Γ⊢ψ
                                 in ⊢-conj Δ⊢ϕ Δ⊢ψ
  weaken Γ⊆Δ (⊢-proj0 Γ⊢ϕ·ψ) = let Δ⊢ϕ·ψ = weaken Γ⊆Δ Γ⊢ϕ·ψ in ⊢-proj0 Δ⊢ϕ·ψ
  weaken Γ⊆Δ (⊢-proj1 Γ⊢ϕ·ψ) = let Δ⊢ϕ·ψ = weaken Γ⊆Δ Γ⊢ϕ·ψ in ⊢-proj1 Δ⊢ϕ·ψ
  weaken Γ⊆Δ (⊢-inj0 Γ⊢ϕ+ψ) = let Δ⊢ϕ+ψ = weaken Γ⊆Δ Γ⊢ϕ+ψ in ⊢-inj0 Δ⊢ϕ+ψ
  weaken Γ⊆Δ (⊢-inj1 Γ⊢ϕ+ψ) = let Δ⊢ϕ+ψ = weaken Γ⊆Δ Γ⊢ϕ+ψ in ⊢-inj1 Δ⊢ϕ+ψ
  weaken Γ⊆Δ (⊢-case Γ⊢ϕ+ψ Γ⊢ϕ⇒γ Γ⊢ψ⇒γ) = let Δ⊢ϕ+ψ = weaken Γ⊆Δ Γ⊢ϕ+ψ
                                              Δ⊢ϕ⇒γ = weaken Γ⊆Δ Γ⊢ϕ⇒γ
                                              Δ⊢ψ⇒γ = weaken Γ⊆Δ Γ⊢ψ⇒γ
                                           in ⊢-case Δ⊢ϕ+ψ Δ⊢ϕ⇒γ Δ⊢ψ⇒γ

  

  Sat : {N : Nat} (v : Assignment N) (Γ : Context N) → Set
  Sat v = All (λ ϕ → Eval v ϕ True)

  infix 3 _⊨_
  _⊨_ : {N : Nat} (Γ : Context N) (ϕ : Formula N) → Set
  Γ ⊨ ϕ = (v : Assignment _) → Sat v Γ → Eval v ϕ True

  -- every derivable sequent is a semantical entailment
  sound : {N : Nat} {Γ : Context N} {ϕ : Formula N} → Γ ⊢ ϕ → Γ ⊨ ϕ
  sound ⊢-true val sat = t⊤
  sound (⊢-ax i) val sat = All-∈ sat i
  sound (⊢-intr {_} {ϕ} {ψ} ϕ⊢ψ) val sat with eval val ϕ 
  ... | ⟨ True  , tϕ ⟩ = let tψ = sound ϕ⊢ψ val (tϕ ∷ sat) in t=>t tϕ tψ
  ... | ⟨ False , fϕ ⟩ with eval val ψ
  ... | ⟨ True  , tψ ⟩ = f=>t fϕ tψ
  ... | ⟨ False , fψ ⟩ = f=>f fϕ fψ
  sound (⊢-elim {Γ} {ϕ} {ψ} ⊢ϕ⇒ψ ⊢ϕ) val sat with sound ⊢ϕ val sat | sound ⊢ϕ⇒ψ val sat
  ... | tϕ' | t=>t tϕ tψ = tψ
  ... | tϕ' | f=>t fϕ tψ = tψ
  ... | tϕ' | f=>f fϕ fψ = absurd (Eval-Unique tϕ' fϕ)
  sound (⊢-pbc {_} {ϕ} ~ϕ⊢) val sat with eval val ϕ
  ... | ⟨ True  , tϕ ⟩ = tϕ
  ... | ⟨ False , fϕ ⟩ = let t⊥ = sound ~ϕ⊢ val (f=>f fϕ f⊥ ∷ sat) in absurd (Eval-Unique t⊥ f⊥)
  sound (⊢-conj ⊢ϕ ⊢ψ) val sat = t/\t (sound ⊢ϕ val sat) (sound ⊢ψ val sat)
  sound (⊢-proj0 ⊢ϕ·ψ) val sat with sound ⊢ϕ·ψ val sat
  ... | t/\t ⊨ϕ ⊨ψ = ⊨ϕ
  sound (⊢-proj1 ⊢ϕ·ψ) val sat with sound ⊢ϕ·ψ val sat
  ... | t/\t ⊨ϕ ⊨ψ = ⊨ψ
  sound (⊢-inj0 {_} {ϕ} {ψ} ⊢ϕ) val sat with sound ⊢ϕ val sat | eval val ψ
  ... | tϕ | ⟨ True  , tψ ⟩ = t\/t tϕ tψ
  ... | tϕ | ⟨ False , fψ ⟩ = t\/f tϕ fψ
  sound (⊢-inj1 {_} {ϕ} {ψ} ⊢ψ) val sat with sound ⊢ψ val sat | eval val ϕ
  ... | tψ | ⟨ True  , tϕ ⟩ = t\/t tϕ tψ
  ... | tψ | ⟨ False , fϕ ⟩ = f\/t fϕ tψ
  sound (⊢-case {_} {γ} {ϕ} {ψ} ⊢ϕ+ψ ⊢ϕ⇒γ ⊢ψ⇒γ) val sat
    with sound ⊢ϕ+ψ val sat | sound ⊢ϕ⇒γ val sat | sound ⊢ψ⇒γ val sat
  ... | t\/t tϕ _  | t=>t _  tγ | _ = tγ
  ... | t\/t tϕ _  | f=>t _  tγ | _ = tγ
  ... | t\/t tϕ _  | f=>f fϕ _  | _ = absurd (Eval-Unique tϕ fϕ)
  ... | t\/f tϕ _  | t=>t _  tγ | _ = tγ
  ... | t\/f tϕ _  | f=>t _  tγ | _ = tγ
  ... | t\/f tϕ _  | f=>f fϕ _  | _ = absurd (Eval-Unique tϕ fϕ)
  ... | f\/t _ tψ  | _ | t=>t _  tγ = tγ
  ... | f\/t _ tψ  | _ | f=>t _  tγ = tγ
  ... | f\/t _ tψ  | _ | f=>f fψ _  = absurd (Eval-Unique tψ fψ)

  Truth-Table-Lemma-True  : {N : Nat} (val : Assignment N) (ϕ : Formula N)
                          → Eval val ϕ True  → (Assignment→Context val) ⊢   ϕ
  Truth-Table-Lemma-False : {N : Nat} (val : Assignment N) (ϕ : Formula N)
                          → Eval val ϕ False → (Assignment→Context val) ⊢ ~ ϕ


  Truth-Table-Lemma-True v (var x) (tvar vx=t) =
    let Γ = Assignment→Context v
        Γ⊢literal = ⊢-ax (Assignment-Context-Locate v x)
        positive-literal : build-literal (value v x) x ≡ build-literal True x
        positive-literal = cong (λ v → build-literal v x) vx=t
     in subst (Γ ⊢_) Γ⊢literal positive-literal
  Truth-Table-Lemma-True val ⊤ t⊤ = ⊢-true
  Truth-Table-Lemma-True val (ϕ ⇒  ψ) (t=>t tϕ tψ) =
    let Γ⊢ψ = Truth-Table-Lemma-True val ψ tψ
        Γ,ϕ⊢ψ = weaken there Γ⊢ψ
     in ⊢-intr Γ,ϕ⊢ψ
  Truth-Table-Lemma-True val (ϕ ⇒  ψ) (f=>t fϕ tψ) =
    let Γ⊢ψ = Truth-Table-Lemma-True val ψ tψ
        Γ,ϕ⊢ψ = weaken there Γ⊢ψ
     in ⊢-intr Γ,ϕ⊢ψ
  Truth-Table-Lemma-True val (ϕ ⇒  ψ) (f=>f fϕ fψ) =
    let Γ⊢~ϕ      = Truth-Table-Lemma-False val ϕ fϕ
        Γ,ϕ,~ψ⊢~ϕ = weaken (λ x → there (there x)) Γ⊢~ϕ
        Γ,ϕ,~ψ⊢ϕ  = ⊢-ax (there (here refl))
        Γ,ϕ,~ψ⊢   = ⊢-elim Γ,ϕ,~ψ⊢~ϕ Γ,ϕ,~ψ⊢ϕ
        Γ,ϕ⊢ψ     = ⊢-pbc Γ,ϕ,~ψ⊢
     in ⊢-intr Γ,ϕ⊢ψ
  Truth-Table-Lemma-True val (ϕ /\ ψ) (t/\t tϕ tψ) =
    let Γ⊢ϕ = Truth-Table-Lemma-True val ϕ tϕ
        Γ⊢ψ = Truth-Table-Lemma-True val ψ tψ
     in ⊢-conj Γ⊢ϕ Γ⊢ψ 
  Truth-Table-Lemma-True val (ϕ \/ ψ) (t\/t tϕ tψ) =
    let Γ⊢ϕ = Truth-Table-Lemma-True val ϕ tϕ
     in ⊢-inj0 Γ⊢ϕ
  Truth-Table-Lemma-True val (ϕ \/ ψ) (t\/f tϕ fψ) =
    let Γ⊢ϕ = Truth-Table-Lemma-True val ϕ tϕ
     in ⊢-inj0 Γ⊢ϕ
  Truth-Table-Lemma-True val (ϕ \/ ψ) (f\/t fϕ tψ) =
    let Γ⊢ψ = Truth-Table-Lemma-True val ψ tψ
     in ⊢-inj1 Γ⊢ψ

  Truth-Table-Lemma-False v (var x) (fvar vx=f) =
    let Γ = Assignment→Context v
        Γ⊢literal = ⊢-ax (Assignment-Context-Locate v x)
        negative-literal : build-literal (value v x) x ≡ build-literal False x
        negative-literal = cong (λ v → build-literal v x) vx=f
     in subst (Γ ⊢_) Γ⊢literal negative-literal
  Truth-Table-Lemma-False val ⊥ f⊥ = ⊢-intr (⊢-ax (here refl))
  Truth-Table-Lemma-False val (ϕ ⇒  ψ) (t=>f tϕ fψ) =
    let Γ⊢ϕ       = Truth-Table-Lemma-True  val ϕ tϕ
        Γ⊢~ψ      = Truth-Table-Lemma-False val ψ fψ
        Γ,ϕ⇒ψ⊢ϕ   = weaken there Γ⊢ϕ
        Γ,ϕ⇒ψ⊢~ψ  = weaken there Γ⊢~ψ
        Γ,ϕ⇒ψ⊢ϕ⇒ψ = ⊢-ax (here refl)
        Γ,ϕ⇒ψ⊢ψ   = ⊢-elim Γ,ϕ⇒ψ⊢ϕ⇒ψ Γ,ϕ⇒ψ⊢ϕ
        Γ,ϕ⇒ψ⊢    = ⊢-elim Γ,ϕ⇒ψ⊢~ψ Γ,ϕ⇒ψ⊢ψ
     in ⊢-intr Γ,ϕ⇒ψ⊢
  Truth-Table-Lemma-False val (ϕ /\ ψ) (t/\f tϕ fψ) =
    let Γ⊢~ψ      = Truth-Table-Lemma-False val ψ fψ
        Γ,ϕ·ψ⊢~ψ  = weaken there Γ⊢~ψ
        Γ,ϕ·ψ⊢ψ   = ⊢-proj1 (⊢-ax (here refl))
        Γ,ϕ·ψ⊢    = ⊢-elim Γ,ϕ·ψ⊢~ψ Γ,ϕ·ψ⊢ψ
     in ⊢-intr Γ,ϕ·ψ⊢
  Truth-Table-Lemma-False val (ϕ /\ ψ) (f/\t fϕ tψ) =
    let Γ⊢~ϕ      = Truth-Table-Lemma-False val ϕ fϕ
        Γ,ϕ·ψ⊢~ϕ  = weaken there Γ⊢~ϕ
        Γ,ϕ·ψ⊢ϕ   = ⊢-proj0 (⊢-ax (here refl))
        Γ,ϕ·ψ⊢    = ⊢-elim Γ,ϕ·ψ⊢~ϕ Γ,ϕ·ψ⊢ϕ
     in ⊢-intr Γ,ϕ·ψ⊢
  Truth-Table-Lemma-False val (ϕ /\ ψ) (f/\f fϕ fψ) =
    let Γ⊢~ϕ      = Truth-Table-Lemma-False val ϕ fϕ
        Γ,ϕ·ψ⊢~ϕ  = weaken there Γ⊢~ϕ
        Γ,ϕ·ψ⊢ϕ   = ⊢-proj0 (⊢-ax (here refl))
        Γ,ϕ·ψ⊢    = ⊢-elim Γ,ϕ·ψ⊢~ϕ Γ,ϕ·ψ⊢ϕ
     in ⊢-intr Γ,ϕ·ψ⊢
  Truth-Table-Lemma-False val (ϕ \/ ψ) (f\/f fϕ fψ) =
    let Γ⊢~ϕ     = Truth-Table-Lemma-False val ϕ fϕ
        Γ⊢~ψ     = Truth-Table-Lemma-False val ψ fψ
        Γ,ϕ+ψ⊢~ϕ = weaken there Γ⊢~ϕ
        Γ,ϕ+ψ⊢~ψ = weaken there Γ⊢~ψ
        Γ,ϕ+ψ⊢   = ⊢-case (⊢-ax (here refl)) Γ,ϕ+ψ⊢~ϕ Γ,ϕ+ψ⊢~ψ
     in ⊢-intr Γ,ϕ+ψ⊢

  build-context : {N : Nat} (picked :  List Bool) → Context N
  build-context {N} picked = zip-map build-literal picked (enumerate N)

  -- completeness for semantically valid formula under the empty context
  complete' : {N : Nat} (ϕ : Formula N) → [] ⊨ ϕ → [] ⊢ ϕ
  complete' {N} ϕ ⊨ϕ = solve N Z rev-vars [] []
                             rev-vars-len
                             refl
                             refl
                             (+-neutral-r N)
                             (trans (++-neutral-r rev-rev-vars) (rev-inv vars))
    where
      Γ⊨ϕ : {Γ : Context N} → Γ ⊨ ϕ
      Γ⊨ϕ v _ = ⊨ϕ v []

      vars = enumerate N
      rev-vars = reverse vars
      rev-rev-vars = reverse rev-vars
      rev-vars-len = trans (rev-len vars) (enum-size N)

      Assignment→Proof : (v : Assignment N) → (Assignment→Context v) ⊢ ϕ
      Assignment→Proof v = Truth-Table-Lemma-True v ϕ (Γ⊨ϕ v [])

      solve : (n m : Nat)
            → (vars0 : List (Fin N)) -- unpicked
            → (vars1 : List (Fin N)) -- picked
            → (vals  : List Bool)    -- values for picked vars
            → (inv0 : length vars0 ≡ n)
            → (inv1 : length vars1 ≡ m)
            → (inv2 : length vals  ≡ m)
            → (inv3 : n + m ≡ N)
            → (inv4 : reverse vars0 ++ vars1 ≡ enumerate N)
            → zip-map build-literal vals vars1 ⊢ ϕ
      solve Z     m [] vars1 vals
            refl refl inv2 inv3 inv4 =
        let assignment : Assignment N
            assignment = ⟨ vals , trans inv2 inv3 ⟩
            proof = Assignment→Proof assignment
            ctx-eq : zip-map build-literal vals (enumerate N)
                   ≡ zip-map build-literal vals vars1
            ctx-eq = cong (zip-map build-literal vals) (sym inv4)
         in subst (_⊢ ϕ) proof ctx-eq
      solve (S n) m (x ∷ vars0) vars1 vals
            refl refl inv2 inv3 inv4 =
        let inv2' = cong S inv2
            inv3' = trans +-suc-shift inv3
            vars-appx-eq = ++-assoc (reverse vars0) [ x ] vars1
            inv4' = trans (sym (vars-appx-eq)) inv4
            Γ,x⁺⊢ϕ = solve n (S m) vars0 (x ∷ vars1) (True  ∷ vals) refl refl inv2' inv3' inv4'
            Γ,x⁻⊢ϕ = solve n (S m) vars0 (x ∷ vars1) (False ∷ vals) refl refl inv2' inv3' inv4'
            Γ⊢x⁺\/x⁻ = ⊢-lem (var x)
         in ⊢-case Γ⊢x⁺\/x⁻ (⊢-intr Γ,x⁺⊢ϕ) (⊢-intr Γ,x⁻⊢ϕ)

  -- every semantical entailment is derivable
  complete : {N : Nat} {Γ : Context N} {ϕ : Formula N} → Γ ⊨ ϕ → Γ ⊢ ϕ
  complete {N} {[]} {ϕ} ⊨ϕ = complete' ϕ ⊨ϕ
  complete {N} {ϕ ∷ Γ} {ψ} Γ⊨ψ =
    let Γ⊢ϕ⇒ψ   = complete {N} {Γ} {ϕ ⇒ ψ} Γ⊨ϕ⇒ψ
        Γ,ϕ⊢ϕ⇒ψ = weaken there Γ⊢ϕ⇒ψ
        Γ,ϕ⊢ϕ   = ⊢-ax (here refl)
        Γ,ϕ⊢ψ   = ⊢-elim Γ,ϕ⊢ϕ⇒ψ Γ,ϕ⊢ϕ
     in Γ,ϕ⊢ψ
    where Γ⊨ϕ⇒ψ : Γ ⊨ ϕ ⇒ ψ
          Γ⊨ϕ⇒ψ val sat with eval val ϕ 
          ... | ⟨ True  , tϕ ⟩ = let tψ = Γ⊨ψ val (tϕ ∷ sat) in t=>t tϕ tψ
          ... | ⟨ False , fϕ ⟩ with eval val ψ
          ... | ⟨ False , fψ ⟩ = f=>f fϕ fψ
          ... | ⟨ True  , tψ ⟩ = f=>t fϕ tψ


{-
-- ### Sub Section 1.2 minimal logic
-}

module ND-minimal where
  infix 3 _⊢_
  -- A sequent of classical logic natural deduction
  data _⊢_ {N : Nat} : Context N → Formula N → Set where
    -- prove true in any context
    ⊢-true : {Γ : Context N} → Γ ⊢ ⊤
    -- assumption
    ⊢-ax : {Γ : Context N} {ϕ : Formula N} → ϕ ∈ Γ → Γ ⊢ ϕ
    -- implication introduction
    ⊢-intr : {Γ : Context N} {ϕ ψ : Formula N} → ϕ ∷ Γ ⊢ ψ → Γ ⊢ ϕ ⇒ ψ
    -- implication elimination
    ⊢-elim : {Γ : Context N} {ϕ ψ : Formula N} → Γ ⊢ ϕ ⇒ ψ → Γ ⊢ ϕ → Γ ⊢ ψ
    -- conjunction introduction
    ⊢-conj : {Γ : Context N} {ϕ ψ : Formula N} → Γ ⊢ ϕ → Γ ⊢ ψ → Γ ⊢ ϕ /\ ψ
    -- conjunction elimination left/right
    ⊢-proj0 : {Γ : Context N} {ϕ ψ : Formula N} → Γ ⊢ ϕ /\ ψ → Γ ⊢ ϕ
    ⊢-proj1 : {Γ : Context N} {ϕ ψ : Formula N} → Γ ⊢ ϕ /\ ψ → Γ ⊢ ψ
    -- disjunction introduction left/right
    ⊢-inj0 : {Γ : Context N} {ϕ ψ : Formula N} → Γ ⊢ ϕ → Γ ⊢ ϕ \/ ψ
    ⊢-inj1 : {Γ : Context N} {ϕ ψ : Formula N} → Γ ⊢ ψ → Γ ⊢ ϕ \/ ψ
    -- disjunction elimination
    ⊢-case : {Γ : Context N} {γ ϕ ψ : Formula N} → Γ ⊢ ϕ \/ ψ → Γ ⊢ ϕ ⇒ γ → Γ ⊢ ψ ⇒ γ → Γ ⊢ γ

  open ND-classical using (⊢-true ; ⊢-ax ;
                           ⊢-intr ; ⊢-elim ;
                           ⊢-pbc ;
                           ⊢-conj ; ⊢-proj0 ; ⊢-proj1 ;
                           ⊢-inj0 ; ⊢-inj1 ; ⊢-case)
                    renaming (_⊢_ to _⊢c_)


  -- b
  weaken : {N : Nat} {Γ Δ : Context N} {ϕ : Formula N} → Γ ⊆ Δ → Γ ⊢ ϕ → Δ ⊢ ϕ
  weaken Γ⊆Δ ⊢-true = ⊢-true
  weaken Γ⊆Δ (⊢-ax ϕ∈Γ) = ⊢-ax (Γ⊆Δ ϕ∈Γ)
  weaken Γ⊆Δ (⊢-intr ϕ,Γ⊢ψ) = let ϕ,Γ⊆ϕ,Δ = ∷-subset Γ⊆Δ in ⊢-intr (weaken ϕ,Γ⊆ϕ,Δ ϕ,Γ⊢ψ)
  weaken Γ⊆Δ (⊢-elim Γ⊢ϕ⇒ψ Γ⊢ϕ) = let Δ⊢ϕ⇒ψ = weaken Γ⊆Δ Γ⊢ϕ⇒ψ
                                      Δ⊢ϕ   = weaken Γ⊆Δ Γ⊢ϕ
                                   in ⊢-elim Δ⊢ϕ⇒ψ Δ⊢ϕ
  weaken Γ⊆Δ (⊢-conj Γ⊢ϕ Γ⊢ψ) = let Δ⊢ϕ = weaken Γ⊆Δ Γ⊢ϕ
                                    Δ⊢ψ = weaken Γ⊆Δ Γ⊢ψ
                                 in ⊢-conj Δ⊢ϕ Δ⊢ψ
  weaken Γ⊆Δ (⊢-proj0 Γ⊢ϕ·ψ) = let Δ⊢ϕ·ψ = weaken Γ⊆Δ Γ⊢ϕ·ψ in ⊢-proj0 Δ⊢ϕ·ψ
  weaken Γ⊆Δ (⊢-proj1 Γ⊢ϕ·ψ) = let Δ⊢ϕ·ψ = weaken Γ⊆Δ Γ⊢ϕ·ψ in ⊢-proj1 Δ⊢ϕ·ψ
  weaken Γ⊆Δ (⊢-inj0 Γ⊢ϕ+ψ) = let Δ⊢ϕ+ψ = weaken Γ⊆Δ Γ⊢ϕ+ψ in ⊢-inj0 Δ⊢ϕ+ψ
  weaken Γ⊆Δ (⊢-inj1 Γ⊢ϕ+ψ) = let Δ⊢ϕ+ψ = weaken Γ⊆Δ Γ⊢ϕ+ψ in ⊢-inj1 Δ⊢ϕ+ψ
  weaken Γ⊆Δ (⊢-case Γ⊢ϕ+ψ Γ⊢ϕ⇒γ Γ⊢ψ⇒γ) = let Δ⊢ϕ+ψ = weaken Γ⊆Δ Γ⊢ϕ+ψ
                                              Δ⊢ϕ⇒γ = weaken Γ⊆Δ Γ⊢ϕ⇒γ
                                              Δ⊢ψ⇒γ = weaken Γ⊆Δ Γ⊢ψ⇒γ
                                           in ⊢-case Δ⊢ϕ+ψ Δ⊢ϕ⇒γ Δ⊢ψ⇒γ

  -- c
  implication : {N : Nat} {Γ : Context N} {ϕ : Formula N} → Γ ⊢ ϕ → Γ ⊢c ϕ
  implication ⊢-true = ⊢-true
  implication (⊢-ax x) = ⊢-ax x
  implication (⊢-intr ϕ,Γ⊢ψ) = let ϕ,Γ⊢'ψ = implication ϕ,Γ⊢ψ in ⊢-intr ϕ,Γ⊢'ψ
  implication (⊢-elim Γ⊢ϕ⇒ψ Γ⊢ϕ) = let Γ⊢'ϕ⇒ψ = implication Γ⊢ϕ⇒ψ
                                       Γ⊢'ϕ   = implication Γ⊢ϕ
                                    in ⊢-elim Γ⊢'ϕ⇒ψ Γ⊢'ϕ
  implication (⊢-conj Γ⊢ϕ Γ⊢ψ) = let Γ⊢'ϕ = implication Γ⊢ϕ
                                     Γ⊢'ψ = implication Γ⊢ψ
                                    in ⊢-conj Γ⊢'ϕ Γ⊢'ψ
  implication (⊢-proj0 Γ⊢ϕ·ψ) = let Γ⊢'ϕ·ψ = implication Γ⊢ϕ·ψ in ⊢-proj0 Γ⊢'ϕ·ψ
  implication (⊢-proj1 Γ⊢ϕ·ψ) = let Γ⊢'ϕ·ψ = implication Γ⊢ϕ·ψ in ⊢-proj1 Γ⊢'ϕ·ψ
  implication (⊢-inj0 Γ⊢ϕ+ψ) = let Γ⊢'ϕ+ψ = implication Γ⊢ϕ+ψ in ⊢-inj0 Γ⊢'ϕ+ψ
  implication (⊢-inj1 Γ⊢ϕ+ψ) = let Γ⊢'ϕ+ψ = implication Γ⊢ϕ+ψ in ⊢-inj1 Γ⊢'ϕ+ψ
  implication (⊢-case Γ⊢ϕ+ψ Γ⊢ϕ⇒γ Γ⊢ψ⇒γ) = let Γ⊢'ϕ+ψ = implication Γ⊢ϕ+ψ
                                               Γ⊢'ϕ⇒γ = implication Γ⊢ϕ⇒γ
                                               Γ⊢'ψ⇒γ = implication Γ⊢ψ⇒γ
                                            in ⊢-case Γ⊢'ϕ+ψ Γ⊢'ϕ⇒γ Γ⊢'ψ⇒γ

  -- d
  friedman[_] : {N : Nat} → Formula N → Formula N → Formula N
  friedman[ ξ ] (var x) = ((var x) ⇒ ξ) ⇒ ξ
  friedman[ ξ ] ⊤ = ⊤
  friedman[ ξ ] ⊥ = ξ
  friedman[ ξ ] (ϕ ⇒ ψ) = (friedman[ ξ ] ϕ) ⇒ (friedman[ ξ ] ψ)
  friedman[ ξ ] (ϕ /\ ψ) = (friedman[ ξ ] ϕ) /\ (friedman[ ξ ] ψ)
  friedman[ ξ ] (ϕ \/ ψ) = (((friedman[ ξ ] ϕ) \/ (friedman[ ξ ] ψ)) ⇒ ξ) ⇒ ξ

  -- e
  DNE-Friedman : {N : Nat} {Γ : Context N} {ξ : Formula N} (ϕ : Formula N)
               → Γ ⊢ friedman[ ξ ] (~ ~ ϕ ⇒ ϕ)
  DNE-Friedman (var x) = let s5 = ⊢-ax (there (here refl))
                             s4 = ⊢-elim (⊢-ax (here refl)) s5
                             s3 = ⊢-intr s4
                             s2 = ⊢-elim (⊢-ax (there (here refl))) s3
                             s1 = ⊢-intr s2
                             s0 = ⊢-intr s1
                          in s0
  DNE-Friedman ⊤ = ⊢-intr ⊢-true
  DNE-Friedman ⊥ = let ⊢~~ξ = ⊢-ax (here refl)
                       ⊢~ξ  = ⊢-intr (⊢-ax (here refl))
                       ⊢ξ   = ⊢-elim ⊢~~ξ ⊢~ξ
                    in ⊢-intr ⊢ξ
  DNE-Friedman (ϕ ⇒ ψ) = let IH = DNE-Friedman ψ
                             s8 = ⊢-ax (there (there (here refl)))
                             s7 = ⊢-elim (⊢-ax (here refl)) s8
                             s6 = ⊢-elim (⊢-ax (there (here refl))) s7
                             s5 = ⊢-intr s6
                             s4 = ⊢-elim (⊢-ax (there (there (here refl)))) s5
                             s3 = ⊢-intr s4
                             s2 = ⊢-elim IH s3
                             s1 = ⊢-intr s2
                             s0 = ⊢-intr s1
                          in s0
  DNE-Friedman (ϕ /\ ψ) = let IHϕ = DNE-Friedman ϕ
                              IHψ = DNE-Friedman ψ
                              p5 = ⊢-proj0 (⊢-ax (here refl))
                              q5 = ⊢-proj1 (⊢-ax (here refl))
                              p4 = ⊢-elim (⊢-ax (there (here refl))) p5
                              q4 = ⊢-elim (⊢-ax (there (here refl))) q5
                              p3 = ⊢-intr     p4 ; q3 = ⊢-intr     q4
                              p2 = ⊢-elim (⊢-ax (there (here refl))) p3
                              q2 = ⊢-elim (⊢-ax (there (here refl))) q3
                              p1 = ⊢-intr     p2 ; q1 = ⊢-intr     q2
                              p0 = ⊢-elim IHϕ p1 ; q0 = ⊢-elim IHψ q1
                              s1 = ⊢-conj p0 q0
                              s0 = ⊢-intr s1
                           in s0
  DNE-Friedman (ϕ \/ ψ) = let s3 = ⊢-elim (⊢-ax (here refl)) (⊢-ax (there (here refl)))
                              s2 = ⊢-intr s3
                              s1 = ⊢-elim (⊢-ax (there (here refl))) s2
                              s0 = ⊢-intr s1
                           in ⊢-intr s0

  PBC-Friedman : {N : Nat} {Γ : Context N} {ξ ϕ : Formula N}
               → friedman[ ξ ] (~ ϕ) ∷ Γ ⊢ friedman[ ξ ] ⊥ → Γ ⊢ friedman[ ξ ] ϕ
  PBC-Friedman {ϕ = ϕ} ~ϕ⊢ = let ⊢~~ϕ = ⊢-intr ~ϕ⊢
                                 dne  = DNE-Friedman ϕ
                              in ⊢-elim dne ⊢~~ϕ

  compose : {N : Nat} {Γ : Context N} {ϕ ψ γ : Formula N} → Γ ⊢ ϕ ⇒ ψ → Γ ⊢ ψ ⇒ γ → Γ ⊢ ϕ ⇒ γ
  compose ⊢ϕ⇒ψ ⊢ψ⇒γ = let ϕ⊢ψ⇒γ = weaken there ⊢ψ⇒γ
                          ϕ⊢ϕ⇒ψ = weaken there ⊢ϕ⇒ψ
                          ϕ⊢ϕ = ⊢-ax (here refl)
                          ϕ⊢ψ = ⊢-elim ϕ⊢ϕ⇒ψ ϕ⊢ϕ
                          ϕ⊢γ = ⊢-elim ϕ⊢ψ⇒γ ϕ⊢ψ
                          ⊢ϕ⇒γ = ⊢-intr ϕ⊢γ
                       in ⊢ϕ⇒γ

  -- f
  Friedman : {N : Nat} {Γ : Context N} {ϕ ξ : Formula N} → Γ ⊢c ϕ → (map friedman[ ξ ] Γ) ⊢ friedman[ ξ ] ϕ
  Friedman ⊢-true = ⊢-true
  Friedman (⊢-ax ϕ∈Γ) = ⊢-ax (∈-map ϕ∈Γ)
  Friedman (⊢-intr ⊢ϕ) = ⊢-intr (Friedman ⊢ϕ)
  Friedman (⊢-elim ⊢ϕ⇒ψ ⊢ϕ) = let ⊢'ϕ⇒ψ = Friedman ⊢ϕ⇒ψ
                                  ⊢'ϕ   = Friedman ⊢ϕ
                               in ⊢-elim ⊢'ϕ⇒ψ ⊢'ϕ
  Friedman (⊢-pbc ~ϕ⊢) = let f[~ϕ]⊢ = Friedman ~ϕ⊢ in PBC-Friedman f[~ϕ]⊢
  Friedman (⊢-conj ⊢ϕ ⊢ψ) = let ⊢'ϕ = Friedman ⊢ϕ
                                ⊢'ψ = Friedman ⊢ψ
                             in ⊢-conj ⊢'ϕ ⊢'ψ
  Friedman (⊢-proj0 ⊢ϕ·ψ) = ⊢-proj0 (Friedman ⊢ϕ·ψ)
  Friedman (⊢-proj1 ⊢ϕ·ψ) = ⊢-proj1 (Friedman ⊢ϕ·ψ)
  Friedman (⊢-inj0 ⊢ϕ) = let ⊢'ϕ = Friedman ⊢ϕ
                             ⊢'ϕ+ψ = ⊢-inj0 ⊢'ϕ
                             Δ⊢'ϕ+ψ = weaken there ⊢'ϕ+ψ
                          in ⊢-intr (⊢-elim (⊢-ax (here refl)) Δ⊢'ϕ+ψ)
  Friedman (⊢-inj1 ⊢ψ) = let ⊢'ψ = Friedman ⊢ψ
                             ⊢'ϕ+ψ = ⊢-inj1 ⊢'ψ
                             Δ⊢'ϕ+ψ = weaken there ⊢'ϕ+ψ
                          in ⊢-intr (⊢-elim (⊢-ax (here refl)) Δ⊢'ϕ+ψ)
  Friedman (⊢-case {γ = γ} ⊢ϕ+ψ ⊢ϕ⇒γ ⊢ψ⇒γ) =
    let ⊢'~~[ϕ+ψ] = Friedman ⊢ϕ+ψ
        ~γ⊢'~~[ϕ+ψ] = weaken there ⊢'~~[ϕ+ψ]
        ⊢'ϕ⇒γ = Friedman ⊢ϕ⇒γ
        ⊢'ψ⇒γ = Friedman ⊢ψ⇒γ
        ~γ,ϕ+ψ⊢'ϕ⇒γ = weaken (λ x → there (there x)) ⊢'ϕ⇒γ
        ~γ,ϕ+ψ⊢'ψ⇒γ = weaken (λ x → there (there x)) ⊢'ψ⇒γ
        ~γ,ϕ+ψ⊢~γ = ⊢-ax (there (here refl))
        ~γ,ϕ+ψ⊢~ϕ = compose ~γ,ϕ+ψ⊢'ϕ⇒γ ~γ,ϕ+ψ⊢~γ
        ~γ,ϕ+ψ⊢~ψ = compose ~γ,ϕ+ψ⊢'ψ⇒γ ~γ,ϕ+ψ⊢~γ
        ~γ,ϕ+ψ⊢⊥ = ⊢-case (⊢-ax (here refl)) ~γ,ϕ+ψ⊢~ϕ ~γ,ϕ+ψ⊢~ψ
        ~γ⊢~[ϕ+ψ] = ⊢-intr ~γ,ϕ+ψ⊢⊥
        ~γ⊢'⊥ = ⊢-elim ~γ⊢'~~[ϕ+ψ] ~γ⊢~[ϕ+ψ]
        ⊢'~~γ = ⊢-intr ~γ⊢'⊥
        dne-γ = DNE-Friedman γ
     in ⊢-elim dne-γ ⊢'~~γ

  GroundTranslationGround : {N : Nat} {ϕ : Formula N} (gϕ : Ground ϕ) → Ground (friedman[ ⊥ ] ϕ)
  GroundTranslationGround ⊤ = ⊤
  GroundTranslationGround ⊥ = ⊥
  GroundTranslationGround (ϕ ⇒ ψ) = let gϕ = GroundTranslationGround ϕ
                                        gψ = GroundTranslationGround ψ
                                     in gϕ ⇒ gψ
  GroundTranslationGround (ϕ /\ ψ) = let gϕ = GroundTranslationGround ϕ
                                         gψ = GroundTranslationGround ψ
                                      in gϕ /\ gψ
  GroundTranslationGround (ϕ \/ ψ) = let gϕ = GroundTranslationGround ϕ
                                         gψ = GroundTranslationGround ψ
                                      in ((gϕ \/ gψ) ⇒ ⊥) ⇒ ⊥


  MinimalFalse  : {N : Nat} {ϕ : Formula N} (gϕ : Ground ϕ) → GValue gϕ False → [] ⊢ ϕ ⇒ ⊥
  MinimalFalse' : {N : Nat} {ϕ : Formula N} (gϕ : Ground ϕ) → GValue gϕ False → [] ⊢ ⊥ ⇒ ϕ
  MinimalTrue   : {N : Nat} {ϕ : Formula N} (gϕ : Ground ϕ) → GValue gϕ True → [] ⊢ ϕ

  MinimalFalse ⊥ v = ⊢-intr (⊢-ax (here refl))
  MinimalFalse (ϕ ⇒  ψ) (t=>f tϕ fψ) =
    let ϕ   = weaken (λ ()) (MinimalTrue ϕ tϕ)
        ψ⇒⊥ = weaken (λ ()) (MinimalFalse ψ fψ)
        ϕ⇒ψ = ⊢-ax (here refl)
     in ⊢-intr (⊢-elim ψ⇒⊥ (⊢-elim ϕ⇒ψ ϕ))
  MinimalFalse (ϕ /\ ψ) (t/\f tϕ fψ) = let ψ⇒⊥ = weaken (λ ()) (MinimalFalse ψ fψ)
                                           ψ   = ⊢-proj1 (⊢-ax (here refl))
                                        in ⊢-intr (⊢-elim ψ⇒⊥ ψ)
  MinimalFalse (ϕ /\ ψ) (f/\t fϕ tψ) = let ϕ⇒⊥ = weaken (λ ()) (MinimalFalse ϕ fϕ)
                                           ϕ   = ⊢-proj0 (⊢-ax (here refl))
                                        in ⊢-intr (⊢-elim ϕ⇒⊥ ϕ)
  MinimalFalse (ϕ /\ ψ) (f/\f fϕ fψ) = let ϕ⇒⊥ = weaken (λ ()) (MinimalFalse ϕ fϕ)
                                           ϕ   = ⊢-proj0 (⊢-ax (here refl))
                                        in ⊢-intr (⊢-elim ϕ⇒⊥ ϕ)
  MinimalFalse (ϕ \/ ψ) (f\/f fϕ fψ) = let ϕ⇒⊥ = weaken (λ ()) (MinimalFalse ϕ fϕ)
                                           ψ⇒⊥ = weaken (λ ()) (MinimalFalse ψ fψ)
                                        in ⊢-intr (⊢-case (⊢-ax (here refl)) ϕ⇒⊥ ψ⇒⊥)

  MinimalFalse' ⊥ v = ⊢-intr (⊢-ax (here refl))
  MinimalFalse' (ϕ ⇒  ψ) (t=>f tϕ fψ) = let ⊥⇒ψ = weaken (λ ()) (MinimalFalse' ψ fψ)
                                            ⊥   = ⊢-ax (there (here refl))
                                         in ⊢-intr (⊢-intr (⊢-elim ⊥⇒ψ ⊥))
  MinimalFalse' (ϕ /\ ψ) (t/\f tϕ fψ) = let ϕ   = weaken (λ ()) (MinimalTrue ϕ tϕ)
                                            ⊥⇒ψ = weaken (λ ()) (MinimalFalse' ψ fψ)
                                            ⊥   = ⊢-ax (here refl)
                                         in ⊢-intr (⊢-conj ϕ (⊢-elim ⊥⇒ψ ⊥))
  MinimalFalse' (ϕ /\ ψ) (f/\t fϕ tψ) = let ψ   = weaken (λ ()) (MinimalTrue ψ tψ)
                                            ⊥⇒ϕ = weaken (λ ()) (MinimalFalse' ϕ fϕ)
                                            ⊥   = ⊢-ax (here refl)
                                         in ⊢-intr (⊢-conj (⊢-elim ⊥⇒ϕ ⊥) ψ)
  MinimalFalse' (ϕ /\ ψ) (f/\f fϕ fψ) = let ⊥⇒ϕ = weaken (λ ()) (MinimalFalse' ϕ fϕ)
                                            ⊥⇒ψ = weaken (λ ()) (MinimalFalse' ψ fψ)
                                            ⊥   = ⊢-ax (here refl)
                                            ϕ   = ⊢-elim ⊥⇒ϕ ⊥
                                            ψ   = ⊢-elim ⊥⇒ψ ⊥
                                         in ⊢-intr (⊢-conj ϕ ψ)
  MinimalFalse' (ϕ \/ ψ) (f\/f fϕ fψ) = let ⊥⇒ϕ = weaken (λ ()) (MinimalFalse' ϕ fϕ)
                                            ⊥   = ⊢-ax (here refl)
                                         in ⊢-intr (⊢-inj0 (⊢-elim ⊥⇒ϕ ⊥))

  MinimalTrue ⊤ t⊤ = ⊢-true
  MinimalTrue (ϕ ⇒ ψ) (t=>t tϕ tψ) = ⊢-intr (weaken (λ ()) (MinimalTrue ψ tψ))
  MinimalTrue (ϕ ⇒ ψ) (f=>t fϕ tψ) = ⊢-intr (weaken (λ ()) (MinimalTrue ψ tψ))
  MinimalTrue (ϕ ⇒ ψ) (f=>f fϕ fψ) = let ϕ⇒⊥ = MinimalFalse ϕ fϕ
                                         ⊥⇒ψ = MinimalFalse' ψ fψ
                                      in compose ϕ⇒⊥ ⊥⇒ψ
  MinimalTrue (ϕ /\ ψ) (t/\t tϕ tψ) = ⊢-conj (MinimalTrue ϕ tϕ) (MinimalTrue ψ tψ)
  MinimalTrue (ϕ \/ ψ) (t\/t tϕ tψ) = ⊢-inj0 (MinimalTrue ϕ tϕ)
  MinimalTrue (ϕ \/ ψ) (t\/f tϕ fψ) = ⊢-inj0 (MinimalTrue ϕ tϕ)
  MinimalTrue (ϕ \/ ψ) (f\/t fϕ tψ) = ⊢-inj1 (MinimalTrue ψ tψ)

  -- g
  GroundTruth : {N : Nat} {ϕ : Formula N} → Ground ϕ → ([] ⊢ ϕ) ⇔ ([] ⊢c ϕ)
  GroundTruth {N} ϕ = record { ⇒ = implication ; ⇐ = lemma ϕ }
    where
      lemma : {ϕ : Formula N} → Ground ϕ → [] ⊢c ϕ → [] ⊢ ϕ
      lemma {ϕ} gϕ ⊢cϕ with GValueDec gϕ
      ... | left  tϕ = MinimalTrue gϕ tϕ
      ... | right fϕ = let ⊢ϕ⇒⊥  = MinimalFalse gϕ fϕ
                           ⊢cϕ⇒⊥ = implication ⊢ϕ⇒⊥
                           ⊢c⊥   = ⊢-elim ⊢cϕ⇒⊥ ⊢cϕ
                           ⊢ϕ    = Friedman {ξ = ϕ} ⊢c⊥
                        in ⊢ϕ

  -- h
  Equi-Consitency : {N : Nat} → ([] ⊢ ⊥ {N}) ⇔ ([] ⊢c ⊥)
  Equi-Consitency = GroundTruth ⊥
