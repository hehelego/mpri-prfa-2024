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
data Formula : Set where
  var : ℕ → Formula
  ⊤ : Formula
  ⊥ : Formula
  _⇒_ : Formula → Formula → Formula
  _/\_ : Formula → Formula → Formula
  _\/_ : Formula → Formula → Formula

-- 1.1.d
data Ground : Formula → Set where
  ⊤ : Ground ⊤
  ⊥ : Ground ⊥
  _⇒_ : {ϕ ψ : Formula} → Ground ϕ → Ground ψ → Ground (ϕ ⇒ ψ)
  _/\_ :{ϕ ψ : Formula} → Ground ϕ → Ground ψ → Ground (ϕ /\ ψ)
  _\/_ : {ϕ ψ : Formula} → Ground ϕ → Ground ψ → Ground (ϕ \/ ψ)

data GValue : {ϕ : Formula} (gϕ : Ground ϕ) (b : Bool) → Set where
  t⊤ : GValue ⊤ True
  f⊥ : GValue ⊥ False
  t/\t : {ϕ : Formula} {gϕ : Ground ϕ} {ψ : Formula} {gψ : Ground ψ}
       → GValue gϕ True → GValue gψ True → GValue (gϕ /\ gψ) True
  t/\f : {ϕ : Formula} {gϕ : Ground ϕ} {ψ : Formula} {gψ : Ground ψ}
       → GValue gϕ True → GValue gψ False → GValue (gϕ /\ gψ) False
  f/\t : {ϕ : Formula} {gϕ : Ground ϕ} {ψ : Formula} {gψ : Ground ψ}
       → GValue gϕ False → GValue gψ True → GValue (gϕ /\ gψ) False
  f/\f : {ϕ : Formula} {gϕ : Ground ϕ} {ψ : Formula} {gψ : Ground ψ}
       → GValue gϕ False → GValue gψ False → GValue (gϕ /\ gψ) False
  t\/t : {ϕ : Formula} {gϕ : Ground ϕ} {ψ : Formula} {gψ : Ground ψ}
       → GValue gϕ True → GValue gψ True → GValue (gϕ \/ gψ) True
  t\/f : {ϕ : Formula} {gϕ : Ground ϕ} {ψ : Formula} {gψ : Ground ψ}
       → GValue gϕ True → GValue gψ False → GValue (gϕ \/ gψ) True
  f\/t : {ϕ : Formula} {gϕ : Ground ϕ} {ψ : Formula} {gψ : Ground ψ}
       → GValue gϕ False → GValue gψ True → GValue (gϕ \/ gψ) True
  f\/f : {ϕ : Formula} {gϕ : Ground ϕ} {ψ : Formula} {gψ : Ground ψ}
       → GValue gϕ False → GValue gψ False → GValue (gϕ \/ gψ) False
  t=>t : {ϕ : Formula} {gϕ : Ground ϕ} {ψ : Formula} {gψ : Ground ψ}
       → GValue gϕ True → GValue gψ True → GValue (gϕ ⇒ gψ) True
  t=>f : {ϕ : Formula} {gϕ : Ground ϕ} {ψ : Formula} {gψ : Ground ψ}
       → GValue gϕ True → GValue gψ False → GValue (gϕ ⇒ gψ) False
  f=>t : {ϕ : Formula} {gϕ : Ground ϕ} {ψ : Formula} {gψ : Ground ψ}
       → GValue gϕ False → GValue gψ True → GValue (gϕ ⇒ gψ) True
  f=>f : {ϕ : Formula} {gϕ : Ground ϕ} {ψ : Formula} {gψ : Ground ψ}
       → GValue gϕ False → GValue gψ False → GValue (gϕ ⇒ gψ) True

GValueDec : {ϕ : Formula} (gϕ : Ground ϕ) → (GValue gϕ True) ⊎ (GValue gϕ False)
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

infixr 50 ~_
~_ : Formula → Formula
~_ = _⇒ ⊥

-- in agda-stdlib (_∷_) has precedence 5
Context : Set
Context = List Formula

module ND-classical where
  infix 3 _⊢_
  -- A sequent of classical logic natural deduction
  data _⊢_ : Context → Formula → Set where
    -- prove true in any context
    ⊢-true : {Γ : Context} → Γ ⊢ ⊤
    -- assumption
    ⊢-ax : {Γ : Context} {ϕ : Formula} → ϕ ∈ Γ → Γ ⊢ ϕ
    -- implication introduction
    ⊢-intr : {Γ : Context} {ϕ ψ : Formula} → ϕ ∷ Γ ⊢ ψ → Γ ⊢ ϕ ⇒ ψ
    -- implication elimination
    ⊢-elim : {Γ : Context} {ϕ ψ : Formula} → Γ ⊢ ϕ ⇒ ψ → Γ ⊢ ϕ → Γ ⊢ ψ
    -- proof by contradiction
    ⊢-pbc : {Γ : Context} {ϕ : Formula} → ~ ϕ ∷ Γ ⊢ ⊥ → Γ ⊢ ϕ
    -- conjunction introduction
    ⊢-conj : {Γ : Context} {ϕ ψ : Formula} → Γ ⊢ ϕ → Γ ⊢ ψ → Γ ⊢ ϕ /\ ψ
    -- conjunction elimination left/right
    ⊢-proj0 : {Γ : Context} {ϕ ψ : Formula} → Γ ⊢ ϕ /\ ψ → Γ ⊢ ϕ
    ⊢-proj1 : {Γ : Context} {ϕ ψ : Formula} → Γ ⊢ ϕ /\ ψ → Γ ⊢ ψ
    -- disjunction introduction left/right
    ⊢-inj0 : {Γ : Context} {ϕ ψ : Formula} → Γ ⊢ ϕ → Γ ⊢ ϕ \/ ψ
    ⊢-inj1 : {Γ : Context} {ϕ ψ : Formula} → Γ ⊢ ψ → Γ ⊢ ϕ \/ ψ
    -- disjunction elimination
    ⊢-case : {Γ : Context} {γ ϕ ψ : Formula} → Γ ⊢ ϕ \/ ψ → Γ ⊢ ϕ ⇒ γ → Γ ⊢ ψ ⇒ γ → Γ ⊢ γ


  -- b.1
  example-1 : {Γ : Context} (ϕ : Formula) → Γ ⊢ ϕ ⇒ ϕ
  example-1 ϕ = ⊢-intr (⊢-ax (here refl))

  -- b.2
  example-2 : {Γ : Context} {ϕ : Formula} → ϕ ∷ Γ ⊢ ~ ~ ϕ
  example-2 = ⊢-intr let ⊢ϕ⇒⊥ = ⊢-ax (here refl)
                         ⊢ϕ   = ⊢-ax (there (here refl))
                      in ⊢-elim ⊢ϕ⇒⊥ ⊢ϕ

  -- b.3
  example-3 : ~ ~ ⊥ ∷ [] ⊢ ⊥
  example-3 = let ⊢⊥⇒⊥       = ⊢-intr (⊢-ax (here refl))
                  ⊢~⊥⇒⊥ = ⊢-ax (here refl)
               in ⊢-elim ⊢~⊥⇒⊥ ⊢⊥⇒⊥

  -- b.4
  -- double-negation-elimination is non-intuitionistic, need PBC
  example-4 : {Γ : Context} {ϕ : Formula} → Γ ⊢ ~ ~ ϕ ⇒ ϕ
  example-4 = let ⊢~ϕ  = ⊢-ax (here refl)
                  ⊢~~ϕ = ⊢-ax (there (here refl))
                  ⊢⊥ = ⊢-elim ⊢~~ϕ ⊢~ϕ
               in ⊢-intr (⊢-pbc ⊢⊥)

  -- c
  weaken : {Γ Δ : Context} {ϕ : Formula} → Γ ⊆ Δ → Γ ⊢ ϕ → Δ ⊢ ϕ
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

{-
-- ### Sub Section 1.2 minimal logic
-}

module ND-minimal where
  infix 3 _⊢_
  -- A sequent of classical logic natural deduction
  data _⊢_ : Context → Formula → Set where
    -- prove true in any context
    ⊢-true : {Γ : Context} → Γ ⊢ ⊤
    -- assumption
    ⊢-ax : {Γ : Context} {ϕ : Formula} → ϕ ∈ Γ → Γ ⊢ ϕ
    -- implication introduction
    ⊢-intr : {Γ : Context} {ϕ ψ : Formula} → ϕ ∷ Γ ⊢ ψ → Γ ⊢ ϕ ⇒ ψ
    -- implication elimination
    ⊢-elim : {Γ : Context} {ϕ ψ : Formula} → Γ ⊢ ϕ ⇒ ψ → Γ ⊢ ϕ → Γ ⊢ ψ
    -- conjunction introduction
    ⊢-conj : {Γ : Context} {ϕ ψ : Formula} → Γ ⊢ ϕ → Γ ⊢ ψ → Γ ⊢ ϕ /\ ψ
    -- conjunction elimination left/right
    ⊢-proj0 : {Γ : Context} {ϕ ψ : Formula} → Γ ⊢ ϕ /\ ψ → Γ ⊢ ϕ
    ⊢-proj1 : {Γ : Context} {ϕ ψ : Formula} → Γ ⊢ ϕ /\ ψ → Γ ⊢ ψ
    -- disjunction introduction left/right
    ⊢-inj0 : {Γ : Context} {ϕ ψ : Formula} → Γ ⊢ ϕ → Γ ⊢ ϕ \/ ψ
    ⊢-inj1 : {Γ : Context} {ϕ ψ : Formula} → Γ ⊢ ψ → Γ ⊢ ϕ \/ ψ
    -- disjunction elimination
    ⊢-case : {Γ : Context} {γ ϕ ψ : Formula} → Γ ⊢ ϕ \/ ψ → Γ ⊢ ϕ ⇒ γ → Γ ⊢ ψ ⇒ γ → Γ ⊢ γ

  open ND-classical using (⊢-true ; ⊢-ax ;
                           ⊢-intr ; ⊢-elim ;
                           ⊢-pbc ;
                           ⊢-conj ; ⊢-proj0 ; ⊢-proj1 ;
                           ⊢-inj0 ; ⊢-inj1 ; ⊢-case)
                    renaming (_⊢_ to _⊢c_)


  -- b
  weaken : {Γ Δ : Context} {ϕ : Formula} → Γ ⊆ Δ → Γ ⊢ ϕ → Δ ⊢ ϕ
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
  implication : {Γ : Context} {ϕ : Formula} → Γ ⊢ ϕ → Γ ⊢c ϕ
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
  friedman[_] : Formula → Formula → Formula
  friedman[ ξ ] (var x) = ((var x) ⇒ ξ) ⇒ ξ
  friedman[ ξ ] ⊤ = ⊤
  friedman[ ξ ] ⊥ = ξ
  friedman[ ξ ] (ϕ ⇒ ψ) = (friedman[ ξ ] ϕ) ⇒ (friedman[ ξ ] ψ)
  friedman[ ξ ] (ϕ /\ ψ) = (friedman[ ξ ] ϕ) /\ (friedman[ ξ ] ψ)
  friedman[ ξ ] (ϕ \/ ψ) = (((friedman[ ξ ] ϕ) \/ (friedman[ ξ ] ψ)) ⇒ ξ) ⇒ ξ

  -- e
  DNE-Friedman : {Γ : Context} {ξ : Formula} (ϕ : Formula) → Γ ⊢ friedman[ ξ ] (~ ~ ϕ ⇒ ϕ)
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

  PBC-Friedman : {Γ : Context} {ξ ϕ : Formula} → friedman[ ξ ] (~ ϕ) ∷ Γ ⊢ friedman[ ξ ] ⊥ → Γ ⊢ friedman[ ξ ] ϕ
  PBC-Friedman {ϕ = ϕ} ~ϕ⊢ = let ⊢~~ϕ = ⊢-intr ~ϕ⊢
                                 dne  = DNE-Friedman ϕ
                              in ⊢-elim dne ⊢~~ϕ

  compose : {Γ : Context} {ϕ ψ γ : Formula} → Γ ⊢ ϕ ⇒ ψ → Γ ⊢ ψ ⇒ γ → Γ ⊢ ϕ ⇒ γ
  compose ⊢ϕ⇒ψ ⊢ψ⇒γ = let ϕ⊢ψ⇒γ = weaken there ⊢ψ⇒γ
                          ϕ⊢ϕ⇒ψ = weaken there ⊢ϕ⇒ψ
                          ϕ⊢ϕ = ⊢-ax (here refl)
                          ϕ⊢ψ = ⊢-elim ϕ⊢ϕ⇒ψ ϕ⊢ϕ
                          ϕ⊢γ = ⊢-elim ϕ⊢ψ⇒γ ϕ⊢ψ
                          ⊢ϕ⇒γ = ⊢-intr ϕ⊢γ
                       in ⊢ϕ⇒γ

  -- f
  Friedman : {Γ : Context} {ϕ ξ : Formula} → Γ ⊢c ϕ → (map friedman[ ξ ] Γ) ⊢ friedman[ ξ ] ϕ
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

  GroundTranslationGround : {ϕ : Formula} (gϕ : Ground ϕ) → Ground (friedman[ ⊥ ] ϕ)
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


  MinimalFalse : {ϕ : Formula} (gϕ : Ground ϕ) → GValue gϕ False → [] ⊢ ϕ ⇒ ⊥
  MinimalFalse' : {ϕ : Formula} (gϕ : Ground ϕ) → GValue gϕ False → [] ⊢ ⊥ ⇒ ϕ
  MinimalTrue : {ϕ : Formula} (gϕ : Ground ϕ) → GValue gϕ True → [] ⊢ ϕ

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
  GroundTruth : {ϕ : Formula} → Ground ϕ → ([] ⊢ ϕ) ⇔ ([] ⊢c ϕ)
  GroundTruth ϕ = record { ⇒ = implication ; ⇐ = lemma ϕ }
    where
      lemma : {ϕ : Formula} → Ground ϕ → [] ⊢c ϕ → [] ⊢ ϕ
      lemma {ϕ} gϕ ⊢cϕ with GValueDec gϕ
      ... | left  tϕ = MinimalTrue gϕ tϕ
      ... | right fϕ = let ⊢ϕ⇒⊥  = MinimalFalse gϕ fϕ
                           ⊢cϕ⇒⊥ = implication ⊢ϕ⇒⊥
                           ⊢c⊥   = ⊢-elim ⊢cϕ⇒⊥ ⊢cϕ
                           ⊢ϕ    = Friedman {ξ = ϕ} ⊢c⊥
                        in ⊢ϕ

  -- h
  Equi-Consitency : ([] ⊢ ⊥) ⇔ ([] ⊢c ⊥)
  Equi-Consitency = GroundTruth ⊥
  
