{-
-- ## Section 1
-- natural deduction for classical and minimal propositional logic
-}

open import common

{-
-- ### Sub Section 1.1 classical logic
-}

infixr 30 _⇒_
data Formula : Set where
  var : ℕ → Formula
  ⊥ : Formula
  _⇒_ : Formula → Formula → Formula

-- 1.1.d
Ground : Formula → Set
Ground (var x) = Empty
Ground ⊥ = Unit
Ground (ϕ ⇒ ψ) = Ground ϕ × Ground ψ

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
    -- assumption
    ⊢-ax : {Γ : Context} {ϕ : Formula} → ϕ ∈ Γ → Γ ⊢ ϕ
    -- implication introduction
    ⊢-intr : {Γ : Context} {ϕ ψ : Formula} → ϕ ∷ Γ ⊢ ψ → Γ ⊢ ϕ ⇒ ψ
    -- implication elimination
    ⊢-elim : {Γ : Context} {ϕ ψ : Formula} → Γ ⊢ ϕ ⇒ ψ → Γ ⊢ ϕ → Γ ⊢ ψ
    -- proof by contradiction
    ⊢-pbc : {Γ : Context} {ϕ : Formula} → ~ ϕ ∷ Γ ⊢ ⊥ → Γ ⊢ ϕ

  -- b.1
  example-1 : {Γ : Context} (ϕ : Formula) → Γ ⊢ ϕ ⇒ ϕ
  example-1 ϕ = ⊢-intr (⊢-ax (here refl))

  -- b.2
  example-2 : {Γ : Context} {ϕ : Formula} → ϕ ∷ Γ ⊢ ~ ~ ϕ
  example-2 = ⊢-intr let ⊢ϕ⇒⊥ = ⊢-ax (here refl)
                         ⊢ϕ     = ⊢-ax (there (here refl))
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
  weaken Γ⊆Δ (⊢-ax ϕ∈Γ) = ⊢-ax (Γ⊆Δ ϕ∈Γ)
  weaken Γ⊆Δ (⊢-intr ϕ,Γ⊢ψ) = let ϕ,Γ⊆ϕ,Δ = ∷-subset Γ⊆Δ in ⊢-intr (weaken ϕ,Γ⊆ϕ,Δ ϕ,Γ⊢ψ)
  weaken Γ⊆Δ (⊢-elim Γ⊢ϕ⇒ψ Γ⊢ϕ) = let Δ⊢ϕ⇒ψ = weaken Γ⊆Δ Γ⊢ϕ⇒ψ
                                      Δ⊢ϕ   = weaken Γ⊆Δ Γ⊢ϕ
                                   in ⊢-elim Δ⊢ϕ⇒ψ Δ⊢ϕ
  weaken Γ⊆Δ (⊢-pbc ~ϕ,Γ⊢⊥) = let ~ϕ,Γ⊆~ϕ,Δ = ∷-subset Γ⊆Δ
                                  ~ϕ,Δ⊢⊥    = weaken ~ϕ,Γ⊆~ϕ,Δ ~ϕ,Γ⊢⊥
                               in ⊢-pbc ~ϕ,Δ⊢⊥


{-
-- ### Sub Section 1.2 minimal logic
-}

module ND-minimal where
  infix 3 _⊢_
  -- A sequent of classical logic natural deduction
  data _⊢_ : Context → Formula → Set where
    -- assumption
    ⊢-ax : {Γ : Context} {ϕ : Formula} → ϕ ∈ Γ → Γ ⊢ ϕ
    -- implication introduction
    ⊢-intr : {Γ : Context} {ϕ ψ : Formula} → ϕ ∷ Γ ⊢ ψ → Γ ⊢ ϕ ⇒ ψ
    -- implication elimination
    ⊢-elim : {Γ : Context} {ϕ ψ : Formula} → Γ ⊢ ϕ ⇒ ψ → Γ ⊢ ϕ → Γ ⊢ ψ

  open ND-classical using (⊢-ax ; ⊢-intr ; ⊢-elim ; ⊢-pbc) renaming (_⊢_ to _⊢c_)

  -- b
  weaken : {Γ Δ : Context} {ϕ : Formula} → Γ ⊆ Δ → Γ ⊢ ϕ → Δ ⊢ ϕ
  weaken Γ⊆Δ (⊢-ax ϕ∈Γ) = ⊢-ax (Γ⊆Δ ϕ∈Γ)
  weaken Γ⊆Δ (⊢-intr ϕ,Γ⊢ψ) = let ϕ,Γ⊆ϕ,Δ = ∷-subset Γ⊆Δ in ⊢-intr (weaken ϕ,Γ⊆ϕ,Δ ϕ,Γ⊢ψ)
  weaken Γ⊆Δ (⊢-elim Γ⊢ϕ⇒ψ Γ⊢ϕ) = let Δ⊢ϕ⇒ψ = weaken Γ⊆Δ Γ⊢ϕ⇒ψ
                                      Δ⊢ϕ   = weaken Γ⊆Δ Γ⊢ϕ
                                   in ⊢-elim Δ⊢ϕ⇒ψ Δ⊢ϕ

  -- c
  implication : {Γ : Context} {ϕ : Formula} → Γ ⊢ ϕ → Γ ⊢c ϕ
  implication (⊢-ax x) = ⊢-ax x
  implication (⊢-intr ϕ,Γ⊢ψ) = let ϕ,Γ⊢'ψ = implication ϕ,Γ⊢ψ in ⊢-intr ϕ,Γ⊢'ψ
  implication (⊢-elim Γ⊢ϕ⇒ψ Γ⊢ϕ) = let Γ⊢'ϕ⇒ψ = implication Γ⊢ϕ⇒ψ
                                       Γ⊢'ϕ   = implication Γ⊢ϕ
                                    in (⊢-elim Γ⊢'ϕ⇒ψ Γ⊢'ϕ)

  -- d
  friedman[_] : Formula → Formula → Formula
  friedman[ ξ ] (var x) = ((var x) ⇒ ξ) ⇒ ξ
  friedman[ ξ ] ⊥ = ξ
  friedman[ ξ ] (ϕ ⇒ ψ) = (friedman[ ξ ] ϕ) ⇒ (friedman[ ξ ] ψ)

  -- e
  DNE-Friedman : {Γ : Context} {ξ : Formula} (ϕ : Formula) → Γ ⊢ friedman[ ξ ] (~ ~ ϕ ⇒ ϕ)
  DNE-Friedman (var x) = let s5 = ⊢-ax (there (here refl))
                             s4 = ⊢-elim (⊢-ax (here refl)) s5
                             s3 = ⊢-intr s4
                             s2 = ⊢-elim (⊢-ax (there (here refl))) s3
                             s1 = ⊢-intr s2
                             s0 = ⊢-intr s1
                          in s0
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

  PBC-Friedman : {Γ : Context} {ξ ϕ : Formula} → friedman[ ξ ] (~ ϕ) ∷ Γ ⊢ friedman[ ξ ] ⊥ → Γ ⊢ friedman[ ξ ] ϕ
  PBC-Friedman {ϕ = ϕ} ~ϕ⊢ = let ⊢~~ϕ = ⊢-intr ~ϕ⊢
                                 dne  = DNE-Friedman ϕ
                              in ⊢-elim dne ⊢~~ϕ

  -- f
  Friedman : {Γ : Context} {ϕ ξ : Formula} → Γ ⊢c ϕ → (map friedman[ ξ ] Γ) ⊢ friedman[ ξ ] ϕ
  Friedman (⊢-ax ϕ∈Γ) = ⊢-ax (∈-map ϕ∈Γ)
  Friedman (⊢-intr ⊢ϕ) = ⊢-intr (Friedman ⊢ϕ)
  Friedman (⊢-elim ⊢ϕ⇒ψ ⊢ϕ) = let ⊢'ϕ⇒ψ = Friedman ⊢ϕ⇒ψ
                                  ⊢'ϕ   = Friedman ⊢ϕ
                               in ⊢-elim ⊢'ϕ⇒ψ ⊢'ϕ
  Friedman (⊢-pbc ~ϕ⊢) = let f[~ϕ]⊢ = Friedman ~ϕ⊢ in PBC-Friedman f[~ϕ]⊢

  friedman-of-ground : (ϕ : Formula) → Ground ϕ → friedman[ ⊥ ] ϕ ≡ ϕ
  friedman-of-ground ⊥ Gϕ = refl
  friedman-of-ground (ϕ ⇒ ψ) ⟨ Gϕ , Gψ ⟩ = let ϕ' = friedman-of-ground ϕ Gϕ
                                               ψ' = friedman-of-ground ψ Gψ
                                            in cong2 _⇒_  ϕ' ψ'

  -- g
  GroundTruth : (ϕ : Formula) → Ground ϕ → ([] ⊢ ϕ) ⇔ ([] ⊢c ϕ)
  GroundTruth ϕ ϕᵍ = record { ⇒ = implication ; ⇐ = converse ϕ ϕᵍ }
    where
      converse : (ϕ : Formula) → Ground ϕ → [] ⊢c ϕ → [] ⊢ ϕ
      converse ϕ ϕᵍ ⊢'ϕ = let ⊢f[⊥]ϕ  = Friedman {ξ = ⊥} ⊢'ϕ
                           in subst ([] ⊢_) ⊢f[⊥]ϕ (friedman-of-ground ϕ ϕᵍ)

  -- h
  Equi-Consitency : ([] ⊢ ⊥) ⇔ ([] ⊢c ⊥)
  Equi-Consitency = GroundTruth ⊥ unit

