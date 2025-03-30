{-
-- ## Section 2
-- Hilbert systems and combinatory logic
-}

open import common
open import ex1
open ex1.ND-minimal using (⊢-true ; ⊢-ax ; ⊢-intr ; ⊢-elim ; ⊢-conj ; ⊢-proj0 ; ⊢-proj1) renaming (_⊢_ to _⊢m_)
open ex1.ND-classical using (⊢-true ; ⊢-ax ; ⊢-intr ; ⊢-elim ; ⊢-conj ; ⊢-proj0 ; ⊢-proj1) renaming (_⊢_ to _⊢c_)

_ : ℕ
_ = Z

{-
-- ### Sub Section 2.1 Hilbert systems
-}
module Hilbert-System where
  infix 3 _⊢_
  -- Hilbert System Derivability
  -- The context never changes so we make it a parameter not an index.
  data _⊢_ (Γ : Context) : Formula → Set where
    -- prove true in any context
    ⊢-TRUE : Γ ⊢ ⊤
    -- using assumption: the identity axiom
    ⊢-AX : {ϕ : Formula} → ϕ ∈ Γ → Γ ⊢ ϕ
    -- modus ponens
    ⊢-MP : {ϕ ψ : Formula} → Γ ⊢ ϕ ⇒ ψ → Γ ⊢ ϕ → Γ ⊢ ψ
    -- the K combinator
    ⊢-K : {ϕ ψ : Formula} → Γ ⊢ ϕ ⇒ ψ ⇒ ϕ
    -- the S combinator
    ⊢-S : {ϕ ψ γ : Formula} → Γ ⊢ (ϕ ⇒ ψ ⇒ γ) ⇒ (ϕ ⇒ ψ) ⇒ ϕ ⇒ γ
    -- conjunction introduction
    ⊢-CONJ : {ϕ ψ : Formula} → Γ ⊢ ϕ ⇒ ψ ⇒ ϕ /\ ψ
    -- conjunction elimination left/right
    ⊢-PROJ0 : {ϕ ψ : Formula} → Γ ⊢ ϕ /\ ψ ⇒ ϕ
    ⊢-PROJ1 : {ϕ ψ : Formula} → Γ ⊢ ϕ /\ ψ ⇒ ψ



  -- b
  Hilbert⇒Minimal : {Γ : Context} {ϕ : Formula} → Γ ⊢ ϕ → Γ ⊢m ϕ
  Hilbert⇒Minimal ⊢-TRUE = ⊢-true
  Hilbert⇒Minimal (⊢-AX x) = ⊢-ax x
  Hilbert⇒Minimal (⊢-MP ϕ⇒ψ ϕ) = let ⊢ϕ⇒ψ = Hilbert⇒Minimal ϕ⇒ψ
                                     ⊢ϕ   = Hilbert⇒Minimal ϕ
                                  in ⊢-elim ⊢ϕ⇒ψ ⊢ϕ
  Hilbert⇒Minimal ⊢-K = let at = ⊢-ax (there (here refl))
                         in ⊢-intr (⊢-intr at)
  Hilbert⇒Minimal ⊢-S = let ϕ     = ⊢-ax               (here refl)
                            ϕ⇒ψ   = ⊢-ax (there        (here refl))
                            ϕ⇒ψ⇒γ = ⊢-ax (there (there (here refl)))
                            ψ     = ⊢-elim ϕ⇒ψ   ϕ
                            ψ⇒γ   = ⊢-elim ϕ⇒ψ⇒γ ϕ
                            γ     = ⊢-elim ψ⇒γ   ψ
                         in ⊢-intr (⊢-intr (⊢-intr γ))
  Hilbert⇒Minimal ⊢-CONJ = let ψϕ⊢ϕ = ⊢-ax (there (here refl))
                               ψϕ⊢ψ = ⊢-ax (here refl)
                               ψϕ⊢ϕ·ψ = ⊢-conj ψϕ⊢ϕ ψϕ⊢ψ
                            in ⊢-intr (⊢-intr ψϕ⊢ϕ·ψ)
  Hilbert⇒Minimal ⊢-PROJ0 = let ϕ·ψ⊢ϕ = ⊢-proj0 (⊢-ax (here refl))
                             in ⊢-intr ϕ·ψ⊢ϕ
  Hilbert⇒Minimal ⊢-PROJ1 = let ϕ·ψ⊢ϕ = ⊢-proj1 (⊢-ax (here refl))
                             in ⊢-intr ϕ·ψ⊢ϕ
  -- c
  fact1 : {Γ : Context} {ϕ ψ : Formula} → Γ ⊢ ϕ → Γ ⊢ ψ ⇒ ϕ
  fact1 ϕ = let ϕ⇒ψ⇒ϕ = ⊢-K
                ψ⇒ϕ   = ⊢-MP ϕ⇒ψ⇒ϕ ϕ
             in ψ⇒ϕ

  fact2 : {Γ : Context} {ϕ ψ γ : Formula} → Γ ⊢ ϕ ⇒ ψ ⇒ γ → Γ ⊢ ϕ ⇒ ψ → Γ ⊢ ϕ ⇒ γ
  fact2 ϕψγ ϕψ = let ϕψγ⇒ϕψ⇒ϕγ = ⊢-S
                     ϕψ⇒ϕγ     = ⊢-MP ϕψγ⇒ϕψ⇒ϕγ ϕψγ
                     ϕγ        = ⊢-MP ϕψ⇒ϕγ     ϕψ
                  in ϕγ

  fact3 : {Γ : Context} {ϕ : Formula} → Γ ⊢ ϕ ⇒ ϕ
  fact3 {_} {ϕ} = let ϕ[ϕϕ]ϕ⇒ϕϕϕ⇒ϕϕ = ⊢-S
                      ϕ[ϕϕ]ϕ = ⊢-K {ψ = ϕ ⇒ ϕ}
                      ϕϕϕ⇒ϕϕ = ⊢-MP ϕ[ϕϕ]ϕ⇒ϕϕϕ⇒ϕϕ ϕ[ϕϕ]ϕ
                      ϕϕϕ    = ⊢-K
                      ϕϕ     = ⊢-MP ϕϕϕ⇒ϕϕ ϕϕϕ
                   in ϕϕ

  -- d
  deduction-theorem : {Γ : Context} {ϕ ψ : Formula} → ϕ ∷ Γ ⊢ ψ → Γ ⊢ ϕ ⇒ ψ
  deduction-theorem ⊢-TRUE = fact1 (⊢-TRUE)
  deduction-theorem (⊢-AX (here refl)) = fact3
  deduction-theorem (⊢-AX (there x)) = fact1 (⊢-AX x)
  deduction-theorem (⊢-MP ϕ⊢γ⇒ψ ϕ⊢γ) = let ϕγψ = deduction-theorem ϕ⊢γ⇒ψ
                                           ϕγ  = deduction-theorem ϕ⊢γ
                                           ϕψ  = fact2 ϕγψ ϕγ
                                        in ϕψ
  deduction-theorem ⊢-K = fact1 ⊢-K
  deduction-theorem ⊢-S = fact1 ⊢-S
  deduction-theorem ⊢-CONJ = fact1 ⊢-CONJ
  deduction-theorem ⊢-PROJ0 = fact1 ⊢-PROJ0
  deduction-theorem ⊢-PROJ1 = fact1 ⊢-PROJ1


  -- e
  Minimal⇒Hilbert : {Γ : Context} {ϕ : Formula} → Γ ⊢m ϕ → Γ ⊢ ϕ
  Minimal⇒Hilbert ⊢-true = ⊢-TRUE
  Minimal⇒Hilbert (⊢-ax x) = ⊢-AX x
  Minimal⇒Hilbert (⊢-intr ⊢ϕ) = deduction-theorem (Minimal⇒Hilbert ⊢ϕ)
  Minimal⇒Hilbert (⊢-elim ⊢ϕ⇒ψ ⊢ϕ) = let ϕψ = Minimal⇒Hilbert ⊢ϕ⇒ψ
                                         ϕ  = Minimal⇒Hilbert ⊢ϕ
                                      in ⊢-MP ϕψ ϕ
  Minimal⇒Hilbert (⊢-conj ⊢ϕ ⊢ψ) = let ϕ = Minimal⇒Hilbert ⊢ϕ
                                       ψ = Minimal⇒Hilbert ⊢ψ
                                    in ⊢-MP (⊢-MP ⊢-CONJ ϕ) ψ
  Minimal⇒Hilbert (⊢-proj0 ⊢ϕ·ψ) = let ϕ·ψ = Minimal⇒Hilbert ⊢ϕ·ψ
                                    in ⊢-MP ⊢-PROJ0 ϕ·ψ
  Minimal⇒Hilbert (⊢-proj1 ⊢ϕ·ψ) = let ϕ·ψ = Minimal⇒Hilbert ⊢ϕ·ψ
                                    in ⊢-MP ⊢-PROJ1 ϕ·ψ



{-
-- ### Sub Section 2.2 Abstract reduction systems
-}
module ARS where
  variable
    -- terms
    A : Set
    -- reduction relation
    R : A → A → Set
    -- typing relation T
    T : A → Set
    -- valuation relation V
    V : A → Set

  -- a
  data SN[_] (R : A → A → Set) (x : A) : Set where
    SN : ({y : A} → R x y → SN[ R ] y) → SN[ R ] x

  -- b
  data Closure[_] (R : A → A → Set) : A → A → Set where
    refl : {x : A} → Closure[ R ] x x
    step : {x y : A} → R x y → Closure[ R ] x y
    transit : {x y z : A} → Closure[ R ] x y → Closure[ R ] y z → Closure[ R ] x z

  -- c
  SN-on-Closure : {x y : A} → SN[ R ] x → Closure[ R ] x y → SN[ R ] y
  SN-on-Closure SNx refl = SNx
  SN-on-Closure (SN f) (step xRy) = f xRy
  SN-on-Closure SNx (transit xRz zRy) = let SNz = SN-on-Closure SNx xRz
                                            SNy = SN-on-Closure SNz zRy
                                         in SNy

  variable
    preserve : {x y : A} → T x → R x y → T y
    progress : {x : A} → T x → Σ (λ y → R x y) ⊎ V x

  -- d
  SN→WN : (preserve : {x y : A} → T x → R x y → T y)
        → (progress : {x : A} → T x → Σ (λ (y : A) → R x y) ⊎ V x)
        → (x : A)
        → T x → SN[ R ] x
        → Σ (λ (z : A) → Closure[ R ] x z × T z × V z)
  SN→WN pres prog x Tx (SN R→SN)
    with prog Tx
  ... | left ⟨ y , xRy ⟩
          = let Ty  = pres Tx xRy
                SNy = R→SN xRy
                ⟨ z , ⟨ yR*z , ⟨ Tz , Vz ⟩ ⟩ ⟩ = SN→WN pres prog y Ty SNy
                xR*z = transit (step xRy) yR*z
             in ⟨ z , ⟨ xR*z , ⟨ Tz , Vz ⟩ ⟩ ⟩
  ... | right Vx
          = let xR*x = refl
             in ⟨ x , ⟨ xR*x , ⟨ Tx , Vx ⟩ ⟩ ⟩

  -- e
  SN-double-ind : {A B : Set}
                → {R : A → A → Set} {S : B → B → Set}
                → {P : A → B → Set}
                → ((a : A) (b : B)
                  → ((a' : A) → R a a' → SN[ R ] a')
                  → ((a' : A) → R a a' → P a' b)
                  → ((b' : B) → S b b' → SN[ S ] b')
                  → ((b' : B) → S b b' → P a b')
                  → P a b)
                → (x : A) (y : B)
                → SN[ R ] x
                → SN[ S ] y
                → P x y
  SN-double-ind f x y (SN R→SN) (SN S→SN) = f x y
      (λ { x' xRx' → R→SN xRx' })
      (λ { x' xRx' → let SNx' = R→SN xRx'
                         SNy  = SN S→SN
                      in SN-double-ind f x' y  SNx' SNy  })
      (λ { y' ySy' → S→SN ySy' })
      (λ { y' ySy' → let SNy' = S→SN ySy'
                         SNx  = SN R→SN
                      in SN-double-ind f x  y' SNx  SNy' })

{-
-- ### Sub Section 2.3 Combinatory Logic
-}
module Combinatory-Logic where
  open Hilbert-System
    using (⊢-TRUE ; ⊢-AX ; ⊢-MP ;
           ⊢-K ; ⊢-S ;
           ⊢-CONJ ; ⊢-PROJ0 ; ⊢-PROJ1)
    renaming (_⊢_ to _⊢'_)
  open ARS using (SN[_] ; SN ; Closure[_] ; refl ; step ; transit)

  infixl 15 _·_
  data Term : Set where
    O : Term
    S : Term
    K : Term
    Pair : Term
    Proj0 : Term
    Proj1 : Term
    𝕍 : ℕ → Term
    _·_ : Term → Term → Term

  -- a
  data _⊢_~_ (Γ : Context) : Term → Formula → Set where
    ⊢-O : Γ ⊢ O ~ ⊤
    ⊢-AX : {n : ℕ} {ϕ : Formula} → Γ ! n ≔ ϕ → Γ ⊢ 𝕍 n ~ ϕ
    ⊢-MP : {u v : Term} {ϕ ψ : Formula} → Γ ⊢ u ~ ϕ ⇒ ψ → Γ ⊢ v ~ ϕ → Γ ⊢ u · v ~ ψ
    ⊢-K : {ϕ ψ : Formula} → Γ ⊢ K ~ ϕ ⇒ ψ ⇒ ϕ
    ⊢-S : {ϕ ψ γ : Formula} → Γ ⊢ S ~ (ϕ ⇒ ψ ⇒ γ) ⇒ (ϕ ⇒ ψ) ⇒ ϕ ⇒ γ
    ⊢-Pair : {ϕ ψ : Formula} → Γ ⊢ Pair ~ ϕ ⇒ ψ ⇒ (ϕ /\ ψ)
    ⊢-Proj0 : {ϕ ψ : Formula} → Γ ⊢ Proj0 ~ (ϕ /\ ψ) ⇒ ϕ
    ⊢-Proj1 : {ϕ ψ : Formula} → Γ ⊢ Proj1 ~ (ϕ /\ ψ) ⇒ ψ

  variable
    Γ : Context


  Hilbert⇒SK : {ϕ : Formula} → Γ ⊢' ϕ → Σ (λ e → Γ ⊢ e ~ ϕ)
  Hilbert⇒SK ⊢-TRUE = ⟨ O , ⊢-O ⟩
  Hilbert⇒SK (⊢-AX ϕ∈Γ) = let ⟨ n , at-n ⟩ = mem→idx ϕ∈Γ
                           in ⟨ 𝕍 n , ⊢-AX at-n ⟩
  Hilbert⇒SK (⊢-MP ⊢'ϕ⇒ψ ⊢'ϕ) = let ⟨ u , ⊢ϕ⇒ψ ⟩ = Hilbert⇒SK ⊢'ϕ⇒ψ
                                    ⟨ v , ⊢ϕ   ⟩ = Hilbert⇒SK ⊢'ϕ
                                 in ⟨ u · v , ⊢-MP ⊢ϕ⇒ψ ⊢ϕ ⟩
  Hilbert⇒SK ⊢-K = ⟨ K , ⊢-K ⟩
  Hilbert⇒SK ⊢-S = ⟨ S , ⊢-S ⟩
  Hilbert⇒SK ⊢-CONJ = ⟨ Pair , ⊢-Pair ⟩
  Hilbert⇒SK ⊢-PROJ0 = ⟨ Proj0 , ⊢-Proj0 ⟩
  Hilbert⇒SK ⊢-PROJ1 = ⟨ Proj1 , ⊢-Proj1 ⟩


  SK⇒Hilbert : {ϕ : Formula} → Σ (λ e → Γ ⊢ e ~ ϕ) → Γ ⊢' ϕ
  SK⇒Hilbert ⟨ O , ⊢-O ⟩ = ⊢-TRUE
  SK⇒Hilbert ⟨ 𝕍 n , ⊢-AX at-n ⟩ = let ϕ∈Γ = idx→mem ⟨ n , at-n ⟩
                                    in ⊢-AX ϕ∈Γ
  SK⇒Hilbert ⟨ u · v , ⊢-MP u:ϕ⇒ψ v:ϕ ⟩ = let ⊢ϕ⇒ψ = SK⇒Hilbert ⟨ u , u:ϕ⇒ψ ⟩
                                              ⊢ϕ   = SK⇒Hilbert ⟨ v , v:ϕ   ⟩
                                           in ⊢-MP ⊢ϕ⇒ψ ⊢ϕ
  SK⇒Hilbert ⟨ K , ⊢-K ⟩ = ⊢-K
  SK⇒Hilbert ⟨ S , ⊢-S ⟩ = ⊢-S
  SK⇒Hilbert ⟨ Pair , ⊢-Pair ⟩ = ⊢-CONJ
  SK⇒Hilbert ⟨ Proj0 , ⊢-Proj0 ⟩ = ⊢-PROJ0
  SK⇒Hilbert ⟨ Proj1 , ⊢-Proj1 ⟩ = ⊢-PROJ1

  -- b
  Hilbert⇔SK : {ϕ : Formula} → (Σ (λ e → Γ ⊢ e ~ ϕ)) ⇔ (Γ ⊢' ϕ)
  Hilbert⇔SK = record { ⇒ = SK⇒Hilbert ; ⇐ = Hilbert⇒SK }

  -- c
  infix 10 _≻_
  data _≻_ : Term → Term → Set where
    ≻K  : {x y : Term}    → K · x · y      ≻ x
    ≻S  : {f g x : Term}  → S · f · g · x  ≻ f · x · (g · x)
    ≻·l : {x' x y : Term} → x ≻ x' → x · y ≻ x' · y
    ≻·r : {y' x y : Term} → y ≻ y' → x · y ≻ x  · y'
    ≻Proj0 : {x y : Term} → Proj0 · (Pair · x · y) ≻ x
    ≻Proj1 : {x y : Term} → Proj1 · (Pair · x · y) ≻ y


  infix 10 _≻*_
  _≻*_ : Term → Term → Set
  _≻*_ = Closure[ _≻_ ]

  -- d
  ≻-preserve : {x x' : Term} {ϕ : Formula} → Γ ⊢ x ~ ϕ  → x ≻ x' → Γ ⊢ x' ~ ϕ
  ≻-preserve (⊢-MP (⊢-MP ⊢-K x:ϕ) y:ψ) ≻K = x:ϕ
  ≻-preserve (⊢-MP (⊢-MP (⊢-MP ⊢-S f:ϕ⇒ψ⇒γ) g:ϕ⇒ψ) x:ϕ) ≻S
    = let fx:ψ⇒γ = ⊢-MP f:ϕ⇒ψ⇒γ x:ϕ
          gx:ψ   = ⊢-MP g:ϕ⇒ψ  x:ϕ
       in ⊢-MP fx:ψ⇒γ gx:ψ
  ≻-preserve (⊢-MP x:ϕ⇒ψ y:ϕ) (≻·l x≻x') = let x':ϕ⇒ψ = ≻-preserve x:ϕ⇒ψ x≻x'
                                            in ⊢-MP x':ϕ⇒ψ y:ϕ
  ≻-preserve (⊢-MP x:ϕ⇒ψ y:ϕ) (≻·r y≻y') = let y':ϕ = ≻-preserve y:ϕ y≻y'
                                            in ⊢-MP x:ϕ⇒ψ y':ϕ
  ≻-preserve (⊢-MP ⊢-Proj0 (⊢-MP (⊢-MP ⊢-Pair x:ϕ) y:ψ)) ≻Proj0 = x:ϕ
  ≻-preserve (⊢-MP ⊢-Proj1 (⊢-MP (⊢-MP ⊢-Pair x:ϕ) y:ψ)) ≻Proj1 = y:ψ


  -- e
  ≻*·l : {x x' y : Term} → x ≻* x' → x · y ≻* x' · y
  ≻*·l refl = refl
  ≻*·l (step x≻x') = step (≻·l x≻x')
  ≻*·l (transit x≻*z z≻*x') = let xy≻*zy = ≻*·l x≻*z
                                  zy≻*x'y = ≻*·l z≻*x'
                               in transit xy≻*zy zy≻*x'y


  ≻*·r : {x y y' : Term} → y ≻* y' → x · y ≻* x · y'
  ≻*·r refl = refl
  ≻*·r (step y≻y') = step (≻·r y≻y')
  ≻*·r (transit y≻*z z≻*y') = let xy≻*xz  = ≻*·r y≻*z
                                  xz≻*xy' = ≻*·r z≻*y'
                               in transit xy≻*xz xz≻*xy'

  -- f
  subject-reduction : {x x' : Term} {ϕ : Formula}
                    → Γ ⊢ x  ~ ϕ → x ≻* x' → Γ ⊢ x' ~ ϕ
  subject-reduction x:ϕ refl = x:ϕ
  subject-reduction x:ϕ (step x≻x') = ≻-preserve x:ϕ x≻x'
  subject-reduction x:ϕ (transit x≻y y≻z) = let y:ϕ = subject-reduction x:ϕ x≻y
                                                z:ϕ = subject-reduction y:ϕ y≻z
                                             in z:ϕ

  -- g
  SN·lemma : (u v : Term) → SN[ _≻_ ] (u · v) → SN[ _≻_ ] u
  SN·lemma O     v sn = SN λ ()
  SN·lemma S     v sn = SN λ ()
  SN·lemma K     v sn = SN λ ()
  SN·lemma Pair  v sn = SN λ ()
  SN·lemma Proj0 v sn = SN λ ()
  SN·lemma Proj1 v sn = SN λ ()
  SN·lemma (𝕍 n) v sn = SN λ ()
  SN·lemma (u · v) w (SN ≻→SN) = SN helper
    where
      helper : {e : Term} → u · v ≻ e → SN[ _≻_ ] e
      helper {e} red-uv = let red-uvw = ≻·l red-uv
                              sn = ≻→SN red-uvw
                           in SN·lemma e w sn

  -- a similar version of SN·lemma
  SN·lemma' : (u v : Term) → SN[ _≻_ ] (u · v) → SN[ _≻_ ] v
  SN·lemma' u O sn = SN λ ()
  SN·lemma' u S sn = SN λ ()
  SN·lemma' u K sn = SN λ ()
  SN·lemma' u Pair sn = SN λ ()
  SN·lemma' u Proj0 sn = SN λ ()
  SN·lemma' u Proj1 sn = SN λ ()
  SN·lemma' u (𝕍 x) sn = SN λ ()
  SN·lemma' u (v · w) (SN ≻→SN) = SN helper
    where
      helper : {e : Term} → v · w ≻ e → SN[ _≻_ ] e
      helper {e} red-uv = let red-uvw = ≻·r red-uv
                              sn = ≻→SN red-uvw
                           in SN·lemma' u e sn



  headO : Term → Bool
  headO O = False
  headO (e · _) = headO e
  headO _ = True

  O·-not-typeable : {ϕ ψ : Formula} (e : Term) → headO e ≡ False → ¬ ([] ⊢ e ~ ϕ ⇒ ψ)
  O·-not-typeable (u · v) ¬headO (⊢-MP u:A⇒ϕ⇒ψ v:A) = O·-not-typeable u ¬headO u:A⇒ϕ⇒ψ

  -- h
  neutral : Term → Bool
  neutral O              = False
  neutral K              = False
  neutral (K · e)        = False
  neutral S              = False
  neutral (S · e)        = False
  neutral (S · e · e')   = False
  neutral Pair           = False
  neutral Proj0          = False
  neutral Proj1          = False
  neutral (Pair · x)     = False
  neutral (Pair · x · y) = False
  neutral e              = headO e

  neutral→headO : (x y z w : Term) → neutral (x · y · z · w) ≡ False → headO x ≡ False
  neutral→headO x _ _ _ neu with headO x
  neutral→headO x _ _ _ neu | False = refl

  neutral· : (u v : Term) → neutral u ≡ True → neutral (u · v) ≡ True
  neutral· (𝕍 n) v refl           = refl
  neutral· (𝕍 n · t) v refl       = refl
  neutral· (K · y · z) v refl     = refl
  neutral· (𝕍 n · y · z) v refl   = refl
  neutral· (Proj0 · p) v refl     = refl
  neutral· (Proj1 · p) v refl     = refl
  neutral· (Proj0 · p · u) v refl = refl
  neutral· (Proj1 · p · u) v refl = refl
  neutral· (x · y · z · w) v neu with headO x
  neutral· (x · y · z · w) v refl | True = refl
  neutral· (x · y · z · w) v ()   | False


  -- a term of a conjunction type is a pair
  neutral-conjunction-is-pair : {e : Term} {ϕ ψ : Formula}
                 → neutral e ≡ False
                 → [] ⊢ e ~ ϕ /\ ψ
                 → Σ (λ x → Σ (λ y → e ≡ (Pair · x · y)))
  neutral-conjunction-is-pair {e · x · y · z} neu (⊢-MP (⊢-MP (⊢-MP e:A x:t1) y:t2) z:t3)
    = let headO-e = neutral→headO e x y z neu
       in absurd (O·-not-typeable e headO-e e:A)
  neutral-conjunction-is-pair {Pair · x · y} neu (⊢-MP (⊢-MP ⊢-Pair x:ϕ) y:ψ) = ⟨ x , ⟨ y , refl ⟩ ⟩


  -- i
  ≻-progress : (e : Term) {ϕ : Formula}
             → [] ⊢ e ~ ϕ → Σ (e ≻_) ⊎ neutral e ≡ False
  ≻-progress (𝕍 n) (⊢-AX ())
  ≻-progress O     ⊢-O     = right refl
  ≻-progress S     ⊢-S     = right refl
  ≻-progress K     ⊢-K     = right refl
  ≻-progress Pair  ⊢-Pair  = right refl
  ≻-progress Proj0 ⊢-Proj0 = right refl
  ≻-progress Proj1 ⊢-Proj1 = right refl
  ≻-progress (u · v) (⊢-MP u:ϕ⇒ψ v:ϕ)
    with ≻-progress u u:ϕ⇒ψ
  ... | left ⟨ u' , u≻u' ⟩ = left ⟨ u' · v , ≻·l u≻u' ⟩
  ... | right ¬neu-u
    with ≻-progress v v:ϕ
  ... | left ⟨ v' , v≻v' ⟩ = left ⟨ u · v' , ≻·r v≻v' ⟩
  ... | right ¬neu-v = lemma u v u:ϕ⇒ψ v:ϕ ¬neu-u ¬neu-v
    where

      lemma : {ϕ ψ : Formula} (u v : Term)
            → [] ⊢ u ~ ϕ ⇒ ψ
            → [] ⊢ v ~ ϕ
            → neutral u ≡ False
            → neutral v ≡ False
            → Σ ((u · v) ≻_) ⊎ neutral (u · v) ≡ False
      lemma O _ _ _ _ _ = right refl
      lemma S _ _ _ _ _ = right refl
      lemma K _ _ _ _ _ = right refl
      lemma Pair _ _ _ _ _  = right refl
      lemma (O · u) _ _ _ _ _ = right refl
      lemma (K · u) _ _ _ _ _ = left ⟨ u , ≻K ⟩
      lemma (S · v) _ _ _ _ _ = right refl
      lemma (O · x · y) _ _ _ _ _  = right refl
      lemma (S · f · g) x _ _ _ _ = left ⟨ f · x · (g · x) , ≻S ⟩
      lemma Proj0 p ⊢-Proj0 p:ϕ·ψ refl np with neutral-conjunction-is-pair np p:ϕ·ψ
      ... | ⟨ x , ⟨ y , refl ⟩ ⟩ = left ⟨ x , ≻Proj0 ⟩
      lemma Proj1 p ⊢-Proj1 p:ϕ·ψ refl np with neutral-conjunction-is-pair np p:ϕ·ψ
      ... | ⟨ x , ⟨ y , refl ⟩ ⟩ = left ⟨ y , ≻Proj1 ⟩
      lemma (Pair · x) y (⊢-MP ⊢-Pair x:ϕ) y:ψ refl ny = right refl
      lemma (Pair · x · y) v (⊢-MP (⊢-MP () x:ϕ) y:ψ) v:γ _ _
      lemma (e · x · y · z) v u:ϕ⇒ψ v:ϕ nu nv with headO e
      lemma (e · x · y · z) v u:ϕ⇒ψ v:ϕ () nv | True
      lemma (e · x · y · z) v u:ϕ⇒ψ v:ϕ nu nv | False = right refl


{-
-- ### Sub Section 2.4 Normalisation
-}
module Normalisation where
  open ARS using (SN[_] ; SN ; SN→WN ;
                  Closure[_] ; refl ; step ; transit ;
                  SN-on-Closure ; SN-double-ind)
  open Combinatory-Logic using (Term ; O ; S ; K ; 𝕍 ; _·_ ; Pair ; Proj0 ; Proj1 ;
                                _≻_ ; ≻K ; ≻S ; ≻·l ; ≻·r ; ≻Proj0 ; ≻Proj1 ;
                                _≻*_ ; ≻*·l ; ≻*·r ;
                                _⊢_~_ ; ⊢-O ; ⊢-AX ; ⊢-MP ; ⊢-K ; ⊢-S ; ⊢-Pair ; ⊢-Proj0 ; ⊢-Proj1 ;
                                neutral ; neutral· ;
                                ≻-preserve ; ≻-progress ;
                                SN·lemma ; SN·lemma' )

  SN≻ : Term → Set
  SN≻ = SN[ _≻_ ]

  infix 3 ⊨_~_
  ⊨_~_ : Term → Formula → Set
  ⊨ e ~ ⊤     = SN≻ e
  ⊨ e ~ ⊥     = SN≻ e
  ⊨ e ~ var n = SN≻ e
  ⊨ e ~ ϕ ⇒ ψ = {x : Term} → ⊨ x ~ ϕ → ⊨ e · x ~ ψ
  ⊨ e ~ ϕ /\ ψ = (⊨ Proj0 · e ~ ϕ) × (⊨ Proj1 · e ~ ψ)

  -- theorem 1.1
  sem-SN : {e : Term} (ϕ : Formula)
         → ⊨ e ~ ϕ
         → SN≻ e
  -- theorem 1.2
  sem-preserve : {e : Term} (ϕ : Formula)
               → ⊨ e ~ ϕ
               → ({e' : Term} → e ≻* e' → ⊨ e' ~ ϕ)
  -- theorem 1.3
  sem-neutral : {e : Term} (ϕ : Formula)
              → (neu-e : neutral e ≡ True)
              → ({e' : Term} → e ≻ e' → ⊨ e' ~ ϕ)
              → ⊨ e ~ ϕ

  -- corollary of theorem 1.3: a variable term is always semantically well-typed
  -- because it is neutral and cannot be further reduced.
  ⊨𝕍n:ϕ : {n : ℕ} (ϕ : Formula) → ⊨ 𝕍 n ~ ϕ
  ⊨𝕍n:ϕ ϕ = sem-neutral ϕ refl λ ()

  -- proof of theorem 1.1
  sem-SN     ⊤       sem = sem
  sem-SN     ⊥       sem = sem
  sem-SN     (var x) sem = sem
  sem-SN {e} (ϕ ⇒ ψ) ⊨e:ϕ⇒ψ =
    let v        = 𝕍 Z
        ⊨v:ϕ     = ⊨𝕍n:ϕ ϕ
        ⊨e·v:ψ   = ⊨e:ϕ⇒ψ ⊨v:ϕ
        SN≻e·v   = sem-SN {e · v} ψ ⊨e·v:ψ
        SN≻e     = SN·lemma e v SN≻e·v
     in SN≻e
  sem-SN {e} (ϕ /\ ψ) ⟨ ⊨x:ϕ , ⊨y:ψ ⟩ =
     let SN≻proj0e·v = sem-SN {Proj0 · e} ϕ ⊨x:ϕ
         SN≻e        = SN·lemma' Proj0 e SN≻proj0e·v
      in SN≻e


  -- proof of theorem 1.2
  sem-preserve     ⊤       sem e≻*e' = SN-on-Closure sem e≻*e'
  sem-preserve     ⊥       sem e≻*e' = SN-on-Closure sem e≻*e'
  sem-preserve     (var x) sem e≻*e' = SN-on-Closure sem e≻*e'
  sem-preserve {e} (ϕ ⇒ ψ) ⊨e:ϕ⇒ψ {e'} e≻*e' = ⊨e':ϕ⇒ψ
    where
      ⊨e':ϕ⇒ψ : ⊨ e' ~ ϕ ⇒ ψ
      ⊨e':ϕ⇒ψ {x} ⊨x:ϕ = let ⊨e·x:ψ    = ⊨e:ϕ⇒ψ ⊨x:ϕ
                             e·x≻*e'·x = ≻*·l e≻*e'
                          in sem-preserve {e · x} ψ ⊨e·x:ψ {e' · x} e·x≻*e'·x
  sem-preserve {e} (ϕ /\ ψ) ⟨ ⊨x:ϕ , ⊨y:ψ ⟩ {e'} e≻*e' =
    let x≻*x' = ≻*·r e≻*e'
        y≻*y' = ≻*·r e≻*e'
        ⊨x':ϕ = sem-preserve ϕ ⊨x:ϕ x≻*x'
        ⊨y':ψ = sem-preserve ψ ⊨y:ψ y≻*y'
     in ⟨ ⊨x':ϕ , ⊨y':ψ ⟩

  -- proof of theorem 1.3
  sem-neutral     ⊤       neu-e ≻→⊨ = SN λ { e≻e' → sem-SN ⊤       (≻→⊨ e≻e') }
  sem-neutral     ⊥       neu-e ≻→⊨ = SN λ { e≻e' → sem-SN ⊥       (≻→⊨ e≻e') }
  sem-neutral     (var x) neu-e ≻→⊨ = SN λ { e≻e' → sem-SN (var x) (≻→⊨ e≻e') }
  sem-neutral {e} (ϕ ⇒ ψ) neu-e ≻→⊨ = λ { ⊨x:ϕ → SN→⊨ϕ⇒ψ (sem-SN ϕ ⊨x:ϕ) ⊨x:ϕ }
    where
      SN→⊨ϕ⇒ψ : {x : Term} → SN≻ x → ⊨ x ~ ϕ → ⊨ e · x ~ ψ
      SN→⊨ϕ⇒ψ {x} (SN SN≻x) ⊨x:ϕ =
        let neu-e·x = neutral· e x neu-e
            ⊨e·x:ψ  = sem-neutral {e · x} ψ neu-e·x
                        λ { (≻·l e≻e') → (≻→⊨ e≻e') ⊨x:ϕ
                          ; (≻·r x≻x') →
                            let ⊨x':ϕ = sem-preserve ϕ ⊨x:ϕ (step x≻x')
                                SN≻x' = SN≻x x≻x'
                             in SN→⊨ϕ⇒ψ SN≻x' ⊨x':ϕ }
         in ⊨e·x:ψ
  sem-neutral {e} (ϕ /\ ψ) neu-e ≻→⊨ =
    let ⊨x:ϕ = sem-neutral {Proj0 · e} ϕ refl λ { (≻·r e≻e') → Σ.fst (≻→⊨ e≻e') }
        ⊨y:ψ = sem-neutral {Proj1 · e} ψ refl λ { (≻·r e≻e') → Σ.snd (≻→⊨ e≻e') }
     in ⟨ ⊨x:ϕ , ⊨y:ψ ⟩


  -- lemma 2: semantic type of K
  ⊨K : (ϕ ψ : Formula) → ⊨ K ~ ϕ ⇒ ψ ⇒ ϕ
  ⊨K ϕ ψ {x} ⊨x:ϕ {y} ⊨y:ψ =
    let SN≻x     = sem-SN ϕ ⊨x:ϕ
        SN≻y     = sem-SN ψ ⊨y:ψ
     in helper ⊨x:ϕ SN≻x ⊨y:ψ SN≻y
    where
      helper : {x y : Term}
             → ⊨ x ~ ϕ → SN≻ x
             → ⊨ y ~ ψ → SN≻ y
             → ⊨ K · x · y ~ ϕ
      helper {x} {y} ⊨x:ϕ (SN SN≻x) ⊨y:ψ (SN SN≻y) =
        sem-neutral {K · x · y} ϕ refl
          λ { ≻K → ⊨x:ϕ
            ; (≻·l (≻·r x≻x')) → let ⊨x':ϕ = sem-preserve ϕ ⊨x:ϕ (step x≻x')
                                     SN≻x' = SN≻x x≻x'
                                  in helper ⊨x':ϕ SN≻x' ⊨y:ψ (SN SN≻y)
            ; (≻·r y≻y') →       let ⊨y':ψ = sem-preserve ψ ⊨y:ψ (step y≻y')
                                     SN≻y' = SN≻y y≻y'
                                  in helper ⊨x:ϕ (SN SN≻x) ⊨y':ψ SN≻y' }

  -- lemma 3: semantic type of S
  -- S f g x => f x (g x)
  ⊨S : (ϕ ψ γ : Formula) → ⊨ S ~ (ϕ ⇒ ψ ⇒ γ) ⇒ (ϕ ⇒ ψ) ⇒ ϕ ⇒ γ
  ⊨S ϕ ψ γ {f} ⊨f:ϕψγ {g} ⊨g:ϕψ {x} ⊨x:ϕ =
    let SN≻f     = sem-SN (ϕ ⇒ ψ ⇒ γ) ⊨f:ϕψγ
        SN≻g     = sem-SN (ϕ ⇒ ψ)     ⊨g:ϕψ
        SN≻x     = sem-SN  ϕ          ⊨x:ϕ
     in helper ⊨f:ϕψγ SN≻f ⊨g:ϕψ SN≻g ⊨x:ϕ SN≻x
    where
      helper : {f g x : Term}
             → ⊨ f ~ ϕ ⇒ ψ ⇒ γ → SN≻ f
             → ⊨ g ~ ϕ ⇒ ψ     → SN≻ g
             → ⊨ x ~ ϕ         → SN≻ x
             → ⊨ S · f · g · x ~ γ
      helper {f} {g} {x} ⊨f:ϕψγ (SN SN≻f) ⊨g:ϕψ (SN SN≻g) ⊨x:ϕ (SN SN≻x) =
        sem-neutral {S · f · g · x} γ refl
          λ { ≻S → ⊨f:ϕψγ ⊨x:ϕ (⊨g:ϕψ ⊨x:ϕ)
            ; (≻·l (≻·l (≻·r f≻f'))) →
                    let ⊨f':ϕψγ = sem-preserve (ϕ ⇒ ψ ⇒ γ) ⊨f:ϕψγ (step f≻f')
                        SN≻f'   = SN≻f f≻f'
                     in helper ⊨f':ϕψγ SN≻f' ⊨g:ϕψ (SN SN≻g) ⊨x:ϕ (SN SN≻x)
            ; (≻·l (≻·r g≻g')) →
                    let ⊨g':ϕψ = sem-preserve (ϕ ⇒ ψ) ⊨g:ϕψ (step g≻g')
                        SN≻g'  = SN≻g g≻g'
                     in helper ⊨f:ϕψγ (SN SN≻f) ⊨g':ϕψ SN≻g' ⊨x:ϕ (SN SN≻x)
            ; (≻·r x≻x') →
                    let ⊨x':ϕ = sem-preserve ϕ ⊨x:ϕ (step x≻x')
                        SN≻x' = SN≻x x≻x'
                     in helper ⊨f:ϕψγ (SN SN≻f) ⊨g:ϕψ (SN SN≻g) ⊨x':ϕ SN≻x' }

  -- semantically well-typed property for the O combinator
  -- O does not reduce
  ⊨O : ⊨ O ~ ⊤
  ⊨O = SN λ ()

  -- semantically well-typed property for projections
  ⊨Proj0 : (ϕ ψ : Formula) → ⊨ Proj0 ~ ϕ /\ ψ ⇒ ϕ
  ⊨Proj0 ϕ ψ ⟨ ⊨fst , ⊨snd ⟩ = ⊨fst

  -- semantically well-typed property for projections
  ⊨Proj1 : (ϕ ψ : Formula) → ⊨ Proj1 ~ ϕ /\ ψ ⇒ ψ
  ⊨Proj1 ϕ ψ ⟨ ⊨fst , ⊨snd ⟩ = ⊨snd

  -- semantically well-typed property for the pair
  ⊨Pair : (ϕ ψ : Formula) → ⊨ Pair ~ ϕ ⇒ ψ ⇒ ϕ /\ ψ
  ⊨Pair ϕ ψ {x} ⊨x:ϕ {y} ⊨y:ψ =
    let sn-x = sem-SN {x} ϕ ⊨x:ϕ
        sn-y = sem-SN {y} ψ ⊨y:ψ
     in helper x ⊨x:ϕ sn-x y ⊨y:ψ sn-y
    where
      ⊨proj0 : ⊨ Proj0 ~ ϕ /\ ψ ⇒ ϕ
      ⊨proj0 = ⊨Proj0 ϕ ψ

      ⊨proj1 : ⊨ Proj1 ~ ϕ /\ ψ ⇒ ψ
      ⊨proj1 = ⊨Proj1 ϕ ψ

      sem-≻x : {x x' : Term} → ⊨ x ~ ϕ → x ≻ x' → ⊨ x' ~ ϕ
      sem-≻x ⊨x:ϕ x≻x' = sem-preserve ϕ ⊨x:ϕ (step x≻x')

      sem-≻y : {y y' : Term} → ⊨ y ~ ψ → y ≻ y' → ⊨ y' ~ ψ
      sem-≻y ⊨y:ψ y≻y' = sem-preserve ψ ⊨y:ψ (step y≻y')

      helper : (x : Term) (sem-x : ⊨ x ~ ϕ) (sn-x : SN≻ x)
             → (y : Term) (sem-y : ⊨ y ~ ψ) (sn-y : SN≻ y)
             → ⊨ Pair · x · y ~ ϕ /\ ψ
      helper x sem-x (SN sn-x) y sem-y (SN sn-y) =
               ⟨ sem-neutral {Proj0 · (Pair · x · y)} ϕ refl
                 (λ { (≻·r (≻·l (≻·r {x'} x≻))) → ⊨proj0 (helper x' (sem-≻x sem-x x≻) (sn-x x≻) y sem-y (SN sn-y))
                    ; (≻·r (≻·r {y'} y≻))       → ⊨proj0 (helper x sem-x (SN sn-x) y' (sem-≻y sem-y y≻) (sn-y y≻))
                    ; ≻Proj0 → sem-x } )
               , sem-neutral {Proj1 · (Pair · x · y)} ψ refl
                 (λ { (≻·r (≻·l (≻·r {x'} x≻))) → ⊨proj1 (helper x' (sem-≻x sem-x x≻) (sn-x x≻) y sem-y (SN sn-y))
                    ; (≻·r (≻·r {y'} y≻))       → ⊨proj1 (helper x sem-x (SN sn-x) y' (sem-≻y sem-y y≻) (sn-y y≻))
                      ; ≻Proj1 → sem-y } ) ⟩



  -- theorem 4: syntactically well-typed implies semantically well-typed
  ⊢→⊨ : {Γ : Context} {e : Term} {ϕ : Formula}
      → ({n : ℕ} {ϕ : Formula} → Γ ! n ≔ ϕ → ⊨ 𝕍 n ~ ϕ)
      → Γ ⊢ e ~ ϕ
      → ⊨ e ~ ϕ
  ⊢→⊨ {Γ} {𝕍 n} {ϕ}                             f (⊢-AX x) = f x
  ⊢→⊨ {Γ} {e}   {ϕ}                             f (⊢-MP ⊢x:ϕ⇒ψ ⊢y:ϕ)
      = let ⊨x:ϕ⇒ψ = ⊢→⊨ f ⊢x:ϕ⇒ψ
            ⊨y:ϕ   = ⊢→⊨ f ⊢y:ϕ
         in ⊨x:ϕ⇒ψ ⊨y:ϕ
  ⊢→⊨ {Γ} {O}     {⊤}                             f ⊢-O     = ⊨O
  ⊢→⊨ {Γ} {K}     {ϕ ⇒ ψ ⇒ ϕ}                     f ⊢-K     = ⊨K ϕ ψ
  ⊢→⊨ {Γ} {S}     {(ϕ ⇒ ψ ⇒ γ) ⇒ (ϕ ⇒ ψ) ⇒ ϕ ⇒ γ} f ⊢-S     = ⊨S ϕ ψ γ
  ⊢→⊨ {Γ} {Pair}  {ϕ ⇒ ψ ⇒ ϕ /\ ψ}                f ⊢-Pair  = ⊨Pair ϕ ψ
  ⊢→⊨ {Γ} {Proj0} {ϕ /\ ψ ⇒ ϕ}                    f ⊢-Proj0 = ⊨Proj0 ϕ ψ
  ⊢→⊨ {Γ} {Proj1} {ϕ /\ ψ ⇒ ψ}                    f ⊢-Proj1 = ⊨Proj1 ϕ ψ

  -- lemma 5: well-typed term under the empty context is strongly normalising.
  ⊢→SN : {e : Term} {ϕ : Formula}
      → [] ⊢ e ~ ϕ
      → SN≻ e
  ⊢→SN {e} {ϕ} ⊢e:ϕ = sem-SN {e} ϕ (⊢→⊨ (λ ()) ⊢e:ϕ)

  -- lemma 6: normalisation is type-preserving and results in an non-neutral term
  ⊢→WN : {e : Term} {ϕ : Formula}
       → [] ⊢ e ~ ϕ
       → Σ (λ e' → [] ⊢ e' ~ ϕ × neutral e' ≡ False)
  ⊢→WN {e} {ϕ} ⊢e:ϕ
    = let SN≻e     = ⊢→SN ⊢e:ϕ
          WN≻e     = SN→WN {T = [] ⊢_~ ϕ}
                           {R = _≻_}
                           {V = λ v → neutral v ≡ False}
                           ≻-preserve (λ {x} → ≻-progress x {ϕ})
                           e ⊢e:ϕ SN≻e
          ⟨ e' , e≻*e'-⊢e':ϕ-¬neu ⟩ = WN≻e
       in ⟨ e' , xyz→yz e≻*e'-⊢e':ϕ-¬neu ⟩
    where
      xyz→yz : {A B C : Set} → A × B × C → B × C
      xyz→yz ⟨ x , ⟨ y , z ⟩ ⟩ = ⟨ y , z ⟩

{-
-- ### Sub Section 2.5 Consistency
-}
module Consistency where
  open ND-minimal using (Equi-Consitency)
  open Hilbert-System using (Minimal⇒Hilbert)
  open Combinatory-Logic using (Term ; O ; S ; K ; 𝕍 ; _·_ ; Pair ; Proj0 ; Proj1 ;
                                headO ; O·-not-typeable ;
                                _⊢_~_ ; ⊢-AX ; ⊢-MP ; ⊢-K ; ⊢-S ;
                                Hilbert⇒SK )
  open Normalisation using (⊢→WN)

  case-with-equation : (b : Bool) → b ≡ True ⊎ b ≡ False
  case-with-equation True = left refl
  case-with-equation False = right refl

  bool-contradiction : {b : Bool} → b ≡ True → b ≡ False → Empty
  bool-contradiction {.True} refl ()

  ⊥-not-inhabitable : {e : Term} → ¬ ([] ⊢ e ~ ⊥)
  ⊥-not-inhabitable ⊢e:⊥ with ⊢→WN ⊢e:⊥
  ... | ⟨ S · e1 , ⟨ ⊢-MP () ⊢e1:A , ¬neutral-e' ⟩ ⟩
  ... | ⟨ K · e1 , ⟨ ⊢-MP () ⊢e1:A , ¬neutral-e' ⟩ ⟩
  ... | ⟨ S · e1 · e2 , ⟨ ⊢-MP (⊢-MP () ⊢e1:A) ⊢e2:B , ¬neutral-e' ⟩ ⟩
  ... | ⟨ O · e1 · e2 , ⟨ ⊢-MP (⊢-MP () ⊢e1:A) ⊢e2:B , ¬neutral-e' ⟩ ⟩
  ... | ⟨ u · e1 · e2 · e3 , ⟨ ⊢-MP (⊢-MP (⊢-MP ⊢u:ABC ⊢e1:A) ⊢e2:B) ⊢e3:C , ¬neutral-e' ⟩ ⟩
    with case-with-equation (headO u)
  ... | left   headO = bool-contradiction headO ¬neutral-e'
  ... | right ¬headO = O·-not-typeable u ¬headO ⊢u:ABC


  nd-consistent : ¬ ([] ⊢m ⊥)
  nd-consistent ⊢m⊥ = let ⊢h⊥           = Minimal⇒Hilbert ⊢m⊥
                          ⟨ e , ⊢e:⊥ ⟩  = Hilbert⇒SK ⊢h⊥
                       in ⊥-not-inhabitable ⊢e:⊥

  ndc-consistent : ¬ ([] ⊢c ⊥)
  ndc-consistent ⊢c⊥ = let ndc→nd        = _⇔_.⇐ Equi-Consitency
                           ⊢m⊥           = ndc→nd ⊢c⊥
                           ⊢h⊥           = Minimal⇒Hilbert ⊢m⊥
                           ⟨ e , ⊢e:⊥ ⟩  = Hilbert⇒SK ⊢h⊥
                        in ⊥-not-inhabitable ⊢e:⊥
