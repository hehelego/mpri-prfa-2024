{-
-- ## Section 2
-- Hilbert systems and combinatory logic
-}

open import common
open import ex1
open ex1.ND-minimal using (⊢-ax ; ⊢-intr ; ⊢-elim) renaming (_⊢_ to _⊢m_)
open ex1.ND-classical using (⊢-ax ; ⊢-intr ; ⊢-elim) renaming (_⊢_ to _⊢c_)

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
    -- using assumption: the identity axiom
    ⊢-AX : {ϕ : Formula} → ϕ ∈ Γ → Γ ⊢ ϕ
    -- modus ponens
    ⊢-MP : {ϕ ψ : Formula} → Γ ⊢ ϕ ⇒ ψ → Γ ⊢ ϕ → Γ ⊢ ψ
    -- the K combinator
    ⊢-K : {ϕ ψ : Formula} → Γ ⊢ ϕ ⇒ ψ ⇒ ϕ
    -- the S combinator
    ⊢-S : {ϕ ψ γ : Formula} → Γ ⊢ (ϕ ⇒ ψ ⇒ γ) ⇒ (ϕ ⇒ ψ) ⇒ ϕ ⇒ γ


  -- b
  Hilbert⇒Minimal : {Γ : Context} {ϕ : Formula} → Γ ⊢ ϕ → Γ ⊢m ϕ
  Hilbert⇒Minimal (⊢-AX x) = ⊢-ax x
  Hilbert⇒Minimal (⊢-MP ϕ⇒ψ ϕ) = let ⊢mϕ⇒ψ = Hilbert⇒Minimal ϕ⇒ψ
                                     ⊢mϕ   = Hilbert⇒Minimal ϕ
                                    in ⊢-elim ⊢mϕ⇒ψ ⊢mϕ
  Hilbert⇒Minimal ⊢-K = let at = ⊢-ax (there (here refl))
                         in ⊢-intr (⊢-intr at)
  Hilbert⇒Minimal ⊢-S = let ϕ     = ⊢-ax               (here refl)
                            ϕ⇒ψ   = ⊢-ax (there        (here refl))
                            ϕ⇒ψ⇒γ = ⊢-ax (there (there (here refl)))
                            ψ     = ⊢-elim ϕ⇒ψ   ϕ
                            ψ⇒γ   = ⊢-elim ϕ⇒ψ⇒γ ϕ
                            γ     = ⊢-elim ψ⇒γ   ψ
                         in ⊢-intr (⊢-intr (⊢-intr γ))


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
  deduction-theorem (⊢-AX (here refl)) = fact3
  deduction-theorem (⊢-AX (there x)) = fact1 (⊢-AX x)
  deduction-theorem (⊢-MP ϕ⊢γ⇒ψ ϕ⊢γ) = let ϕγψ = deduction-theorem ϕ⊢γ⇒ψ
                                           ϕγ  = deduction-theorem ϕ⊢γ
                                           ϕψ  = fact2 ϕγψ ϕγ
                                        in ϕψ
  deduction-theorem ⊢-K = fact1 ⊢-K
  deduction-theorem ⊢-S = fact1 ⊢-S

  -- e
  Minimal⇒Hilbert : {Γ : Context} {ϕ : Formula} → Γ ⊢m ϕ → Γ ⊢ ϕ
  Minimal⇒Hilbert (⊢-ax x) = ⊢-AX x
  Minimal⇒Hilbert (⊢-intr ⊢ϕ) = deduction-theorem (Minimal⇒Hilbert ⊢ϕ)
  Minimal⇒Hilbert (⊢-elim ⊢ϕ⇒ψ ⊢ϕ) = let ϕψ = Minimal⇒Hilbert ⊢ϕ⇒ψ
                                         ϕ  = Minimal⇒Hilbert ⊢ϕ
                                      in ⊢-MP ϕψ ϕ

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
  open Hilbert-System using (⊢-AX ; ⊢-MP ; ⊢-K ; ⊢-S) renaming (_⊢_ to _⊢'_)
  open ARS using (SN[_] ; SN ; Closure[_] ; refl ; step ; transit)

  infixl 15 _·_
  data Term : Set where
    S : Term
    K : Term
    𝕍 : ℕ → Term
    _·_ : Term → Term → Term

  -- a
  data _⊢_~_ (Γ : Context) : Term → Formula → Set where
    ⊢-AX : {n : ℕ} {ϕ : Formula} → Γ ! n ≔ ϕ → Γ ⊢ 𝕍 n ~ ϕ
    ⊢-MP : {u v : Term} {ϕ ψ : Formula} → Γ ⊢ u ~ ϕ ⇒ ψ → Γ ⊢ v ~ ϕ → Γ ⊢ u · v ~ ψ
    ⊢-K : {ϕ ψ : Formula} → Γ ⊢ K ~ ϕ ⇒ ψ ⇒ ϕ
    ⊢-S : {ϕ ψ γ : Formula} → Γ ⊢ S ~ (ϕ ⇒ ψ ⇒ γ) ⇒ (ϕ ⇒ ψ) ⇒ ϕ ⇒ γ

  variable
    Γ : Context


  Hilbert⇒SK : {ϕ : Formula} → Γ ⊢' ϕ → Σ (λ e → Γ ⊢ e ~ ϕ)
  Hilbert⇒SK (⊢-AX ϕ∈Γ) = let ⟨ n , at-n ⟩ = mem→idx ϕ∈Γ
                           in ⟨ 𝕍 n , ⊢-AX at-n ⟩
  Hilbert⇒SK (⊢-MP ⊢'ϕ⇒ψ ⊢'ϕ) = let ⟨ u , ⊢ϕ⇒ψ ⟩ = Hilbert⇒SK ⊢'ϕ⇒ψ
                                    ⟨ v , ⊢ϕ   ⟩ = Hilbert⇒SK ⊢'ϕ
                                 in ⟨ u · v , ⊢-MP ⊢ϕ⇒ψ ⊢ϕ ⟩
  Hilbert⇒SK ⊢-K = ⟨ K , ⊢-K ⟩
  Hilbert⇒SK ⊢-S = ⟨ S , ⊢-S ⟩

  SK⇒Hilbert : {ϕ : Formula} → Σ (λ e → Γ ⊢ e ~ ϕ) → Γ ⊢' ϕ
  SK⇒Hilbert ⟨ 𝕍 n , ⊢-AX at-n ⟩ = let ϕ∈Γ = idx→mem ⟨ n , at-n ⟩
                                    in ⊢-AX ϕ∈Γ
  SK⇒Hilbert ⟨ u · v , ⊢-MP u:ϕ⇒ψ v:ϕ ⟩ = let ⊢ϕ⇒ψ = SK⇒Hilbert ⟨ u , u:ϕ⇒ψ ⟩
                                              ⊢ϕ   = SK⇒Hilbert ⟨ v , v:ϕ   ⟩
                                           in ⊢-MP ⊢ϕ⇒ψ ⊢ϕ
  SK⇒Hilbert ⟨ K , ⊢-K ⟩ = ⊢-K
  SK⇒Hilbert ⟨ S , ⊢-S ⟩ = ⊢-S

  -- b
  Hilbert⇔SK : {ϕ : Formula} → (Σ (λ e → Γ ⊢ e ~ ϕ)) ⇔ (Γ ⊢' ϕ)
  Hilbert⇔SK = record { ⇒ = SK⇒Hilbert ; ⇐ = Hilbert⇒SK }

  -- c
  infix 10 _≻_
  data _≻_ : Term → Term → Set where
    ≻K  : {x y : Term}    → K · x · y      ≻ x
    ≻S  : {f g x : Term}  → S · f · g · x  ≻ f · x · (g · x)
    ≻·l : {x x' y : Term} → x ≻ x' → x · y ≻ x' · y
    ≻·r : {x y y' : Term} → y ≻ y' → x · y ≻ x  · y'

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

  -- e
  ≻*·l : {x x' y : Term} → x ≻* x' → x · y ≻* x' · y
  ≻*·l refl = refl
  ≻*·l (step x≻x') = step (≻·l x≻x')
  ≻*·l (transit x≻*z z≻*x') = let xy≻*zy = ≻*·l x≻*z
                                  zy≻*x'y = ≻*·l z≻*x'
                               in transit xy≻*zy zy≻*x'y

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
  SN·lemma S v sn = SN λ ()
  SN·lemma K v sn = SN λ ()
  SN·lemma (𝕍 n) v sn = SN λ ()
  SN·lemma (u · v) w (SN ≻→SN) = SN g
    where g : {e : Term} → u · v ≻ e → SN[ _≻_ ] e
          g {e} ≻K = let Kevw≻ew = ≻·l ≻K
                         sn = ≻→SN Kevw≻ew
                      in SN·lemma e w sn
          g {e} ≻S = let Sfgxy≻fx[gx]y = ≻·l ≻S
                         sn = ≻→SN Sfgxy≻fx[gx]y
                      in SN·lemma e w sn
          g {e} (≻·l u≻u') = let uvw≻u'vw = ≻·l (≻·l u≻u')
                                 sn = ≻→SN uvw≻u'vw
                              in SN·lemma e w sn
          g {e} (≻·r v≻v') = let uvw≻uv'w = ≻·l (≻·r v≻v')
                                 sn = ≻→SN uvw≻uv'w
                              in SN·lemma e w sn

  -- h
  neutral : Term → 𝔹
  neutral K = False
  neutral (K · e) = False
  neutral S = False
  neutral (S · e) = False
  neutral (S · e · e') = False
  neutral e = True

  neutral· : (u v : Term) → neutral u ≡ True → neutral (u · v) ≡ True
  neutral· (𝕍 n) v refl = refl
  neutral· (𝕍 n · t) v refl = refl
  neutral· (K · y · z) v refl = refl
  neutral· (𝕍 n · y · z) v refl = refl
  neutral· (x · y · z · w) v refl = refl


  -- i
  ≻-progress : (e : Term) {ϕ : Formula}
             → [] ⊢ e ~ ϕ → Σ (e ≻_) ⊎ neutral e ≡ False
  ≻-progress S S:ϕ = right refl
  ≻-progress K K:ϕ = right refl
  ≻-progress (𝕍 n) (⊢-AX ())
  ≻-progress (u · v) (⊢-MP u:ϕ⇒ψ v:ϕ)
    with ≻-progress u u:ϕ⇒ψ
  ... | left ⟨ u' , u≻u' ⟩ = left ⟨ u' · v , ≻·l u≻u' ⟩
  ... | right ¬neu-u
    with ≻-progress v v:ϕ
  ... | left ⟨ v' , v≻v' ⟩ = left ⟨ u · v' , ≻·r v≻v' ⟩
  ... | right ¬neu-v = lemma u v ¬neu-u ¬neu-v
    where
      lemma : (u v : Term) → neutral u ≡ False → neutral v ≡ False
            → Σ ((u · v) ≻_) ⊎ neutral (u · v) ≡ False
      lemma S v nu nv = right refl
      lemma K v nu nv = right refl
      lemma (K · u) v nu nv = left ⟨ u , ≻K ⟩
      lemma (S · v) x nuv nv = right refl
      lemma (S · f · g) x nuv nv = left ⟨ f · x · (g · x) , ≻S ⟩

{-
-- ### Sub Section 2.4 Normalisation
-}
module Normalisation where
  open ARS using (SN[_] ; SN ; SN→WN ;
                  Closure[_] ; refl ; step ; transit ;
                  SN-on-Closure ; SN-double-ind)
  open Combinatory-Logic using (Term ; S ; K ; 𝕍 ; _·_ ; _≻_ ; ≻K ; ≻S ; ≻·l ; ≻·r ;
                                _≻*_ ; ≻*·l ;
                                _⊢_~_ ; ⊢-AX ; ⊢-MP ; ⊢-K ; ⊢-S ;
                                neutral ; neutral· ;
                                ≻-preserve ; ≻-progress ;
                                SN·lemma)


  SN≻ : Term → Set
  SN≻ = SN[ _≻_ ]

  infix 3 ⊨_~_
  ⊨_~_ : Term → Formula → Set
  ⊨ e ~ ⊥     = SN≻ e
  ⊨ e ~ var n = SN≻ e
  ⊨ e ~ ϕ ⇒ ψ = {x : Term} → ⊨ x ~ ϕ → ⊨ e · x ~ ψ

  -- theorem 1.1
  sem-SN : {e : Term} (ϕ : Formula)
      → ⊨ e ~ ϕ
      → SN≻ e
  -- theorem 1.2
  sem-preserve : {e : Term} (ϕ : Formula)
            → ⊨ e ~ ϕ
            → ({e' : Term} → e ≻* e' → ⊨ e' ~ ϕ)
  -- theorem 1.3
  sem-neutral : {e : Term} (ϕ : Formula) (neu-e : neutral e ≡ True)
           → ({e' : Term} → e ≻ e' → ⊨ e' ~ ϕ)
           → ⊨ e ~ ϕ

  -- corollary of theorem 1.3: a variable term is always semantically well-typed
  -- because it is neutral and cannot be further reduced.
  ⊨𝕍n:ϕ : {n : ℕ} (ϕ : Formula) → ⊨ 𝕍 n ~ ϕ
  ⊨𝕍n:ϕ ϕ = sem-neutral ϕ refl λ { () }

  -- proof of theorem 1.1
  sem-SN     ⊥       sem = sem
  sem-SN     (var x) sem = sem
  sem-SN {e} (ϕ ⇒ ψ) ⊨e:ϕ⇒ψ = 
    let v        = 𝕍 Z
        ⊨v:ϕ     = ⊨𝕍n:ϕ ϕ
        ⊨e·v:ψ   = ⊨e:ϕ⇒ψ ⊨v:ϕ
        SN≻e·v   = sem-SN {e · v} ψ ⊨e·v:ψ
        SN≻e     = SN·lemma e v SN≻e·v
     in SN≻e


  -- proof of theorem 1.2
  sem-preserve     ⊥       sem e≻*e' = SN-on-Closure sem e≻*e'
  sem-preserve     (var x) sem e≻*e' = SN-on-Closure sem e≻*e'
  sem-preserve {e} (ϕ ⇒ ψ) ⊨e:ϕ⇒ψ {e'} e≻*e' = ⊨e':ϕ⇒ψ
    where
      ⊨e':ϕ⇒ψ : ⊨ e' ~ ϕ ⇒ ψ
      ⊨e':ϕ⇒ψ {x} ⊨x:ϕ = let ⊨e·x:ψ    = ⊨e:ϕ⇒ψ ⊨x:ϕ
                             e·x≻*e'·x = ≻*·l e≻*e'
                          in sem-preserve {e · x} ψ ⊨e·x:ψ {e' · x} e·x≻*e'·x

  -- proof of theorem 1.3
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
  ⊢→⊨ {Γ} {K}   {ϕ ⇒ ψ ⇒ ϕ}                     f ⊢-K = ⊨K ϕ ψ
  ⊢→⊨ {Γ} {S}   {(ϕ ⇒ ψ ⇒ γ) ⇒ (ϕ ⇒ ψ) ⇒ ϕ ⇒ γ} f ⊢-S = ⊨S ϕ ψ γ

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
  open Combinatory-Logic using (Term ; S ; K ; 𝕍 ; _·_ ;
                                _⊢_~_ ; ⊢-AX ; ⊢-MP ; ⊢-K ; ⊢-S ;
                                Hilbert⇒SK )
  open Normalisation using (⊢→WN)

  ⊥-not-inhabitable : {e : Term} → ¬ ([] ⊢ e ~ ⊥)
  ⊥-not-inhabitable ⊢e:⊥ with ⊢→WN ⊢e:⊥
  ... | ⟨ S · e1 , ⟨ ⊢-MP () ⊢e1:A , ¬neutral-e' ⟩ ⟩
  ... | ⟨ K · e1 , ⟨ ⊢-MP () ⊢e1:A , ¬neutral-e' ⟩ ⟩
  ... | ⟨ S · e1 · e2 , ⟨ ⊢-MP (⊢-MP () ⊢e1:A) ⊢e2:B , ¬neutral-e' ⟩ ⟩

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
