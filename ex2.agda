{-
-- ## Section 2
-- Hilbert systems and combinatory logic
-}

open import common
open import ex1
open ex1.ND-minimal using (⊢-ax ; ⊢-intr ; ⊢-elim) renaming (_⊢_ to _⊢m_)

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


module ARS where
  variable
    A : Set
    R : A → A → Set
