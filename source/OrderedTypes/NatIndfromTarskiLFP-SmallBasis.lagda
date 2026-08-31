Ian Ray. August 27 2026.

We derive induction for ℕ-lfp from recursion in the standard way.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons

module OrderedTypes.NatIndfromTarskiLFP-SmallBasis
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : Prop-Ext)
       where

private
 fe' : FunExt
 fe' 𝓤 𝓥 = fe {𝓤} {𝓥}

open import MLTT.Spartan
open import UF.Base
open import UF.Subsingletons-FunExt
open import UF.Sets
open import UF.Sets-Properties
open import OrderedTypes.NatfromTarskiLFP-SmallBasis pt fe pe 
open import OrderedTypes.NatRecfromTarskiLFP-SmallBasis pt fe pe 

\end{code}

We give the usual construction of induction from recursion.

\begin{code}

module _ (wi : weak-infinity 𝓤) (lfp : TarskiLFP-SmallBasis (𝓤 ⁺) 𝓤 𝓤) where

 open weak-infinity wi
 open nat-weak-inf-tarski wi lfp
 open nat-rec-weak-inf-tarsk wi lfp

 module _ (X : ℕ-lfp → 𝓤 ̇) (X-set : (n : ℕ-lfp) → is-set (X n))
          (X-zero : X zero-lfp) (X-suc : (n : ℕ-lfp) → X n → X (suc-lfp n))
        where

  recursion-total-space : ℕ-lfp → Σ n ꞉ ℕ-lfp , X n
  recursion-total-space 
   = ℕ-recursion-lfp wi lfp (Σ n ꞉ ℕ-lfp , X n) (Σ-is-set ℕ-is-set-lfp X-set)
      (zero-lfp , X-zero) (λ (n , Xn) → (suc-lfp n , X-suc n Xn))

  ℕ-tot : (n : ℕ-lfp)
        → ℕ-lfp
  ℕ-tot n = pr₁ (recursion-total-space n)

  X-tot : (n : ℕ-lfp)
        → X (ℕ-tot n)
  X-tot n = pr₂ (recursion-total-space n)

  recursion-total-space-zero
   : recursion-total-space zero-lfp ＝ (zero-lfp , X-zero)
  recursion-total-space-zero
   = ℕ-recursion-comp-zero-lfp wi lfp (Σ n ꞉ ℕ-lfp , X n)
      (Σ-is-set ℕ-is-set-lfp X-set)
      (zero-lfp , X-zero) (λ (n , Xn) → (suc-lfp n , X-suc n Xn))

  recursion-total-space-suc
   : (n : ℕ-lfp)
   → recursion-total-space (suc-lfp n)
   ＝ (suc-lfp (ℕ-tot n) , X-suc (ℕ-tot n) (X-tot n))
  recursion-total-space-suc n
   = ℕ-recursion-comp-suc-lfp wi lfp (Σ n ꞉ ℕ-lfp , X n)
      (Σ-is-set ℕ-is-set-lfp X-set)
      (zero-lfp , X-zero) (λ (n , Xn) → (suc-lfp n , X-suc n Xn)) n

  ℕ-tot-suc-lfp : (n : ℕ-lfp)
                → ℕ-tot (suc-lfp n) ＝ suc-lfp (ℕ-tot n)
  ℕ-tot-suc-lfp n = pr₁ (from-Σ-＝ (recursion-total-space-suc n))

  transport-X-suc-lfp
   : (n : ℕ-lfp)
   → transport X (ℕ-tot-suc-lfp n) (X-tot (suc-lfp n))
   ＝ X-suc (ℕ-tot n) (X-tot n)
  transport-X-suc-lfp n = pr₂ (from-Σ-＝ (recursion-total-space-suc n))

  inductive-step-pr₁＝id
   : (n : ℕ-lfp)
   → ℕ-tot n ＝ n
   → ℕ-tot (suc-lfp n) ＝ suc-lfp n 
  inductive-step-pr₁＝id n pr₁recn＝n
   = ap pr₁ (recursion-total-space-suc n) ∙ ap suc-lfp pr₁recn＝n

  pr₁-rec-tot＝id : (n : ℕ-lfp)
                  → ℕ-tot n ＝ n
  pr₁-rec-tot＝id
   = ℕ-prop-induction-lfp
      (λ - → (pr₁ (recursion-total-space -) ＝ -) , ℕ-is-set-lfp)
      (ap pr₁ recursion-total-space-zero) inductive-step-pr₁＝id

\end{code}

We can now give the induction principle and computations rules for ℕ-lfp.

\begin{code}

 ℕ-induction-lfp : (X : ℕ-lfp → 𝓤 ̇)
                 → ((n : ℕ-lfp) → is-set (X n))
                 → X zero-lfp
                 → ((n : ℕ-lfp) → X n → X (suc-lfp n))
                 → (n : ℕ-lfp) → X n
 ℕ-induction-lfp X X-set X-zero X-suc n
  = transport X (pr₁-rec-tot＝id X X-set X-zero X-suc n)
     (X-tot X X-set X-zero X-suc n)

 ℕ-induction-comp-zero-lfp
  : (X : ℕ-lfp → 𝓤 ̇)
  → (X-set : (n : ℕ-lfp) → is-set (X n))
  → (X-zero : X zero-lfp)
  → (X-suc : (n : ℕ-lfp) → X n → X (suc-lfp n))
  → ℕ-induction-lfp X X-set X-zero X-suc zero-lfp ＝ X-zero
 ℕ-induction-comp-zero-lfp X X-set X-zero X-suc
  = ℕ-induction-lfp X X-set X-zero X-suc zero-lfp   ＝⟨refl⟩
    transport X I II                                ＝⟨ V ⟩
    transport X III II                              ＝⟨ VI ⟩
    X-zero                                          ∎
  where
   I = pr₁-rec-tot＝id X X-set X-zero X-suc zero-lfp
   II = X-tot X X-set X-zero X-suc zero-lfp
   III = pr₁ (from-Σ-＝ (recursion-total-space-zero X X-set X-zero X-suc))
   IV : I ＝ III
   IV = ℕ-is-set-lfp _ _
   V = ap (λ - → transport X - (X-tot X X-set X-zero X-suc zero-lfp)) IV     
   VI = pr₂ (from-Σ-＝ (recursion-total-space-zero X X-set X-zero X-suc))

 ℕ-induction-comp-suc-lfp
  : (X : ℕ-lfp → 𝓤 ̇)
  → (X-set : (n : ℕ-lfp) → is-set (X n))
  → (X-zero : X zero-lfp)
  → (X-suc : (n : ℕ-lfp) → X n → X (suc-lfp n))
  → (n : ℕ-lfp)
  → ℕ-induction-lfp X X-set X-zero X-suc (suc-lfp n)
  ＝ X-suc n (ℕ-induction-lfp X X-set X-zero X-suc n)
 ℕ-induction-comp-suc-lfp X X-set X-zero X-suc n
  = ℕ-induction-lfp X X-set X-zero X-suc (suc-lfp n)                 ＝⟨refl⟩
    transport X (I (suc-lfp n)) (IV (suc-lfp n))                     ＝⟨ V ⟩
    transport X (II ∙ ap suc-lfp (I n)) (IV (suc-lfp n))             ＝⟨ VI ⟩
    transport X (ap suc-lfp (I n)) (transport X II (IV (suc-lfp n))) ＝⟨ VII ⟩
    transport X (ap suc-lfp (I n)) (X-suc (III n) (IV n))            ＝⟨ VIII ⟩
    transport (X ∘ suc-lfp) (I n) (X-suc (III n) (IV n))             ＝⟨ IX ⟩
    X-suc n (transport X (I n) (IV n))                               ∎
  where
   I = pr₁-rec-tot＝id X X-set X-zero X-suc
   II = ℕ-tot-suc-lfp X X-set X-zero X-suc n
   III = ℕ-tot X X-set X-zero X-suc
   IV = X-tot X X-set X-zero X-suc
   V = ap (λ - → transport X - (IV (suc-lfp n)))
          (ℕ-is-set-lfp (I (suc-lfp n)) (II ∙ ap suc-lfp (I n)))
   VI = transport-∙ X II (ap suc-lfp (I n))
   VII = ap (transport X (ap suc-lfp (I n)))
          (transport-X-suc-lfp X X-set X-zero X-suc n)
   VIII = transport-ap X suc-lfp (I n) ⁻¹
   IX = nat-transport X-suc (I n) ⁻¹ 

\end{code}
