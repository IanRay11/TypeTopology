Ian Ray. August 27 2026.

We derive induction for ℕ-lfp from recursion in the standard way.

TODO: Carlo suggests first proving that the recursor is unique, and using this
to derive induction more straightforwardly (?)

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
 open nat-rec-lfp wi lfp

 module _ (X : ℕ-lfp → 𝓤 ̇) (X-set : (n : ℕ-lfp) → is-set (X n))
          (X-zero : X zero-lfp) (X-suc : (n : ℕ-lfp) → X n → X (suc-lfp n))
        where

  recursion-total-space : ℕ-lfp → Σ n ꞉ ℕ-lfp , X n
  recursion-total-space 
   = ℕ-recursion-lfp (Σ n ꞉ ℕ-lfp , X n) (Σ-is-set ℕ-is-set-lfp X-set)
      (zero-lfp , X-zero) (λ (n , Xn) → (suc-lfp n , X-suc n Xn))

  id-ℕ-lfp? : ℕ-lfp → ℕ-lfp
  id-ℕ-lfp? = pr₁ ∘ recursion-total-space

  X-id-ℕ-lfp? : (n : ℕ-lfp)
              → X (id-ℕ-lfp? n)
  X-id-ℕ-lfp? n = pr₂ (recursion-total-space n)

  recursion-total-space-zero
   : recursion-total-space zero-lfp ＝ (zero-lfp , X-zero)
  recursion-total-space-zero
   = ℕ-recursion-comp-zero-lfp (Σ n ꞉ ℕ-lfp , X n)
      (Σ-is-set ℕ-is-set-lfp X-set)
      (zero-lfp , X-zero) (λ (n , Xn) → (suc-lfp n , X-suc n Xn))

  id-ℕ-lfp?-zero : id-ℕ-lfp? zero-lfp ＝ zero-lfp
  id-ℕ-lfp?-zero = ap pr₁ recursion-total-space-zero

  recursion-total-space-suc
   : (n : ℕ-lfp)
   → recursion-total-space (suc-lfp n)
   ＝ (suc-lfp (id-ℕ-lfp? n) , X-suc (id-ℕ-lfp? n) (X-id-ℕ-lfp? n))
  recursion-total-space-suc n
   = ℕ-recursion-comp-suc-lfp (Σ n ꞉ ℕ-lfp , X n)
      (Σ-is-set ℕ-is-set-lfp X-set)
      (zero-lfp , X-zero) (λ (n , Xn) → (suc-lfp n , X-suc n Xn)) n

  id-ℕ-lfp?-suc : (n : ℕ-lfp)
                → id-ℕ-lfp? (suc-lfp n) ＝ suc-lfp (id-ℕ-lfp? n)
  id-ℕ-lfp?-suc n = pr₁ (from-Σ-＝ (recursion-total-space-suc n))

  id-ℕ-lfp : (n : ℕ-lfp) → id-ℕ-lfp? n ＝ n
  id-ℕ-lfp 
   = ℕ-recursion-uniqueness'-lfp ℕ-lfp ℕ-is-set-lfp zero-lfp suc-lfp
      id-ℕ-lfp? id id-ℕ-lfp?-zero refl id-ℕ-lfp?-suc ∼-refl 

  transport-X-suc-lfp
   : (n : ℕ-lfp)
   → transport X (id-ℕ-lfp?-suc n) (X-id-ℕ-lfp? (suc-lfp n))
   ＝ X-suc (id-ℕ-lfp? n) (X-id-ℕ-lfp? n)
  transport-X-suc-lfp n = pr₂ (from-Σ-＝ (recursion-total-space-suc n))

\end{code}

We can now give the induction principle and computations rules for ℕ-lfp.

\begin{code}

 ℕ-induction-lfp : (X : ℕ-lfp → 𝓤 ̇)
                 → ((n : ℕ-lfp) → is-set (X n))
                 → X zero-lfp
                 → ((n : ℕ-lfp) → X n → X (suc-lfp n))
                 → (n : ℕ-lfp) → X n
 ℕ-induction-lfp X X-set X-zero X-suc n
  = transport X (id-ℕ-lfp X X-set X-zero X-suc n)
     (X-id-ℕ-lfp? X X-set X-zero X-suc n)

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
   I = id-ℕ-lfp X X-set X-zero X-suc zero-lfp
   II = X-id-ℕ-lfp? X X-set X-zero X-suc zero-lfp
   III = pr₁ (from-Σ-＝ (recursion-total-space-zero X X-set X-zero X-suc))
   IV : I ＝ III
   IV = ℕ-is-set-lfp _ _
   V = ap (λ - → transport X - (X-id-ℕ-lfp? X X-set X-zero X-suc zero-lfp)) IV     
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
   I = id-ℕ-lfp X X-set X-zero X-suc
   II = id-ℕ-lfp?-suc X X-set X-zero X-suc n
   III = id-ℕ-lfp? X X-set X-zero X-suc
   IV = X-id-ℕ-lfp? X X-set X-zero X-suc
   V = ap (λ - → transport X - (IV (suc-lfp n)))
          (ℕ-is-set-lfp (I (suc-lfp n)) (II ∙ ap suc-lfp (I n)))
   VI = transport-∙ X II (ap suc-lfp (I n))
   VII = ap (transport X (ap suc-lfp (I n)))
          (transport-X-suc-lfp X X-set X-zero X-suc n)
   VIII = transport-ap X suc-lfp (I n) ⁻¹
   IX = nat-transport X-suc (I n) ⁻¹ 

\end{code}
