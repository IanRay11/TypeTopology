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

(zero-lfp , X-zero)
        (λ (n , Xn) → (suc-lfp n , X-suc n Xn))

We give the usual construction of induction from recursion.

\begin{code}

module _ (wi : weak-infinity 𝓤) (lfp : TarskiLFP-SmallBasis (𝓤 ⁺) 𝓤 𝓤) where

 open weak-infinity wi
 open nat-weak-inf-tarski wi lfp

 module recursion-total
          (X : ℕ-lfp → 𝓤 ̇) (X-set : (n : ℕ-lfp) → is-set (X n))
          (X-zero : X zero-lfp) (X-suc : (n : ℕ-lfp) → X n → X (suc-lfp n))
        where

  open nat-rec-lfp wi lfp (Σ n ꞉ ℕ-lfp , X n)
        (Σ-is-set ℕ-is-set-lfp X-set)
        

  recursion-total-space : ℕ-lfp → Σ n ꞉ ℕ-lfp , X n
  recursion-total-space 
   = ℕ-recursion-lfp (zero-lfp , X-zero) (λ (n , Xn) → (suc-lfp n , X-suc n Xn))

  pr₁-rec : ℕ-lfp → ℕ-lfp
  pr₁-rec = pr₁ ∘ recursion-total-space

  X-pr₁-rec : (n : ℕ-lfp)
            → X (pr₁-rec n)
  X-pr₁-rec n = pr₂ (recursion-total-space n)

  pr₁-rec-zero : pr₁-rec zero-lfp ＝ zero-lfp
  pr₁-rec-zero
   = ap pr₁ (ℕ-recursion-comp-zero-lfp (zero-lfp , X-zero)
              (λ (n , Xn) → (suc-lfp n , X-suc n Xn)))
  
  pr₁-rec-suc : (n : ℕ-lfp)
              → pr₁-rec (suc-lfp n) ＝ suc-lfp (pr₁-rec n)
  pr₁-rec-suc n
   = pr₁ (from-Σ-＝ (ℕ-recursion-comp-suc-lfp (zero-lfp , X-zero)
                      (λ (n , Xn) → (suc-lfp n , X-suc n Xn)) n))

  transport-X-suc-lfp
   : (n : ℕ-lfp)
   → transport X (pr₁-rec-suc n) (X-pr₁-rec (suc-lfp n))
   ＝ X-suc (pr₁-rec n) (X-pr₁-rec n)
  transport-X-suc-lfp n
   = pr₂ (from-Σ-＝ (ℕ-recursion-comp-suc-lfp (zero-lfp , X-zero)
                      (λ (n , Xn) → (suc-lfp n , X-suc n Xn)) n))

 module pr₁-rec-is-id-from-uniqueness
          (X : ℕ-lfp → 𝓤 ̇) (X-set : (n : ℕ-lfp) → is-set (X n))
          (X-zero : X zero-lfp) (X-suc : (n : ℕ-lfp) → X n → X (suc-lfp n))
        where

  open nat-rec-lfp wi lfp ℕ-lfp ℕ-is-set-lfp 
  open recursion-total X X-set X-zero X-suc

  pr₁-rec-id : (n : ℕ-lfp) → pr₁-rec n ＝ n
  pr₁-rec-id = ℕ-recursion-uniqueness'-lfp pr₁-rec id pr₁-rec-zero
                (λ n IH → pr₁-rec-suc n ∙ ap suc-lfp IH)

\end{code}

We can now give the induction principle and computations rules for ℕ-lfp.

\begin{code}

 module _ (X : ℕ-lfp → 𝓤 ̇) (X-set : (n : ℕ-lfp) → is-set (X n))
          (X-zero : X zero-lfp) (X-suc : (n : ℕ-lfp) → X n → X (suc-lfp n))
        where

  open nat-rec-lfp wi lfp (Σ n ꞉ ℕ-lfp , X n)
        (Σ-is-set ℕ-is-set-lfp X-set)
        
  open recursion-total X X-set X-zero X-suc
  open pr₁-rec-is-id-from-uniqueness X X-set X-zero X-suc

  ℕ-induction-lfp : (n : ℕ-lfp) → X n
  ℕ-induction-lfp n
   = transport X (pr₁-rec-id n) (X-pr₁-rec n)

  ℕ-induction-comp-zero-lfp
   : ℕ-induction-lfp zero-lfp ＝ X-zero
  ℕ-induction-comp-zero-lfp 
   = ℕ-induction-lfp zero-lfp                                  ＝⟨refl⟩
     transport X (pr₁-rec-id zero-lfp) (X-pr₁-rec zero-lfp)    ＝⟨ II ⟩
     transport X (pr₁ (from-Σ-＝ I)) (X-pr₁-rec zero-lfp)      ＝⟨ III ⟩
     X-zero                                                    ∎
   where
    I = ℕ-recursion-comp-zero-lfp (zero-lfp , X-zero)
         (λ (n , Xn) → (suc-lfp n , X-suc n Xn))
    II = ap (λ - → transport X - (X-pr₁-rec zero-lfp))
            (ℕ-is-set-lfp (pr₁-rec-id zero-lfp)
                          (pr₁ (from-Σ-＝ I)))
    III = pr₂ (from-Σ-＝ I)

  ℕ-induction-comp-suc-lfp
   : (n : ℕ-lfp)
   → ℕ-induction-lfp (suc-lfp n) ＝ X-suc n (ℕ-induction-lfp n)
  ℕ-induction-comp-suc-lfp n
   = ℕ-induction-lfp (suc-lfp n)                                      ＝⟨refl⟩
     transport X (pr₁-rec-id (suc-lfp n)) (X-pr₁-rec (suc-lfp n))     ＝⟨ I ⟩
     transport X (pr₁-rec-suc n ∙ ap suc-lfp (pr₁-rec-id n))
               (X-pr₁-rec (suc-lfp n))                                ＝⟨ II ⟩
     transport X (ap suc-lfp (pr₁-rec-id n))
               (transport X (pr₁-rec-suc n) (X-pr₁-rec (suc-lfp n)))  ＝⟨ III ⟩
     transport X (ap suc-lfp (pr₁-rec-id n))
               (X-suc (pr₁-rec n) (X-pr₁-rec n))                      ＝⟨ IV ⟩
     transport (X ∘ suc-lfp) (pr₁-rec-id n)
               (X-suc (pr₁-rec n) (X-pr₁-rec n))                      ＝⟨ V ⟩
     X-suc n (transport X (pr₁-rec-id n) (X-pr₁-rec n))               ∎
   where
    I = ap (λ - → transport X - (X-pr₁-rec (suc-lfp n)))
           (ℕ-is-set-lfp (pr₁-rec-id (suc-lfp n))
           (pr₁-rec-suc n ∙ ap suc-lfp (pr₁-rec-id n)))
    II = transport-∙ X (pr₁-rec-suc n) (ap suc-lfp (pr₁-rec-id n))
    III = ap (transport X (ap suc-lfp (pr₁-rec-id n)))
             (transport-X-suc-lfp n)
    IV = transport-ap X suc-lfp (pr₁-rec-id n) ⁻¹
    V = nat-transport X-suc (pr₁-rec-id n) ⁻¹ 

\end{code}
