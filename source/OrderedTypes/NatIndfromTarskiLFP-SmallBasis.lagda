Ian Ray. August 27 2026.

TODO. Remove unused imports.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons
open import UF.Size

module OrderedTypes.NatIndfromTarskiLFP-SmallBasis
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : Prop-Ext)
        (pr : Propositional-resizing)
       where

private
 fe' : FunExt
 fe' 𝓤 𝓥 = fe {𝓤} {𝓥}

open import MLTT.Spartan
open import UF.Base
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.Logic
open import UF.Powerset-MultiUniverse
open import UF.Sets
open import UF.Sets-Properties
open import UF.Subsingletons-FunExt
open import UF.Subsingletons-Properties
open import UF.SubtypeClassifier
open import OrderedTypes.SupLattice pt fe
open import OrderedTypes.SupLattice-SmallBasis pt fe
open import OrderedTypes.NatfromTarskiLFP-SmallBasis pt fe pe 
open import OrderedTypes.NatRecfromTarskiLFP-SmallBasis pt fe pe 

open AllCombinators pt fe
open PropositionalTruncation pt hiding (_∨_)
open import Locales.Frame pt fe hiding (⟨_⟩ ; join-of)

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

  recursion-total-space-zero
   : recursion-total-space zero-lfp ＝ (zero-lfp , X-zero)
  recursion-total-space-zero
   = ℕ-recursion-comp-zero-lfp wi lfp (Σ n ꞉ ℕ-lfp , X n)
      (Σ-is-set ℕ-is-set-lfp X-set)
      (zero-lfp , X-zero) (λ (n , Xn) → (suc-lfp n , X-suc n Xn))

  opaque
   unfolding rec-functional-rel
   recusion-total-space-suc
    : (n : ℕ-lfp)
    → (X-n : X n)
    → recursion-total-space (suc-lfp n) ＝ (suc-lfp n , X-suc n X-n)
   recusion-total-space-suc n X-n
    = ℕ-recursion-comp-suc-lfp wi {!lfp!} {!!} {!!} {!!} {!!} {!!}

 ℕ-induction-lfp : (X : ℕ-lfp → 𝓤 ̇)
                 → ((n : ℕ-lfp) → is-set (X n))
                 → X zero-lfp
                 → ((n : ℕ-lfp) → X n → X (suc-lfp n))
                 → (n : ℕ-lfp) → X n
 ℕ-induction-lfp X X-set X-zero X-suc
  = {!!}

\end{code}
