\begin{code}

{-# OPTIONS --safe --without-K #-}

module DURGs.Examples where

open import MLTT.Spartan
open import UF.Equiv
open import DURGs.BasicConstructionsonReflexiveGraphs
open import DURGs.ClosurePropertiesofUnivalentReflexiveGraphs
open import DURGs.DisplayedReflexiveGraphs
open import DURGs.DisplayedUnivalentReflexiveGraphs
open import DURGs.ReflexiveGraphs
open import DURGs.UnivalentReflexiveGraphs

\end{code}

The identity type of binary products can be characterized using the closure
property univalent reflexive graphs under products. 

\begin{code}

product-characterization-from-univalent-graphs
 : {A : 𝓤 ̇} {B : 𝓥 ̇} {a a' : A} {b b' : B}
 → ((a , b) ＝ (a' , b')) ≃ (a ＝ a') × (b ＝ b')
product-characterization-from-univalent-graphs {_} {_} {A} {B} {a} {a'} {b} {b'}
 = (id-to-edge' ((Δ A) ⊗ (Δ B)) , II (a , b) (a' , b'))
 where
  I : is-univalent-refl-graph ((Δ A) ⊗ (Δ B))
  I = univalence-closed-under-binary-product (Δ A) (Δ B)
       (discrete-refl-graph-is-univalent A) (discrete-refl-graph-is-univalent B)
  II : (p q : A × B) → is-equiv (id-to-edge' ((Δ A) ⊗ (Δ B)) {p} {q})
  II = prop-fans-implies-id-to-edge-equiv I

\end{code}
