Ian Ray. 1st March 2026.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module DURGs.RepresentationIndependenceWhiteboard where

open import MLTT.Spartan hiding (_⁻¹)
open import DURGs.BivariantMidpointLenses
open import DURGs.ReflexiveGraphConstructions
open import DURGs.UnivalentReflexiveGraphClosureProperties
open import DURGs.DisplayedReflexiveGraphs
open import DURGs.DisplayedUnivalentReflexiveGraphs
open import DURGs.Lenses
open import DURGs.ReflexiveGraphs
open import DURGs.UnivalentFamilies
open import DURGs.UnivalentReflexiveGraphs
open import DURGs.UnivalenceProperty
open import UF.PropTrunc
open import UF.Subsingletons
open import UF.SubtypeClassifier

\end{code}

We investigate quasi-relations.

\begin{code}

module _ (pt : propositional-truncations-exist)
        where

 inv-rel : {X : 𝓤 ̇} {Y : 𝓥 ̇} (R : X → Y → 𝓣 ̇) 
         → Y → X → 𝓣 ̇
 inv-rel R y x = R x y

 syntax inv-rel R = R ⁻¹

 comp-rel : {X : 𝓤 ̇} {Y : 𝓥 ̇} {Z : 𝓦 ̇} (R : X → Y → 𝓣 ̇) (Q : Y → Z → 𝓣' ̇)
          → X → Z → 𝓥 ⊔ 𝓣 ⊔ 𝓣' ̇
 comp-rel {_} {_} {_} {_} {_} {_} {Y} R Q x z = Σ y ꞉ Y , R x y × Q y z

 syntax comp-rel R Q = Q · R

 for-rel : {X : 𝓤 ̇} {Y : 𝓥 ̇} (R : X → Y → 𝓣 ̇)
             → X → X → 𝓥 ⊔ 𝓣 ̇
 for-rel R = (R ⁻¹) · R

 back-rel : {X : 𝓤 ̇} {Y : 𝓥 ̇} (R : X → Y → 𝓣 ̇)
              → Y → Y → 𝓤 ⊔ 𝓣 ̇
 back-rel R = R · (R ⁻¹)

 zig-zag-complete : {X : 𝓤 ̇} {Y : 𝓥 ̇} (R : X → Y → 𝓣 ̇) → 𝓤 ⊔ 𝓥 ⊔ 𝓣 ̇
 zig-zag-complete {_} {_} {_} {X} {Y} R = (x x' : X) (y y' : Y)
                                        → R x y
                                        → R x' y'
                                        → R x' y
                                        → R x y'

 open PropositionalTruncation pt

 quasi-equiv-rel : {X : 𝓤 ̇} {Y : 𝓥 ̇} (R : X → Y → 𝓣 ̇) (z : zig-zag-complete R)
                 → 𝓤 ⊔ 𝓥 ⊔ 𝓣 ̇
 quasi-equiv-rel {_} {_} {_} {X} {Y} R z
  = ((x : X) → ∃ y ꞉ Y , (R x y)) × ((y : Y) → ∃ x ꞉ X , (R x y))
