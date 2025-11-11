Ian Ray. 11th November 2025.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module DURGs.DefinitionalLenses where

open import MLTT.Spartan
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.FunExt
open import DURGs.BasicConstructionsonReflexiveGraphs
open import DURGs.BivariantMidpointLenses
open import DURGs.ClosurePropertiesofUnivalentReflexiveGraphs
open import DURGs.DisplayedReflexiveGraphs
open import DURGs.DisplayedUnivalentReflexiveGraphs
open import DURGs.Lenses
open import DURGs.ReflexiveGraphs
open import DURGs.UnivalentReflexiveGraphs

\end{code}

We investigate definitional lenses.

How do we implement this?

\begin{code}

definitional-covariant-lens : {𝓤' 𝓥' : Universe} (𝓐 : refl-graph 𝓤 𝓥)
                            → (𝓑 : (x : ⊰ 𝓐 ⊱) → refl-graph 𝓤' 𝓥')
                            → oplax-covariant-lens 𝓤' 𝓥' 𝓐
definitional-covariant-lens 𝓐 𝓑 = record
 { lens-fam = 𝓑
 ; lens-push = {!!}
 ; lens-push-R = {!!}
 }
