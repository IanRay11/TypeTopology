Ian Ray. 3rd March 2026.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module DURGs.AlgebraicHierarchyWhiteboard where

open import MLTT.Spartan 
open import DURGs.BivariantMidpointLenses
open import DURGs.ReflexiveGraphs
open import DURGs.ReflexiveGraphConstructions
open import DURGs.ReflexiveGraphExamples
open import DURGs.UnivalentReflexiveGraphClosureProperties
open import DURGs.DisplayedReflexiveGraphs
open import DURGs.DisplayedUnivalentReflexiveGraphs
open import DURGs.Lenses
open import DURGs.UnivalentFamilies
open import DURGs.UnivalentReflexiveGraphs
open import DURGs.UnivalenceProperty
open import UF.PropTrunc
open import UF.Sets
open import UF.Subsingletons
open import UF.SubtypeClassifier

\end{code}

We define some algerbaic structures characterize their equality with lenses and
consider the induced hierarchy and it's relationships.

\begin{code}

Magma : (𝓤 : Universe) → (𝓤 ⁺) ̇
Magma 𝓤 = Σ M@(X , _) ꞉ ∞-Magma 𝓤 , is-set X
