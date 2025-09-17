\begin{code}

{-# OPTIONS --safe --without-K #-}

module DURGs.ClosurePropertiesofUnivalentReflexiveGraphs where

open import MLTT.Spartan
open import UF.Base
open import UF.Equiv
open import UF.Subsingletons
open import UF.Subsingletons-Properties
open import DURGs.BasicConstructionsonReflexiveGraphs
open import DURGs.DisplayedReflexiveGraphs
open import DURGs.DisplayedUnivalentReflexiveGraphs
open import DURGs.PathAlgebraToolkit
open import DURGs.ReflexiveGraphs
open import DURGs.UnivalentFamilies
open import DURGs.UnivalentReflexiveGraphs

\end{code}

We record closure properties of (displayed?) univalent reflexive graphs.

\begin{code}

univalence-closed-under-opposite : (𝓐 : refl-graph 𝓤 𝓥)
                                 → is-univalent-refl-graph 𝓐
                                 → is-univalent-refl-graph (𝓐 ᵒᵖ)
univalence-closed-under-opposite 𝓐 𝓐-ua x y = {!!}

univalence-closed-under-opposite' : (𝓐 : refl-graph 𝓤 𝓥)
                                  → is-univalent-refl-graph (𝓐 ᵒᵖ)
                                  → is-univalent-refl-graph 𝓐
univalence-closed-under-opposite' 𝓐 = univalence-closed-under-opposite (𝓐 ᵒᵖ)

univalence-closed-under-total
 : (𝓐 : refl-graph 𝓤 𝓥) (𝓑 : displayed-refl-graph 𝓣 𝓦 𝓐)
 → is-univalent-refl-graph 𝓐
 → is-displayed-univalent-refl-graph 𝓐 𝓑
 → is-univalent-refl-graph (𝓐 ﹐ 𝓑)
univalence-closed-under-total 𝓐 𝓑 𝓐-ua 𝓑-ua x y = {!!}

univalence-closed-under-binary-product
 : (𝓐 : refl-graph 𝓤 𝓥) (𝓐' : refl-graph 𝓤 𝓥)
 → is-univalent-refl-graph 𝓐
 → is-univalent-refl-graph 𝓐'
 → is-univalent-refl-graph (𝓐 ⊗ 𝓐')
univalence-closed-under-binary-product 𝓐 𝓐' 𝓐-ua 𝓐'-ua x y = {!!}

\end{code}
