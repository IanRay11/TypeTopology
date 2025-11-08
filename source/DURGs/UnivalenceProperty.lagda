Ian Ray. 7th November 2025.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module DURGs.UnivalenceProperty where

open import MLTT.Spartan
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.FunExt
open import DURGs.BasicConstructionsonReflexiveGraphs
open import DURGs.DisplayedReflexiveGraphs
open import DURGs.DisplayedUnivalentReflexiveGraphs
open import DURGs.Lenses
open import DURGs.ReflexiveGraphs
open import DURGs.UnivalentReflexiveGraphs

\end{code}

We show that univalence is a proposition.

\begin{code}

refl-graph-univalence-is-a-property : Fun-Ext
                                    → (𝓐 : refl-graph 𝓤 𝓥)
                                    → is-prop (is-univalent-refl-graph 𝓐)
refl-graph-univalence-is-a-property fe 𝓐
 = Π-is-prop fe (λ - → being-prop-is-prop fe)

displayed-refl-graph-univalence-is-a-property
 : Fun-Ext
 → (𝓐 : refl-graph 𝓤 𝓥) (𝓑 : displayed-refl-graph 𝓤' 𝓥' 𝓐)
 → is-prop (is-displayed-univalent-refl-graph 𝓐 𝓑)
displayed-refl-graph-univalence-is-a-property fe 𝓐 𝓑
 = Π-is-prop fe (λ - → refl-graph-univalence-is-a-property fe (⋖ 𝓑 ⋗ -))

\end{code}

We show the type of lens structures is a proposition.


