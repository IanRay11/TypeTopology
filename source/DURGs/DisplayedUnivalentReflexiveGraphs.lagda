Ian Ray. 3rd September 2025.

We provide define displayed univalent reflexive graphs (see Sterling, Ulrik,
etc.)

\begin{code}

{-# OPTIONS --safe --without-K #-}

module DURGs.DisplayedUnivalentReflexiveGraphs where

open import MLTT.Spartan
open import UF.Equiv
open import UF.Subsingletons
open import DURGs.BasicConstructionsonReflexiveGraphs
open import DURGs.DisplayedReflexiveGraphs
open import DURGs.ReflexiveGraphs
open import DURGs.UnivalentReflexiveGraphs

\end{code}

We define the notion of a displayed reflexive graph.

\begin{code}

is-displayed-univalent-refl-graph : (𝓐 : refl-graph 𝓤 𝓥)
                                    (𝓑 : displayed-refl-graph 𝓣 𝓦 𝓐)
                                  → 𝓤 ⊔ 𝓣 ⊔ 𝓦 ̇
is-displayed-univalent-refl-graph 𝓐 𝓑 = (x : ⊰ 𝓐 ⊱)
                                      → is-univalent-refl-graph (⋖ 𝓑 ⋗ x)

displayed-univalent-refl-graph : (𝓣 𝓦 : Universe) (𝓐 : refl-graph 𝓤 𝓥)
                               → 𝓤 ⊔ 𝓥 ⊔ (𝓣 ⊔ 𝓦)⁺ ̇
displayed-univalent-refl-graph 𝓣 𝓦 𝓐
 = Σ 𝓑 ꞉ (displayed-refl-graph 𝓣 𝓦 𝓐) , is-displayed-univalent-refl-graph 𝓐 𝓑
                               
\end{code}
