\begin{code}

{-# OPTIONS --safe --without-K #-}

module DURGs.PathAlgebraToolkit where

open import MLTT.Spartan
open import UF.Equiv
open import UF.Subsingletons
open import DURGs.BasicConstructionsonReflexiveGraphs
open import DURGs.DisplayedReflexiveGraphs
open import DURGs.DisplayedUnivalentReflexiveGraphs
open import DURGs.ReflexiveGraphs
open import DURGs.UnivalentReflexiveGraphs

\end{code}

When reflexive graphs are univalent they natrually inherit many of the
familiar results we have for identifications. We do not exhaust all of these
results but we will record some of the obvious ones.

We begin with concatenation and inverse of edges.

\begin{code}

concat-edges : {𝓐 : univalent-refl-graph 𝓤 𝓥} {x y z : ⊰ 𝓐 ⊱ᵤ}
             → x ≈ᵤ⟨ 𝓐 ⟩ y
             → y ≈ᵤ⟨ 𝓐 ⟩ z
             → x ≈ᵤ⟨ 𝓐 ⟩ z
concat-edges {_} {_} {𝓐} p q
 = id-to-edge' (underlying-refl-graph 𝓐) (edge-to-id' 𝓐 p ∙ edge-to-id' 𝓐 q)

syntax concat-edges p q = p ∙ᵤ q

inverse-edge : {𝓐 : univalent-refl-graph 𝓤 𝓥} {x y z : ⊰ 𝓐 ⊱ᵤ}
             → x ≈ᵤ⟨ 𝓐 ⟩ y
             → y ≈ᵤ⟨ 𝓐 ⟩ x
inverse-edge {_} {_} {𝓐} p
 = id-to-edge' (underlying-refl-graph 𝓐) (edge-to-id' 𝓐 p ⁻¹)

syntax inverse-edge p = p ᵤ⁻¹ 

\end{code}
