Ian Ray. 4th November 2025.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module DURGs.BivariantMidpointLenses where

open import MLTT.Spartan
open import DURGs.BasicConstructionsonReflexiveGraphs
open import DURGs.DisplayedReflexiveGraphs
open import DURGs.DisplayedUnivalentReflexiveGraphs
open import DURGs.Lenses
open import DURGs.ReflexiveGraphs
open import DURGs.UnivalentReflexiveGraphs

\end{code}

We define a technical device that generalize the previous two notion of lenses.

\begin{code}

record bivariant-midpoint-lens (𝓤' 𝓥' : Universe) (𝓐 : refl-graph 𝓤 𝓥): 𝓤ω where
 field
  lens-fam : {x y : ⊰ 𝓐 ⊱} → (x ≈⟨ 𝓐 ⟩ y) → refl-graph 𝓤' 𝓥'
 private
  𝓑 = lens-fam
 field
  lext : (x y : ⊰ 𝓐 ⊱) (p : x ≈⟨ 𝓐 ⟩ y) (u : ⊰ 𝓑 (𝓻 𝓐 x) ⊱) → ⊰ 𝓑 p ⊱
  rext : (x y : ⊰ 𝓐 ⊱) (p : x ≈⟨ 𝓐 ⟩ y) (u : ⊰ 𝓑 (𝓻 𝓐 y) ⊱) → ⊰ 𝓑 p ⊱
  ext-R : (x : ⊰ 𝓐 ⊱) (u : ⊰ 𝓑 (𝓻 𝓐 x) ⊱)
        → lext x x (𝓻 𝓐 x) u ≈⟨ 𝓑 (𝓻 𝓐 x) ⟩ rext x x (𝓻 𝓐 x) u
  rext-R : (x : ⊰ 𝓐 ⊱) (u : ⊰ 𝓑 (𝓻 𝓐 x) ⊱)
         → u ≈⟨ 𝓑 (𝓻 𝓐 x) ⟩ rext x x (𝓻 𝓐 x) u

\end{code}

Now we define a display of bivariant midpoint lenses.

\begin{code}



\end{code}
