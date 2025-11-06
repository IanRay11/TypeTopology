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
  lext : {x y : ⊰ 𝓐 ⊱} (p : x ≈⟨ 𝓐 ⟩ y) (u : ⊰ 𝓑 (𝓻 𝓐 x) ⊱) → ⊰ 𝓑 p ⊱
  rext : {x y : ⊰ 𝓐 ⊱} (p : x ≈⟨ 𝓐 ⟩ y) (u : ⊰ 𝓑 (𝓻 𝓐 y) ⊱) → ⊰ 𝓑 p ⊱
  ext-R : {x : ⊰ 𝓐 ⊱} (u : ⊰ 𝓑 (𝓻 𝓐 x) ⊱)
        → lext (𝓻 𝓐 x) u ≈⟨ 𝓑 (𝓻 𝓐 x) ⟩ rext (𝓻 𝓐 x) u
  rext-R : {x : ⊰ 𝓐 ⊱} (u : ⊰ 𝓑 (𝓻 𝓐 x) ⊱)
         → u ≈⟨ 𝓑 (𝓻 𝓐 x) ⟩ rext (𝓻 𝓐 x) u

\end{code}

Now we define when a bivariant midpoint lens is univalent.

\begin{code}

bivariant-midpoint-lens-is-univalent : {𝓤' 𝓥' : Universe} (𝓐 : refl-graph 𝓤 𝓥)
                                     → bivariant-midpoint-lens 𝓤' 𝓥' 𝓐
                                     → 𝓤 ⊔ 𝓥 ⊔ 𝓤' ⊔ 𝓥' ̇
bivariant-midpoint-lens-is-univalent 𝓐 𝓜
 = {x y : ⊰ 𝓐 ⊱} → (p : (x ≈⟨ 𝓐 ⟩ y)) → is-univalent-refl-graph (lens-fam p)
 where
  open bivariant-midpoint-lens 𝓜

\end{code}

Now we define a display of bivariant midpoint lenses.

\begin{code}

bivariant-midpoint-displayed-lens
 : {𝓤' 𝓥' : Universe} (𝓐 : refl-graph 𝓤 𝓥)
 → (𝓑 : bivariant-midpoint-lens 𝓤' 𝓥' 𝓐)
 → displayed-refl-graph 𝓤' 𝓥' 𝓐
bivariant-midpoint-displayed-lens{𝓤} {𝓥} {𝓤'} {𝓥'} 𝓐 𝓑 = (I , II , III)
 where
  open bivariant-midpoint-lens 𝓑
  I : ⊰ 𝓐 ⊱ → 𝓤' ̇
  I x = ⊰ lens-fam (𝓻 𝓐 x) ⊱
  II : {x y : ⊰ 𝓐 ⊱}
     → (x ≈⟨ 𝓐 ⟩ y)
     → ⊰ lens-fam (𝓻 𝓐 x) ⊱
     → ⊰ lens-fam (𝓻 𝓐 y) ⊱
     → 𝓥' ̇
  II {x} {y} p u v = lext p u ≈⟨ lens-fam p ⟩ rext p v
  III : {x : ⊰ 𝓐 ⊱} (u : ⊰ lens-fam (𝓻 𝓐 x) ⊱)
      → II (𝓻 𝓐 x) u u
  III {x} u = ext-R u

syntax bivariant-midpoint-displayed-lens 𝓐 𝓑 = disp± 𝓐 , 𝓑

private
 observation
  : {𝓤' 𝓥' : Universe} (𝓐 : refl-graph 𝓤 𝓥)
  → (𝓑 : bivariant-midpoint-lens 𝓤' 𝓥' 𝓐)
  → (x : ⊰ 𝓐 ⊱)
  → ⋖ disp± 𝓐 , 𝓑 ⋗ x ＝ ([ disp± 𝓐 , 𝓑 ] x
                          , displayed-edge-rel (disp± 𝓐 , 𝓑) (𝓻 𝓐 x)
                          , 𝓻𝓭 (disp± 𝓐 , 𝓑))
 observation 𝓐 𝓑 x = refl

\end{code}

Let's now look at fans of bivariant midpoint lenses.
