Ian Ray. 4th November 2025.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module DURGs.BivariantMidpointLenses where

open import MLTT.Spartan
open import UF.Base
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.Subsingletons
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

\begin{code}

fan-of-bivariant-midpoint-lens
 : {𝓤' 𝓥' : Universe} (𝓐 : refl-graph 𝓤 𝓥)
 → (𝓑 : bivariant-midpoint-lens 𝓤' 𝓥' 𝓐)
 → ((x : ⊰ 𝓐 ⊱)
  → is-univalent-refl-graph (bivariant-midpoint-lens.lens-fam 𝓑 (𝓻 𝓐 x)))
 → (x : ⊰ 𝓐 ⊱)
 → (u : [ disp± 𝓐 , 𝓑 ] x)
 → fan (⋖ disp± 𝓐 , 𝓑 ⋗ x) u ≃ fan (bivariant-midpoint-lens.lens-fam 𝓑 (𝓻 𝓐 x))
                                 (bivariant-midpoint-lens.lext 𝓑 (𝓻 𝓐 x) u)
fan-of-bivariant-midpoint-lens 𝓐 𝓑 fibers-ua x u = III
 where
  open bivariant-midpoint-lens 𝓑
  I : (v : [ disp± 𝓐 , 𝓑 ] x)
    → (rext (𝓻 𝓐 x) v , rext-R v)
    ＝[ fan (lens-fam (𝓻 𝓐 x)) v ]
      (v , 𝓻 (lens-fam (𝓻 𝓐 x)) v)
  I v = fibers-ua x v (rext (𝓻 𝓐 x) v , rext-R v) (v , 𝓻 (lens-fam (𝓻 𝓐 x)) v)
  II : (v : [ disp± 𝓐 , 𝓑 ] x) → rext (𝓻 𝓐 x) v ＝ v
  II v = ap pr₁ (I v)
  III : (Σ v ꞉ ([ disp± 𝓐 , 𝓑 ] x) ,
          lext (𝓻 𝓐 x) u ≈⟨ lens-fam (𝓻 𝓐 x) ⟩ rext (𝓻 𝓐 x) v)
      ≃ (Σ v ꞉ (⊰ lens-fam (𝓻 𝓐 x) ⊱) , lext (𝓻 𝓐 x) u ≈⟨ lens-fam (𝓻 𝓐 x) ⟩ v)
  III = Σ-cong (λ v → transport-≃ (λ - → lext (𝓻 𝓐 x) u ≈⟨ lens-fam (𝓻 𝓐 x) ⟩ -)
               (II v))

\end{code}

We now show that if each fiber of a bivariant midpoint lens is univalent then
the displayed reflexive graph over it is univalent.

\begin{code}

disp-bivariant-midpoint-lens-univalent
 : {𝓤' 𝓥' : Universe} (𝓐 : refl-graph 𝓤 𝓥)
 → (𝓑 : bivariant-midpoint-lens 𝓤' 𝓥' 𝓐)
 → ((x : ⊰ 𝓐 ⊱)
 → is-univalent-refl-graph (bivariant-midpoint-lens.lens-fam 𝓑 (𝓻 𝓐 x)))
 → is-displayed-univalent-refl-graph 𝓐 (disp± 𝓐 , 𝓑)
disp-bivariant-midpoint-lens-univalent 𝓐 𝓑 fibers-ua x u 
 = equiv-to-prop (fan-of-bivariant-midpoint-lens 𝓐 𝓑 fibers-ua x u)
    (fibers-ua x (lext (𝓻 𝓐 x) u))
 where
  open bivariant-midpoint-lens 𝓑

\end{code}
