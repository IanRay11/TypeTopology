\begin{code}

{-# OPTIONS --safe --without-K #-}

module DURGs.Lenses where

open import MLTT.Spartan
open import DURGs.BasicConstructionsonReflexiveGraphs
open import DURGs.DisplayedReflexiveGraphs
open import DURGs.DisplayedUnivalentReflexiveGraphs
open import DURGs.ReflexiveGraphs
open import DURGs.UnivalentReflexiveGraphs

\end{code}

We introduce the notion of lenses which allow for a deeper characterization
of transport.

We will use record types.

\begin{code}

record oplax-covariant-lens (𝓤' 𝓥' : Universe) (𝓐 : refl-graph 𝓤 𝓥): 𝓤ω where
 field
  lens-fam : ⊰ 𝓐 ⊱ → refl-graph 𝓤' 𝓥'
 private
  𝓑 = lens-fam
 field
  lens-push : {x y : ⊰ 𝓐 ⊱} (p : x ≈⟨ 𝓐 ⟩ y) (u : ⊰ 𝓑 x ⊱) → ⊰ 𝓑 y ⊱
  lens-push-R : {x : ⊰ 𝓐 ⊱} (u : ⊰ 𝓑 x ⊱) → lens-push (𝓻 𝓐 x) u ≈⟨ 𝓑 x ⟩ u

record lax-contravariant-lens (𝓤' 𝓥' : Universe) (𝓐 : refl-graph 𝓤 𝓥): 𝓤ω where
 field
  lens-fam : ⊰ 𝓐 ⊱ → refl-graph 𝓤' 𝓥'
 private
  𝓑 = lens-fam
 field
  lens-pull : {x y : ⊰ 𝓐 ⊱} (p : x ≈⟨ 𝓐 ⟩ y) (u : ⊰ 𝓑 y ⊱) → ⊰ 𝓑 x ⊱
  lens-pull-R : {x : ⊰ 𝓐 ⊱} (u : ⊰ 𝓑 x ⊱) → u ≈⟨ 𝓑 x ⟩ lens-pull (𝓻 𝓐 x) u
  
\end{code}

We say a oplax (lax) covariant (contraviant) lens is univalent if its family
is valued in univalent reflexive graphs.

\begin{code}

oplax-covariant-lens-is-univalent : {𝓤' 𝓥' : Universe} (𝓐 : refl-graph 𝓤 𝓥)
                                  → oplax-covariant-lens 𝓤' 𝓥' 𝓐
                                  → 𝓤 ⊔ 𝓤' ⊔ 𝓥' ̇
oplax-covariant-lens-is-univalent 𝓐 𝓞
 = (x : ⊰ 𝓐 ⊱) → is-univalent-refl-graph (lens-fam x)
 where
  open oplax-covariant-lens 𝓞

lax-contravariant-lens-is-univalent : {𝓤' 𝓥' : Universe} (𝓐 : refl-graph 𝓤 𝓥)
                                    → lax-contravariant-lens 𝓤' 𝓥' 𝓐
                                    → 𝓤 ⊔ 𝓤' ⊔ 𝓥' ̇
lax-contravariant-lens-is-univalent 𝓐 𝓛
 = (x : ⊰ 𝓐 ⊱) → is-univalent-refl-graph (lens-fam x)
 where
  open lax-contravariant-lens 𝓛

\end{code}

We now define a display of lenses.

\begin{code}

covariant-displayed-oplax-lens : {𝓤' 𝓥' : Universe} (𝓐 : refl-graph 𝓤 𝓥)
                               → (𝓑 : oplax-covariant-lens 𝓤' 𝓥' 𝓐)
                               → displayed-refl-graph 𝓤' 𝓥' 𝓐
covariant-displayed-oplax-lens {𝓤} {𝓥} {𝓤'} {𝓥'} 𝓐 𝓑 = (I , II , III)
 where
  open oplax-covariant-lens 𝓑
  I : ⊰ 𝓐 ⊱ → 𝓤' ̇
  I x = ⊰ lens-fam x ⊱
  II : {x y : ⊰ 𝓐 ⊱}
     → x ≈⟨ 𝓐 ⟩ y
     →  ⊰ lens-fam x ⊱
     → ⊰ lens-fam y ⊱
     → 𝓥' ̇
  II {x} {y} p u v = lens-push p u ≈⟨ lens-fam y ⟩ v
  III : {x : ⊰ 𝓐 ⊱} (u : ⊰ lens-fam x ⊱)
      → II (𝓻 𝓐 x) u u
  III {x} u = lens-push-R u

syntax covariant-displayed-oplax-lens 𝓐 𝓑 = disp⁺ 𝓐 , 𝓑

contravariant-displayed-lax-lens : {𝓤' 𝓥' : Universe} (𝓐 : refl-graph 𝓤 𝓥)
                                 → (𝓑 : lax-contravariant-lens 𝓤' 𝓥' 𝓐)
                                 → displayed-refl-graph 𝓤' 𝓥' 𝓐
contravariant-displayed-lax-lens {𝓤} {𝓥} {𝓤'} {𝓥'} 𝓐 𝓑 = (I , II , III)
 where
  open lax-contravariant-lens 𝓑
  I : ⊰ 𝓐 ⊱ → 𝓤' ̇
  I x = ⊰ lens-fam x ⊱
  II : {x y : ⊰ 𝓐 ⊱}
     → x ≈⟨ 𝓐 ⟩ y
     → ⊰ lens-fam x ⊱
     → ⊰ lens-fam y ⊱
     → 𝓥' ̇
  II {x} {y} p u v = u ≈⟨ lens-fam x ⟩ lens-pull p v
  III : {x : ⊰ 𝓐 ⊱} (u : ⊰ lens-fam x ⊱)
      → II (𝓻 𝓐 x) u u
  III {x} u = lens-pull-R u

syntax contravariant-displayed-lax-lens 𝓐 𝓑 = disp⁻ 𝓐 , 𝓑

\end{code}

We observe the components of the displayed lenses are as we expect.

\begin{code}

private
 observation
  : {𝓤' 𝓥' : Universe} (𝓐 : refl-graph 𝓤 𝓥)
  → (𝓑 : oplax-covariant-lens 𝓤' 𝓥' 𝓐)
  → (x : ⊰ 𝓐 ⊱)
  → ⋖ disp⁺ 𝓐 , 𝓑 ⋗ x ＝ ([ disp⁺ 𝓐 , 𝓑 ] x
                          , displayed-edge-rel (disp⁺ 𝓐 , 𝓑) (𝓻 𝓐 x)
                          , 𝓻𝓭 (disp⁺ 𝓐 , 𝓑))
 observation 𝓐 𝓑 x = refl

 observation'
  : {𝓤' 𝓥' : Universe} (𝓐 : refl-graph 𝓤 𝓥)
  → (𝓑 : lax-contravariant-lens 𝓤' 𝓥' 𝓐)
  → (x : ⊰ 𝓐 ⊱)
  → ⋖ disp⁻ 𝓐 , 𝓑 ⋗ x ＝ ([ disp⁻ 𝓐 , 𝓑 ] x
                          , displayed-edge-rel (disp⁻ 𝓐 , 𝓑) (𝓻 𝓐 x)
                          , 𝓻𝓭 (disp⁻ 𝓐 , 𝓑))
 observation' 𝓐 𝓑 x = refl

\end{code}

Now let's consider the description of fans of displayed lenses.

\begin{code}
 
fan-of-oplax-covariant-lens
 : {𝓤' 𝓥' : Universe} (𝓐 : refl-graph 𝓤 𝓥)
 → (𝓑 : oplax-covariant-lens 𝓤' 𝓥' 𝓐)
 → (x : ⊰ 𝓐 ⊱)
 → (u : [ disp⁺ 𝓐 , 𝓑 ] x)
 → fan (⋖ disp⁺ 𝓐 , 𝓑 ⋗ x) u ＝ fan (oplax-covariant-lens.lens-fam 𝓑 x)
                                 (oplax-covariant-lens.lens-push 𝓑 (𝓻 𝓐 x) u)
fan-of-oplax-covariant-lens 𝓐 𝓑 x u = refl

cofan-of-lax-contravariant-lens
 : {𝓤' 𝓥' : Universe} (𝓐 : refl-graph 𝓤 𝓥)
 → (𝓑 : lax-contravariant-lens 𝓤' 𝓥' 𝓐)
 → (x : ⊰ 𝓐 ⊱)
 → (u : [ disp⁻ 𝓐 , 𝓑 ] x)
 → cofan (⋖ disp⁻ 𝓐 , 𝓑 ⋗ x) u ＝ cofan (lax-contravariant-lens.lens-fam 𝓑 x)
                                  (lax-contravariant-lens.lens-pull 𝓑 (𝓻 𝓐 x) u)
cofan-of-lax-contravariant-lens 𝓐 𝓑 x u = refl

\end{code}

We now show that if each fiber of a lens is univalent then the displayed
reflexive graph is univalent.

\begin{code}

disp-oplax-covariant-lens-univalent
 : {𝓤' 𝓥' : Universe} (𝓐 : refl-graph 𝓤 𝓥)
 → (𝓑 : oplax-covariant-lens 𝓤' 𝓥' 𝓐)
 → ((x : ⊰ 𝓐 ⊱)
 → is-univalent-refl-graph (oplax-covariant-lens.lens-fam 𝓑 x))
 → is-displayed-univalent-refl-graph 𝓐 (disp⁺ 𝓐 , 𝓑)
disp-oplax-covariant-lens-univalent 𝓐 𝓑 fibers-ua x u 
 = fibers-ua x (lens-push (𝓻 𝓐 x) u)
 where
  open oplax-covariant-lens 𝓑

disp-lax-contravariant-lens-univalent
 : {𝓤' 𝓥' : Universe} (𝓐 : refl-graph 𝓤 𝓥)
 → (𝓑 : lax-contravariant-lens 𝓤' 𝓥' 𝓐)
 → ((x : ⊰ 𝓐 ⊱)
 → is-univalent-refl-graph (lax-contravariant-lens.lens-fam 𝓑 x))
 → is-displayed-univalent-refl-graph 𝓐 (disp⁻ 𝓐 , 𝓑)
disp-lax-contravariant-lens-univalent 𝓐 𝓑 fibers-ua x 
 = prop-cofan-to-fan {_} {_} {⋖ disp⁻ 𝓐 , 𝓑 ⋗ x}
    ((λ - → fibers-co-ua (lens-pull (𝓻 𝓐 x) -))) 
 where
  open lax-contravariant-lens 𝓑
  fibers-co-ua = prop-fan-to-cofan {_} {_} {lens-fam x} (fibers-ua x)
  
\end{code}
