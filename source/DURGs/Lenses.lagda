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
  lens-push : (x y : ⊰ 𝓐 ⊱) (p : x ≈⟨ 𝓐 ⟩ y) (u : ⊰ 𝓑 x ⊱) → ⊰ 𝓑 y ⊱
  lens-push-R : (x : ⊰ 𝓐 ⊱) (u : ⊰ 𝓑 x ⊱) → lens-push x x (𝓻 𝓐 x) u ≈⟨ 𝓑 x ⟩ u

record lax-contravariant-lens (𝓤' 𝓥' : Universe) (𝓐 : refl-graph 𝓤 𝓥): 𝓤ω where
 field
  fam-lens : ⊰ 𝓐 ⊱ → refl-graph 𝓤' 𝓥'
 private
  𝓑 = fam-lens
 field
  lens-pull : (x y : ⊰ 𝓐 ⊱) (p : x ≈⟨ 𝓐 ⟩ y) (u : ⊰ 𝓑 y ⊱) → ⊰ 𝓑 x ⊱
  lens-pull-R : (x : ⊰ 𝓐 ⊱) (u : ⊰ 𝓑 x ⊱) → u ≈⟨ 𝓑 x ⟩ lens-pull x x (𝓻 𝓐 x) u
  
\end{code}

We say a oplax (lax) covariant (contraviant) lens is univalent if its family
is valued in univalent reflexive graphs.

\begin{code}

oplax-covariant-lens-is-univalent : {𝓤' 𝓥' : Universe} (𝓐 : refl-graph 𝓤 𝓥)
                                  → oplax-covariant-lens 𝓤' 𝓥' 𝓐
                                  → 𝓤 ⊔ 𝓤' ⊔ 𝓥' ̇
oplax-covariant-lens-is-univalent 𝓐 𝓞
 = (x : ⊰ 𝓐 ⊱) → is-univalent-refl-graph (oplax-covariant-lens.lens-fam 𝓞 x)

lax-contravariant-lens-is-univalent : {𝓤' 𝓥' : Universe} (𝓐 : refl-graph 𝓤 𝓥)
                                    → lax-contravariant-lens 𝓤' 𝓥' 𝓐
                                    → 𝓤 ⊔ 𝓤' ⊔ 𝓥' ̇
lax-contravariant-lens-is-univalent 𝓐 𝓛
 = (x : ⊰ 𝓐 ⊱) → is-univalent-refl-graph (lax-contravariant-lens.fam-lens 𝓛 x)

\end{code}

We now define a display of lenses.

\begin{code}

covariant-displayed-oplax-lens : {𝓤' 𝓥' : Universe} (𝓐 : refl-graph 𝓤 𝓥)
                               → (𝓑 : oplax-covariant-lens 𝓤' 𝓥' 𝓐)
                               → displayed-refl-graph 𝓤' 𝓥' 𝓐
covariant-displayed-oplax-lens {𝓤} {𝓥} {𝓤'} {𝓥'} 𝓐 𝓑 = (I , II , III)
 where
  I : ⊰ 𝓐 ⊱ → 𝓤' ̇
  I x = ⊰ oplax-covariant-lens.lens-fam 𝓑 x ⊱
  II : {x y : ⊰ 𝓐 ⊱}
     → x ≈⟨ 𝓐 ⟩ y
     →  ⊰ oplax-covariant-lens.lens-fam 𝓑 x ⊱
     → ⊰ oplax-covariant-lens.lens-fam 𝓑 y ⊱
     → 𝓥' ̇
  II {x} {y} p u v = oplax-covariant-lens.lens-push 𝓑 x y p u
                   ≈⟨ oplax-covariant-lens.lens-fam 𝓑 y ⟩ v
  III : {x : ⊰ 𝓐 ⊱} (u : ⊰ oplax-covariant-lens.lens-fam 𝓑 x ⊱)
      → II (𝓻 𝓐 x) u u
  III {x} u = oplax-covariant-lens.lens-push-R 𝓑 x u

contravariant-displayed-lax-lens : {𝓤' 𝓥' : Universe} (𝓐 : refl-graph 𝓤 𝓥)
                                 → (𝓑 : lax-contravariant-lens 𝓤' 𝓥' 𝓐)
                                 → displayed-refl-graph 𝓤' 𝓥' 𝓐
contravariant-displayed-lax-lens {𝓤} {𝓥} {𝓤'} {𝓥'} 𝓐 𝓑 = (I , II , III)
 where
  I : ⊰ 𝓐 ⊱ → 𝓤' ̇
  I x = ⊰ lax-contravariant-lens.fam-lens 𝓑 x ⊱
  II : {x y : ⊰ 𝓐 ⊱}
     → x ≈⟨ 𝓐 ⟩ y
     → ⊰ lax-contravariant-lens.fam-lens 𝓑 x ⊱
     → ⊰ lax-contravariant-lens.fam-lens 𝓑 y ⊱
     → 𝓥' ̇
  II {x} {y} p u v = u ≈⟨ lax-contravariant-lens.fam-lens 𝓑 x ⟩
                   lax-contravariant-lens.lens-pull 𝓑 x y p v
  III : {x : ⊰ 𝓐 ⊱} (u : ⊰ lax-contravariant-lens.fam-lens 𝓑 x ⊱)
      → II (𝓻 𝓐 x) u u
  III {x} u = lax-contravariant-lens.lens-pull-R 𝓑 x u


\end{code}

