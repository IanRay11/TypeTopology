Ian Ray. July 20th 2026.

This file expirements with using universes rather than cardinals to define
accessibility and related notions.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import Categories.Functor
open import Categories.Pre
open import Categories.Wild
open import Categories.Notation.Pre
open import Categories.Notation.Wild

module Categories.Accessibility where

\end{code}

We define when a precategory is filtered.

A precategory P is filtered if it is:
1) inhabited, that is, there exists d : obj P,
2) for every x , y : obj P there is an upper bound z : obj 𝓓, that is, there are
   morphisms f : hom x z and g : hom y z,
3) for every f, g : hom x y there is h : hom y z such that h ∘ g = h ∘ f.

\begin{code}

module _ {𝓤 𝓥 : Universe} (P : Precategory 𝓤 𝓥) where
 open PrecategoryNotation P

 record is-filtered : 𝓤 ⊔ 𝓥 ̇ where
  field
   bot : obj P
   upper-bound : (x y : obj P) → Σ z ꞉ obj P , hom x z × hom y z
   coherence : {x y : obj P} (f g : hom x y)
             → Σ z ꞉ obj P , Σ h ꞉ hom y z , h ◦ g ＝ h ◦ f

Filtered-Precategory : (𝓤 𝓥 : Universe) → (𝓤 ⊔ 𝓥)⁺ ̇
Filtered-Precategory 𝓤 𝓥 = Σ P ꞉ Precategory 𝓤 𝓥 , is-filtered P

\end{code}

A diagram (functor) D : P → X is filtered if P is filtered.

\begin{code}

module _ {𝓤 𝓥 𝓦 𝓣 : Universe} {P : Precategory 𝓤 𝓥} {X : Precategory 𝓦 𝓣}
       where
 open PrecategoryNotation P

 is-filtered-functor : Functor P X → 𝓤 ⊔ 𝓥 ̇
 is-filtered-functor F = is-filtered P

\end{code}

TODO Add colimits to the library so we can define filtered colimits.

A colimit of a filtered diagram D : P → X is filtered.

\begin{code}

\end{code}
