Ian Ray. July 20th 2026.

We expirement with using universes rather than cardinals to define
accessibility and related notions.

We test this expiremental development by formalizing results from
"Initial Algebras Unchained".

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import Categories.Colimits
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

A functor F : X → Y is filtered if P is filtered.

\begin{code}

module _ {𝓤 𝓥 𝓦 𝓣 : Universe} {X : Precategory 𝓤 𝓥} {Y : Precategory 𝓦 𝓣}
       where

 is-filtered-functor : Functor X Y → 𝓤 ⊔ 𝓥 ̇
 is-filtered-functor F = is-filtered X

Filtered-Functor : (X : Precategory 𝓤 𝓥) (Y : Precategory 𝓦 𝓣) → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓣 ̇
Filtered-Functor X Y = Σ F ꞉ Functor X Y , is-filtered-functor F

\end{code}

A colimit of a filtered diagram D : C → X is filtered.

\begin{code}

module _ {C : Precategory 𝓤 𝓥} {X : Precategory 𝓦 𝓣} (D : Functor C X)
       where

 is-filtered-colimit : Colim D → 𝓤 ⊔ 𝓥 ̇
 is-filtered-colimit c = is-filtered-functor D

Filtered-Colimit
 : {C : Precategory 𝓤 𝓥} {X : Precategory 𝓦 𝓣} (D : Functor C X)
 → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓣 ̇
Filtered-Colimit D = Σ c ꞉ Colim D , is-filtered-colimit D c

\end{code}

A functor is finitary if it preserves filtered colimits.

\begin{code}

module _ {C : Precategory 𝓦 𝓣} {X : Precategory 𝓤 𝓥} {Y : Precategory 𝓤' 𝓥'}
       where

 is-finitary : (Functor X Y)
             → 𝓦 ⊔ 𝓣 ⊔ 𝓤 ⊔ 𝓥 ⊔ 𝓤' ⊔ 𝓥' ̇
 is-finitary F = (D : Functor C X)
               → ((c , fil) : Filtered-Colimit D)
               → F preserves c
