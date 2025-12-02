\begin{code}

{-# OPTIONS --safe --without-K #-}

module DURGs.UnivalentFamilies where

open import MLTT.Spartan
open import UF.Base
open import UF.Equiv
open import UF.Subsingletons
open import UF.Subsingletons-Properties
open import DURGs.ReflexiveGraphs
open import DURGs.UnivalentReflexiveGraphs

\end{code}

We define the reflexive graph image as a means to define univalent families.

\begin{code}

refl-graph-image : (A : 𝓤 ̇)
                 → (A → 𝓣 ̇)
                 → refl-graph 𝓤 𝓣
refl-graph-image {𝓤} {𝓣} A B = (A , I , II)
 where
  I : A → A → 𝓣 ̇
  I x y = B x ≃ B y
  II : (x : A) → I x x
  II x = ≃-refl (B x)

is-univalent-family : Σ A ꞉ 𝓤 ̇ , (A → 𝓣 ̇)
                    → 𝓤 ⊔ 𝓣 ̇
is-univalent-family (A , B) = is-univalent-refl-graph (refl-graph-image A B)

\end{code}

We can give some equivalent characterizations of univalent family of types.

\begin{code}

id-to-equiv-family : {A : 𝓤 ̇} {B : A → 𝓣 ̇}
                   → (x y : A)
                   → x ＝ y
                   → B x ≃ B y
id-to-equiv-family {_} {_} {A} {B} x y = id-to-edge (refl-graph-image A B) 

is-univalent-family-implies-id-to-equiv
 : {A : 𝓤 ̇} {B : A → 𝓣 ̇}
 → is-univalent-family (A , B)
 → (x y : A)
 → is-equiv (id-to-equiv-family x y)
is-univalent-family-implies-id-to-equiv {𝓤} {𝓣} {A} {B} is-ua-fam x y
 = prop-fans-implies-id-to-edge-equiv is-ua-fam x y

\end{code}

We can also state this in terms of contractible/propositional fans (or cofans).
This may be useful later...

Propositional reflexive graph image

\begin{code}

prop-refl-graph-image : (A : 𝓤 ̇)
                      → (A → 𝓣 ̇)
                      → refl-graph 𝓤 𝓣
prop-refl-graph-image {𝓤} {𝓣} A B = (A , I , II)
 where
  I : A → A → 𝓣 ̇
  I x y = B x ↔ B y
  II : (x : A) → I x x
  II x = (id , id)

\end{code}

We define a univalent family of 'path objects'.

\begin{code}

univalent-family-of-path-objects
 : {𝓦 𝓣 : Universe}
 → ((U , 𝓔) : Σ U ꞉ 𝓤 ̇ , (U → univalent-refl-graph 𝓦 𝓣))
 → 𝓤 ⊔ 𝓦 ̇
univalent-family-of-path-objects (U , 𝓔)
 = is-univalent-refl-graph (refl-graph-image U (λ A → ⊰ (𝓔 A) ⊱ᵤ))

\end{code}
