\begin{code}

{-# OPTIONS --safe --without-K #-}

module DURGs.UnivalentFamilies where

open import MLTT.Spartan
open import UF.Base
open import UF.Equiv
open import UF.Subsingletons
open import UF.Subsingletons-Properties
open import DURGs.BasicConstructionsonReflexiveGraphs
open import DURGs.DisplayedReflexiveGraphs
open import DURGs.DisplayedUnivalentReflexiveGraphs
open import DURGs.PathAlgebraToolkit
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
id-to-equiv-family {_} {_} {_} {B} x y refl = ≃-refl (B x)

is-univalent-family-implies-id-to-equiv
 : {A : 𝓤 ̇} {B : A → 𝓣 ̇}
 → is-univalent-family (A , B)
 → (x y : A)
 → is-equiv (id-to-edge (refl-graph-image A B) x y)
is-univalent-family-implies-id-to-equiv {𝓤} {𝓣} {A} {B} is-ua-fam x y
 = is-ua-fam x y

\end{code}

We can also state this in terms of contractible/propositional fans (or cofans).
This may be useful later...
