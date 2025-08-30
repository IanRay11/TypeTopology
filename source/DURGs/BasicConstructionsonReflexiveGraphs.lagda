Ian Ray. 28th August 2025.

We provide some basic contructions on (displayed) reflexive graphs (see
Sterling, Ulrik, etc.)

\begin{code}

{-# OPTIONS --safe --without-K #-}

module DURGs.BasicConstructionsonReflexiveGraphs where

open import MLTT.Spartan
open import DURGs.ReflexiveGraphs
open import DURGs.DisplayedReflexiveGraphs

\end{code}

Given a reflexive graph and a displayed reflexive graph over it we can define
the total reflexive graph as follows.

\begin{code}

module _ (𝓐 : refl-graph 𝓤 𝓥) (𝓑 : displayed-refl-graph 𝓤 𝓥 𝓣 𝓦 𝓐) where

 total-refl-graph : refl-graph (𝓤 ⊔ 𝓣) (𝓥 ⊔ 𝓦)
 total-refl-graph = ((Σ x ꞉ ⊰ 𝓐 ⊱ , [ 𝓑 ] x) , I , II)
  where
   I : Σ x ꞉ ⊰ 𝓐 ⊱ , [ 𝓑 ] x
     → Σ x ꞉ ⊰ 𝓐 ⊱ , [ 𝓑 ] x
     → 𝓥 ⊔ 𝓦 ̇
   I (a , b) (a' , b') = Σ p ꞉ a ≈⟨ 𝓐 ⟩ a' , b ≈＜ 𝓑 , p ＞ b'
   II : (t : Σ x ꞉ ⊰ 𝓐 ⊱ , [ 𝓑 ] x)
      → I t t
   II (a , b) = (𝓻 𝓐 a , 𝓻𝓭 𝓑 b)

\end{code}

We define the projection map from the total reflexive graph to the base
reflexive graph.

\begin{code}

 proj-refl-graph : refl-graph-hom total-refl-graph 𝓐
 proj-refl-graph = (pr₁ , (λ t t' → pr₁) , ∼-refl)

\end{code}

We define the binary product of reflexive graphs as follows.

\begin{code}

binary-prod-refl-graph : (𝓐 : refl-graph 𝓤 𝓥) (𝓐' : refl-graph 𝓤' 𝓥')
                       → refl-graph (𝓤 ⊔ 𝓤') (𝓥 ⊔ 𝓥')
binary-prod-refl-graph {𝓤} {𝓥} {𝓤'} {𝓥'} 𝓐 𝓐' = ((⊰ 𝓐 ⊱ × ⊰ 𝓐' ⊱) , I , II)
 where
  I : ⊰ 𝓐 ⊱ × ⊰ 𝓐' ⊱ → ⊰ 𝓐 ⊱ × ⊰ 𝓐' ⊱ → 𝓥 ⊔ 𝓥' ̇
  I (x , x') (y , y') = (x ≈⟨ 𝓐 ⟩ y) × (x' ≈⟨ 𝓐' ⟩ y')
  II : (t : ⊰ 𝓐 ⊱ × ⊰ 𝓐' ⊱) → I t t
  II (x , x') = (𝓻 𝓐 x , 𝓻 𝓐' x')

\end{code}

Of course, we can generalize to products of reflexive graphs as follows.

\begin{code}

prod-refl-graphs : (A : 𝓤' ̇) (𝓑 : (x : A) → refl-graph 𝓤 𝓥)
                 → refl-graph (𝓤' ⊔ 𝓤) (𝓤' ⊔ 𝓥)
prod-refl-graphs {𝓤'} {𝓤} {𝓥} A 𝓑
 = (((x : A) → ⊰ 𝓑 x ⊱) , I , II)
 where
  I : ((x : A) → ⊰ 𝓑 x ⊱)
    → ((x : A) → ⊰ 𝓑 x ⊱)
    → 𝓤' ⊔ 𝓥 ̇
  I f f' = (x : A) → f x ≈⟨ 𝓑 x ⟩ f' x
  II : (f : (x : A) → ⊰ 𝓑 x ⊱) → I f f
  II f x = 𝓻 (𝓑 x) (f x)

\end{code}
