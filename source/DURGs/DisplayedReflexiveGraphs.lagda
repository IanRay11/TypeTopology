Ian Ray. 28th August 2025.

We define displayed reflexive graphs (see Sterling, Ulrik, etc.)

\begin{code}

{-# OPTIONS --safe --without-K #-}

module DURGs.DisplayedReflexiveGraphs where

open import MLTT.Spartan
open import UF.Base
open import DURGs.ReflexiveGraphs

module _ (𝓣 𝓦 : Universe) where

 displayed-refl-graph : (𝓐 : refl-graph 𝓤 𝓥) →  𝓤 ⊔ 𝓥 ⊔ (𝓣 ⊔ 𝓦)⁺ ̇
 displayed-refl-graph 𝓐
  = Σ B ꞉ (⊰ 𝓐 ⊱ → 𝓣 ̇) ,
     Σ R ꞉ ({x y : ⊰ 𝓐 ⊱} (p : x ≈⟨ 𝓐 ⟩ y) → B x → B y → 𝓦 ̇) ,
      ({x : ⊰ 𝓐 ⊱} (u : B x) → R (𝓻 𝓐 x) u u)

\end{code}

More boiler plate

\begin{code}

module _ {𝓐 : refl-graph 𝓤 𝓥} where

 [_] : displayed-refl-graph 𝓣 𝓦 𝓐 → ⊰ 𝓐 ⊱ → 𝓣 ̇
 [ (B , _) ] = B

 displayed-edge-rel : (𝓑 : displayed-refl-graph 𝓣 𝓦 𝓐)
                    → {x y : ⊰ 𝓐 ⊱} (p : x ≈⟨ 𝓐 ⟩ y)
                    → [ 𝓑 ] x → [ 𝓑 ] y → 𝓦 ̇
 displayed-edge-rel (_ , R , _) = R

 syntax displayed-edge-rel 𝓑 p u v = u ≈＜ 𝓑 , p ＞ v

 𝓻𝓭 : (𝓑 : displayed-refl-graph 𝓣 𝓦 𝓐)
    → {x : ⊰ 𝓐 ⊱} (u : [ 𝓑 ] x)
    → u ≈＜ 𝓑 , 𝓻 𝓐 x ＞ u 
 𝓻𝓭 (_ , _ , r) u = r u
 
\end{code}

We show that the components of a displayed reflexive graph is itself a
reflexive graph.

\begin{code}

 component-refl-graph : displayed-refl-graph 𝓣 𝓦 𝓐
                      → ⊰ 𝓐 ⊱
                      → refl-graph 𝓣 𝓦
 component-refl-graph 𝓑 x
  = ([ 𝓑 ] x , displayed-edge-rel 𝓑 (𝓻 𝓐 x) , 𝓻𝓭 𝓑)

 syntax component-refl-graph 𝓑 x = ⋖ 𝓑 ⋗ x

\end{code}

Displayed reflexive graph homomorphism.

\begin{code}

displayed-refl-graph-hom : {𝓐 : refl-graph 𝓤 𝓥} {𝓐' : refl-graph 𝓤' 𝓥'}
                         → (F : refl-graph-hom 𝓐 𝓐')
                         → (𝓑 : displayed-refl-graph 𝓣 𝓦 𝓐)
                         → (𝓑' : displayed-refl-graph 𝓣' 𝓦' 𝓐')
                         → 𝓤 ⊔ 𝓥 ⊔ 𝓣 ⊔ 𝓦 ⊔ 𝓣' ⊔ 𝓦' ̇
displayed-refl-graph-hom {_} {_} {_} {_} {_} {_} {_} {_} {𝓐} {𝓐'}
 (F₀ , F₁ , Fᵣ) 𝓑 𝓑'
 = Σ G ꞉ ((x : ⊰ 𝓐 ⊱) → [ 𝓑 ] x → [ 𝓑' ] (F₀ x)) ,
    Σ G' ꞉ ((x y : ⊰ 𝓐 ⊱) (p : x ≈⟨ 𝓐 ⟩ y) (u : [ 𝓑 ] x) (v : [ 𝓑 ] y)
         → u ≈＜ 𝓑 , p ＞ v
         → (G x u) ≈＜ 𝓑' , (F₁ x y p) ＞ (G y v)) ,
     ((x : ⊰ 𝓐 ⊱) (u : [ 𝓑 ] x)
         → G' x x (𝓻 𝓐 x) u u (𝓻𝓭 𝓑 u)
         ＝ transport (λ - → (G x u) ≈＜ 𝓑' , - ＞ (G x u))
             (Fᵣ x ⁻¹) (𝓻𝓭 𝓑' (G x u)))

\end{code}
