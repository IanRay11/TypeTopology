Ian Ray. 28th August 2025.

We define displayed reflexive graphs (see Sterling, Ulrik, etc.)

\begin{code}

{-# OPTIONS --safe --without-K #-}

module DURGs.DisplayedReflexiveGraphs where

open import MLTT.Spartan
open import DURGs.ReflexiveGraphs

module _ (𝓤 𝓥 𝓣 𝓦 : Universe) where

 displayed-refl-graph : (𝓐 : refl-graph 𝓤 𝓥) →  𝓤 ⊔ 𝓥 ⊔ (𝓣 ⊔ 𝓦)⁺ ̇
 displayed-refl-graph 𝓐
  = Σ B ꞉ (⊰ 𝓐 ⊱ → 𝓣 ̇)
    , Σ R ꞉ ({x y : ⊰ 𝓐 ⊱} (p : x ≈⟨ 𝓐 ⟩ y) → B x → B y → 𝓦 ̇)
     , ({x : ⊰ 𝓐 ⊱} {u : B x} → R (𝓻 𝓐) u u)

\end{code}

More boiler plate

\begin{code}

module _ {𝓐 : refl-graph 𝓤 𝓥} where

 ⊲_⊳ : displayed-refl-graph 𝓤 𝓥 𝓣 𝓦 𝓐 → ⊰ 𝓐 ⊱ → 𝓣 ̇
 ⊲ (B , _) ⊳ = B

 displayed-edge-rel : (𝓑 : displayed-refl-graph 𝓤 𝓥 𝓣 𝓦 𝓐)
                    → {x y : ⊰ 𝓐 ⊱} (p : x ≈⟨ 𝓐 ⟩ y) → ⊲ 𝓑 ⊳ x → ⊲ 𝓑 ⊳ y → 𝓦 ̇
 displayed-edge-rel (_ , R , _) = R

 syntax displayed-edge-rel 𝓑 p u v = u ≈≺ 𝓑 , p ≻ v

 𝓻𝓭 : (𝓑 : displayed-refl-graph 𝓤 𝓥 𝓣 𝓦 𝓐) {x : ⊰ 𝓐 ⊱} { u : ⊲ 𝓑 ⊳ x}
    → u ≈≺ 𝓑 , 𝓻 𝓐 ≻ u 
 𝓻𝓭 (_ , _ , r) = r
 

\end{code}
