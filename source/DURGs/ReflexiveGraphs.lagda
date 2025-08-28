Ian Ray. 28th August 2025.

We define reflexive graphs (see Sterling, Ulrik, etc.)

\begin{code}

{-# OPTIONS --safe --without-K #-}

module DURGs.ReflexiveGraphs where

open import MLTT.Spartan

module _ (𝓤 𝓥 : Universe) where

 refl-graph : (𝓤 ⊔ 𝓥) ⁺  ̇
 refl-graph = Σ A ꞉ 𝓤 ̇ , Σ R ꞉ (A → A → 𝓥 ̇) , ((x : A) → R x x)

\end{code}

We give some boiler plate

\begin{code}

⊰_⊱ : refl-graph 𝓤 𝓥 → 𝓤 ̇
⊰ (A , _) ⊱ = A

edge-rel : (𝓐 : refl-graph 𝓤 𝓥) → ⊰ 𝓐 ⊱ → ⊰ 𝓐 ⊱ → 𝓥 ̇
edge-rel (_ , R , _) = R

syntax edge-rel 𝓐 x y = x ≈⟨ 𝓐 ⟩ y

𝓻 : (𝓐 : refl-graph 𝓤 𝓥) → {x : ⊰ 𝓐 ⊱} → x ≈⟨ 𝓐 ⟩ x
𝓻 (_ , _ , r) {x} = r x

\end{code}
