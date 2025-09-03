Ian Ray. 2nd September 2025.

We provide some equivalent descriptions of univalent reflexive graphs (see
Sterling, Ulrik, etc.)


\begin{code}

{-# OPTIONS --safe --without-K #-}

module DURGs.UnivalentReflexiveGraphs where

open import MLTT.Spartan
open import UF.Equiv
open import UF.Subsingletons
open import DURGs.ReflexiveGraphs
open import DURGs.DisplayedReflexiveGraphs

fan : (𝓐 : refl-graph 𝓤 𝓥)
    →  ⊰ 𝓐 ⊱
    → 𝓤 ⊔ 𝓥 ̇ 
fan 𝓐 x = Σ y ꞉ ⊰ 𝓐 ⊱ , x ≈⟨ 𝓐 ⟩ y

cofan : (𝓐 : refl-graph 𝓤 𝓥)
      → ⊰ 𝓐 ⊱
      → 𝓤 ⊔ 𝓥 ̇ 
cofan 𝓐 x = Σ y ꞉ ⊰ 𝓐 ⊱ , y ≈⟨ 𝓐 ⟩ x

contr-fan-lemma : {𝓐 : refl-graph 𝓤 𝓥} 
                → ((x : ⊰ 𝓐 ⊱) → is-contr (fan 𝓐 x))
                → (x y : ⊰ 𝓐 ⊱)
                → (p : x ≈⟨ 𝓐 ⟩ y)
                → (x , 𝓻 𝓐 x) ＝ (y , p)
contr-fan-lemma {𝓤} {𝓥} {𝓐} fan-contr x y p = I ∙ II
 where
  I : (x , 𝓻 𝓐 x) ＝ center (fan-contr x)
  I = centrality (fan-contr x) (x , 𝓻 𝓐 x) ⁻¹
  II : center (fan-contr x) ＝ (y , p)
  II = centrality (fan-contr x) (y , p)

contr-fan-lemma' : {𝓐 : refl-graph 𝓤 𝓥}
                 → ((x : ⊰ 𝓐 ⊱) → is-contr (fan 𝓐 x))
                 → (x y : ⊰ 𝓐 ⊱)
                 → (p : x ≈⟨ 𝓐 ⟩ y)
                 → (P : (fan 𝓐 x) → 𝓣 ̇)
                 → P (x , 𝓻 𝓐 x)
                 → P (y , p)
contr-fan-lemma' fan-contr x y p P
 = transport P (contr-fan-lemma fan-contr x y p)

prop-fan-to-cofan : {𝓐 : refl-graph 𝓤 𝓥} 
                  → ((x : ⊰ 𝓐 ⊱) → is-prop (fan 𝓐 x))
                  → ((x : ⊰ 𝓐 ⊱) → is-prop (cofan 𝓐 x))
prop-fan-to-cofan {_} {_} {𝓐} fan-prop x (y , p) (y' , q)
 = contr-fan-lemma' fan-contr {!!} {!!} {!!} {!!} {!!}
 where
  fan-contr : (x' : ⊰ 𝓐 ⊱) → is-contr (fan 𝓐 x')
  fan-contr x' = pointed-props-are-singletons (x' , 𝓻 𝓐 x') (fan-prop x')

prop-cofan-to-fan : {𝓐 : refl-graph 𝓤 𝓥} 
                  → ((x : ⊰ 𝓐 ⊱) → is-prop (cofan 𝓐 x))
                  → ((x : ⊰ 𝓐 ⊱) → is-prop (fan 𝓐 x))
prop-cofan-to-fan = {!!}

contr-fan-to-cofan : {𝓐 : refl-graph 𝓤 𝓥} {x : ⊰ 𝓐 ⊱}
                   → is-contr (fan 𝓐 x)
                   → is-contr (cofan 𝓐 x)
contr-fan-to-cofan {_} {_} {𝓐} {x} ((y , e) , C)
 = pointed-props-are-singletons (x , 𝓻 𝓐 x) {!!}

contr-cofan-to-fan : {𝓐 : refl-graph 𝓤 𝓥} {x : ⊰ 𝓐 ⊱}
                   → is-contr (cofan 𝓐 x)
                   → is-contr (fan 𝓐 x)
contr-cofan-to-fan ((y , e) , C) = {!!}

contr-fan-iff-cofan : {𝓐 : refl-graph 𝓤 𝓥} {x : ⊰ 𝓐 ⊱}
                    → is-contr (fan 𝓐 x)
                    ↔ is-contr (cofan 𝓐 x)
contr-fan-iff-cofan = (contr-fan-to-cofan , contr-cofan-to-fan)

\end{code}

We give the canonical function from an identification to an edge.

\begin{code}

id-to-edge : (𝓐 : refl-graph 𝓤 𝓥) (x y : ⊰ 𝓐 ⊱)
           → x ＝ y
           → x ≈⟨ 𝓐 ⟩ y
id-to-edge 𝓐 x x refl = 𝓻 𝓐 x

\end{code}

We now define univalent reflexive graphs.

\begin{code}

is-univalent-refl-graph : (𝓐 : refl-graph 𝓤 𝓥) → 𝓤 ⊔ 𝓥 ̇ 
is-univalent-refl-graph 𝓐 = (x y : ⊰ 𝓐 ⊱)
                          → is-equiv (id-to-edge 𝓐 x y)

univalent-refl-graph : (𝓤 𝓥 : Universe) → (𝓤 ⁺) ⊔ (𝓥 ⁺) ̇
univalent-refl-graph 𝓤 𝓥 = Σ 𝓐 ꞉ (refl-graph 𝓤 𝓥) , is-univalent-refl-graph 𝓐


\end{code}
