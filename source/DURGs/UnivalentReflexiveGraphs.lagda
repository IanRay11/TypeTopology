Ian Ray. 2nd September 2025.

We provide some equivalent descriptions of univalent reflexive graphs (see
Sterling, Ulrik, etc.)


\begin{code}

{-# OPTIONS --safe --without-K #-}

module DURGs.UnivalentReflexiveGraphs where

open import MLTT.Spartan
open import UF.Base
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
contr-fan-lemma {_} {_} {𝓐} fan-contr x y p = I ∙ II
 where
  I : (x , 𝓻 𝓐 x) ＝ center (fan-contr x)
  I = centrality (fan-contr x) (x , 𝓻 𝓐 x) ⁻¹
  II : center (fan-contr x) ＝ (y , p)
  II = centrality (fan-contr x) (y , p)

prop-fan-to-cofan : {𝓐 : refl-graph 𝓤 𝓥} 
                  → ((x : ⊰ 𝓐 ⊱) → is-prop (fan 𝓐 x))
                  → ((x : ⊰ 𝓐 ⊱) → is-prop (cofan 𝓐 x))
prop-fan-to-cofan {_} {_} {𝓐} fan-prop x (y , p) (y' , q)
 = to-Σ-＝ ((II ∙ V) , VII)
 where
  fan-contr : (x' : ⊰ 𝓐 ⊱) → is-contr (fan 𝓐 x')
  fan-contr x' = pointed-props-are-singletons (x' , 𝓻 𝓐 x') (fan-prop x')
  I : (y , 𝓻 𝓐 y) ＝ (x , p)
  I = contr-fan-lemma fan-contr y x p
  II : y ＝ x
  II = pr₁ (from-Σ-＝ I)
  III : transport (λ - → y ≈⟨ 𝓐 ⟩ -) II (𝓻 𝓐 y) ＝ p
  III = pr₂ (from-Σ-＝ I)
  IV : (x , q) ＝ (y' , 𝓻 𝓐 y')
  IV = contr-fan-lemma fan-contr y' x q ⁻¹
  V : x ＝ y'
  V = pr₁ (from-Σ-＝ IV)
  VI : transport (λ - → y' ≈⟨ 𝓐 ⟩ -) V q ＝ 𝓻 𝓐 y'
  VI = pr₂ (from-Σ-＝ IV)
  fam = λ - → - ≈⟨ 𝓐 ⟩ x
  VII : transport fam (II ∙ V) p ＝ q
  VII = transport fam (II ∙ V) p              ＝⟨ {!!} ⟩
        transport fam V (transport fam II p)  ＝⟨ {!!} ⟩
        transport fam V (𝓻 𝓐 x)               ＝⟨ {!!} ⟩
        q                                     ∎  

prop-cofan-to-fan : {𝓐 : refl-graph 𝓤 𝓥} 
                  → ((x : ⊰ 𝓐 ⊱) → is-prop (cofan 𝓐 x))
                  → ((x : ⊰ 𝓐 ⊱) → is-prop (fan 𝓐 x))
prop-cofan-to-fan = {!!}

contr-fan-to-cofan : {𝓐 : refl-graph 𝓤 𝓥} {x : ⊰ 𝓐 ⊱}
                   → ((x : ⊰ 𝓐 ⊱) → is-contr (fan 𝓐 x))
                   → ((x : ⊰ 𝓐 ⊱) → is-contr (cofan 𝓐 x))
contr-fan-to-cofan {_} {_} {𝓐} contr-fan x
 = pointed-props-are-singletons (x , 𝓻 𝓐 x)
    (prop-fan-to-cofan (λ - → singletons-are-props (contr-fan -)) x)

contr-cofan-to-fan : {𝓐 : refl-graph 𝓤 𝓥} 
                   → ((x : ⊰ 𝓐 ⊱) → is-contr (cofan 𝓐 x))
                   → ((x : ⊰ 𝓐 ⊱) → is-contr (fan 𝓐 x))
contr-cofan-to-fan {_} {_} {𝓐} contr-cofan x
 = pointed-props-are-singletons (x , 𝓻 𝓐 x)
    (prop-cofan-to-fan (λ - → singletons-are-props (contr-cofan -)) x)

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
