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
open import DURGs.DisplayedReflexiveGraphs
open import DURGs.ReflexiveGraphs

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

contr-cofan-lemma : {𝓐 : refl-graph 𝓤 𝓥} 
                  → ((x : ⊰ 𝓐 ⊱) → is-contr (cofan 𝓐 x))
                  → (x y : ⊰ 𝓐 ⊱)
                  → (p : y ≈⟨ 𝓐 ⟩ x)
                  → (x , 𝓻 𝓐 x) ＝ (y , p)
contr-cofan-lemma {_} {_} {𝓐} cofan-contr x y p = I ∙ II
 where
  I : (x , 𝓻 𝓐 x) ＝ center (cofan-contr x)
  I = centrality (cofan-contr x) (x , 𝓻 𝓐 x) ⁻¹
  II : center (cofan-contr x) ＝ (y , p)
  II = centrality (cofan-contr x) (y , p)

prop-fan-to-cofan : {𝓐 : refl-graph 𝓤 𝓥} 
                  → ((x : ⊰ 𝓐 ⊱) → is-prop (fan 𝓐 x))
                  → ((x : ⊰ 𝓐 ⊱) → is-prop (cofan 𝓐 x))
prop-fan-to-cofan {_} {_} {𝓐} fan-prop x (y , s) (y' , t)
 = I III VI IV VII
 where
  I : (p : y ＝ x) (q : x ＝ y')
      (α : transport (λ - → y ≈⟨ 𝓐 ⟩ -) p (𝓻 𝓐 y) ＝ s)
      (β : transport (λ - → y' ≈⟨ 𝓐 ⟩ -) q t ＝ 𝓻 𝓐 y')
    → (y , s) ＝ (y' , t)
  I refl refl refl refl = refl
  fan-contr : (x' : ⊰ 𝓐 ⊱) → is-contr (fan 𝓐 x')
  fan-contr x' = pointed-props-are-singletons (x' , 𝓻 𝓐 x') (fan-prop x')
  II : (y , 𝓻 𝓐 y) ＝ (x , s)
  II = contr-fan-lemma {_} {_} {𝓐} fan-contr y x s
  III : y ＝ x
  III = pr₁ (from-Σ-＝ II)
  IV : transport (λ - → y ≈⟨ 𝓐 ⟩ -) III (𝓻 𝓐 y) ＝ s
  IV = pr₂ (from-Σ-＝ II)
  V : (x , t) ＝ (y' , 𝓻 𝓐 y')
  V = contr-fan-lemma {_} {_} {𝓐} fan-contr y' x t ⁻¹
  VI : x ＝ y'
  VI = pr₁ (from-Σ-＝ V)
  VII : transport (λ - → y' ≈⟨ 𝓐 ⟩ -) VI t ＝ 𝓻 𝓐 y'
  VII = pr₂ (from-Σ-＝ V)

prop-cofan-to-fan : {𝓐 : refl-graph 𝓤 𝓥} 
                  → ((x : ⊰ 𝓐 ⊱) → is-prop (cofan 𝓐 x))
                  → ((x : ⊰ 𝓐 ⊱) → is-prop (fan 𝓐 x))
prop-cofan-to-fan {_} {_} {𝓐} cofan-prop x (y , s) (y' , t)
 = I III VI IV VII
 where
  I : (p : y ＝ x) (q : x ＝ y')
      (α : transport (λ - → - ≈⟨ 𝓐 ⟩ y) p (𝓻 𝓐 y) ＝ s)
      (β : transport (λ - → - ≈⟨ 𝓐 ⟩ y') q t ＝ 𝓻 𝓐 y')
    → (y , s) ＝ (y' , t)
  I refl refl refl refl = to-Σ-＝ (refl , refl)
  cofan-contr : (x' : ⊰ 𝓐 ⊱) → is-contr (cofan 𝓐 x')
  cofan-contr x' = pointed-props-are-singletons (x' , 𝓻 𝓐 x') (cofan-prop x')
  II : (y , 𝓻 𝓐 y) ＝ (x , s)
  II = contr-cofan-lemma {_} {_} {𝓐} cofan-contr y x s
  III : y ＝ x
  III = pr₁ (from-Σ-＝ II)
  IV : transport (λ - → - ≈⟨ 𝓐 ⟩ y) III (𝓻 𝓐 y) ＝ s
  IV = pr₂ (from-Σ-＝ II)
  V : (x , t) ＝ (y' , 𝓻 𝓐 y')
  V = contr-cofan-lemma {_} {_} {𝓐} cofan-contr y' x t ⁻¹
  VI : x ＝ y'
  VI = pr₁ (from-Σ-＝ V)
  VII : transport (λ - → - ≈⟨ 𝓐 ⟩ y') VI t ＝ 𝓻 𝓐 y'
  VII = pr₂ (from-Σ-＝ V)

contr-fan-to-cofan : {𝓐 : refl-graph 𝓤 𝓥} {x : ⊰ 𝓐 ⊱}
                   → ((x : ⊰ 𝓐 ⊱) → is-contr (fan 𝓐 x))
                   → ((x : ⊰ 𝓐 ⊱) → is-contr (cofan 𝓐 x))
contr-fan-to-cofan {_} {_} {𝓐} contr-fan x
 = pointed-props-are-singletons (x , 𝓻 𝓐 x)
    (prop-fan-to-cofan {_} {_} {𝓐} (λ - → singletons-are-props (contr-fan -)) x)

contr-cofan-to-fan : {𝓐 : refl-graph 𝓤 𝓥} 
                   → ((x : ⊰ 𝓐 ⊱) → is-contr (cofan 𝓐 x))
                   → ((x : ⊰ 𝓐 ⊱) → is-contr (fan 𝓐 x))
contr-cofan-to-fan {_} {_} {𝓐} contr-cofan x
 = pointed-props-are-singletons (x , 𝓻 𝓐 x)
    (prop-cofan-to-fan {_} {_} {𝓐}
     (λ - → singletons-are-props (contr-cofan -)) x)

\end{code}

We give the canonical function from an identification to an edge.

\begin{code}

id-to-edge : (𝓐 : refl-graph 𝓤 𝓥) (x y : ⊰ 𝓐 ⊱)
           → x ＝ y
           → x ≈⟨ 𝓐 ⟩ y
id-to-edge 𝓐 x x refl = 𝓻 𝓐 x

id-to-edge' : (𝓐 : refl-graph 𝓤 𝓥) {x y : ⊰ 𝓐 ⊱}
            → x ＝ y
            → x ≈⟨ 𝓐 ⟩ y
id-to-edge' 𝓐 {x} {y} = id-to-edge 𝓐 x y

\end{code}

We now define univalent reflexive graphs.

\begin{code}

is-univalent-refl-graph : (𝓐 : refl-graph 𝓤 𝓥) → 𝓤 ⊔ 𝓥 ̇ 
is-univalent-refl-graph 𝓐 = (x y : ⊰ 𝓐 ⊱)
                          → is-equiv (id-to-edge 𝓐 x y)

univalent-refl-graph : (𝓤 𝓥 : Universe) → (𝓤 ⁺) ⊔ (𝓥 ⁺) ̇
univalent-refl-graph 𝓤 𝓥 = Σ 𝓐 ꞉ (refl-graph 𝓤 𝓥) , is-univalent-refl-graph 𝓐

\end{code}

We will now record some boiler plate code for univalent reflexive graphs.

\begin{code}

⊰_⊱ᵤ : univalent-refl-graph 𝓤 𝓥 → 𝓤 ̇
⊰ (𝓐 , _) ⊱ᵤ = ⊰ 𝓐 ⊱

edge-relᵤ : (𝓐 : univalent-refl-graph 𝓤 𝓥) → ⊰ 𝓐 ⊱ᵤ → ⊰ 𝓐 ⊱ᵤ → 𝓥 ̇
edge-relᵤ (𝓐 , _) = edge-rel 𝓐

syntax edge-relᵤ 𝓐 x y = x ≈ᵤ⟨ 𝓐 ⟩ y

𝓻ᵤ : (𝓐 : univalent-refl-graph 𝓤 𝓥) → (x : ⊰ 𝓐 ⊱ᵤ) → x ≈ᵤ⟨ 𝓐 ⟩ x
𝓻ᵤ (𝓐 , _) x = 𝓻 𝓐 x

underlying-refl-graph : (𝓐 : univalent-refl-graph 𝓤 𝓥)
                      → refl-graph 𝓤 𝓥
underlying-refl-graph (𝓐 , _) = 𝓐

is-univalent : (𝓐 : univalent-refl-graph 𝓤 𝓥)
              → is-univalent-refl-graph (underlying-refl-graph 𝓐)
is-univalent (𝓐 , is-ua) = is-ua

id-equiv-edge : (𝓐 : univalent-refl-graph 𝓤 𝓥)
              → (x y : ⊰ 𝓐 ⊱ᵤ)
              → (x ＝ y) ≃ (x ≈ᵤ⟨ 𝓐 ⟩ y)
id-equiv-edge 𝓐 x y
 = (id-to-edge (underlying-refl-graph 𝓐) x y , is-univalent 𝓐 x y)

edge-to-id : (𝓐 : univalent-refl-graph 𝓤 𝓥)
           → (x y : ⊰ 𝓐 ⊱ᵤ)
           → x ≈ᵤ⟨ 𝓐 ⟩ y
           → x ＝ y
edge-to-id 𝓐 x y = ⌜ id-equiv-edge 𝓐 x y ⌝⁻¹

edge-to-id' : (𝓐 : univalent-refl-graph 𝓤 𝓥) {x y : ⊰ 𝓐 ⊱ᵤ}
            → x ≈ᵤ⟨ 𝓐 ⟩ y
            → x ＝ y
edge-to-id' 𝓐 {x} {y} = edge-to-id 𝓐 x y

\end{code}
