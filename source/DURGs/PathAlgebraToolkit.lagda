\begin{code}

{-# OPTIONS --safe --without-K #-}

module DURGs.PathAlgebraToolkit where

open import MLTT.Spartan
open import UF.Base
open import UF.Equiv
open import UF.Subsingletons
open import UF.Subsingletons-Properties
open import DURGs.BasicConstructionsonReflexiveGraphs
open import DURGs.DisplayedReflexiveGraphs
open import DURGs.DisplayedUnivalentReflexiveGraphs
open import DURGs.ReflexiveGraphs
open import DURGs.UnivalentReflexiveGraphs

\end{code}

When reflexive graphs are univalent they natrually inherit many of the
familiar results we have for identifications. We do not exhaust all of these
results but we will record some of the obvious ones.

We begin with concatenation and inverse of edges.

\begin{code}

concat-edges : (𝓐 : univalent-refl-graph 𝓤 𝓥) {x y z : ⊰ 𝓐 ⊱ᵤ}
             → x ≈ᵤ⟨ 𝓐 ⟩ y
             → y ≈ᵤ⟨ 𝓐 ⟩ z
             → x ≈ᵤ⟨ 𝓐 ⟩ z
concat-edges 𝓐 {x} {y} {z} p q
 = id-to-edge' (𝓐 /ᵤ) (edge-to-id' 𝓐 p ∙ edge-to-id' 𝓐 q)

syntax concat-edges 𝓐 p q = p ∙ᵤ⟨ 𝓐 ⟩ q

inverse-edge : (𝓐 : univalent-refl-graph 𝓤 𝓥) {x y : ⊰ 𝓐 ⊱ᵤ}
             → x ≈ᵤ⟨ 𝓐 ⟩ y
             → y ≈ᵤ⟨ 𝓐 ⟩ x
inverse-edge 𝓐 {x} {y} p
 = id-to-edge' (𝓐 /ᵤ) (edge-to-id' 𝓐 p ⁻¹)

syntax inverse-edge 𝓐 p = p ᵤ⟨ 𝓐 ⟩ ⁻¹

\end{code}

We will record unit, symmetry and associativity laws.

\begin{code}

l-unit-edges : {𝓐 : univalent-refl-graph 𝓤 𝓥} {x y : ⊰ 𝓐 ⊱ᵤ}
             → (p : x ≈ᵤ⟨ 𝓐 ⟩ y)
             → 𝓻ᵤ 𝓐 x ∙ᵤ⟨ 𝓐 ⟩ p ＝ p
l-unit-edges {𝓤} {𝓥} {𝓐} {x} {y} p
 = id-to-edge' (𝓐 /ᵤ) (edge-to-id' 𝓐 (𝓻ᵤ 𝓐 x) ∙ edge-to-id' 𝓐 p) ＝⟨ I ⟩
   id-to-edge' (𝓐 /ᵤ) (refl ∙ edge-to-id' 𝓐 p)                   ＝⟨ II ⟩
   id-to-edge' (𝓐 /ᵤ) (edge-to-id' 𝓐 p)                          ＝⟨ III ⟩
   p                                                             ∎
 where
  I = ap (λ - → id-to-edge' (𝓐 /ᵤ) (- ∙ edge-to-id' 𝓐 p)) (edge-to-id-comp 𝓐)
  II = ap (id-to-edge' (𝓐 /ᵤ)) {refl ∙ edge-to-id' 𝓐 p} {edge-to-id' 𝓐 p}
        refl-left-neutral
  III = inverses-are-sections (id-to-edge' (𝓐 /ᵤ)) (is-univalent 𝓐 x y) p
   
r-unit-edges : {𝓐 : univalent-refl-graph 𝓤 𝓥} {x y : ⊰ 𝓐 ⊱ᵤ}
             → (p : x ≈ᵤ⟨ 𝓐 ⟩ y)
             → p ∙ᵤ⟨ 𝓐 ⟩ 𝓻ᵤ 𝓐 y ＝ p
r-unit-edges {𝓤} {𝓥} {𝓐} {x} {y} p
 = id-to-edge' (𝓐 /ᵤ) (edge-to-id' 𝓐 p ∙ edge-to-id' 𝓐 (𝓻ᵤ 𝓐 y)) ＝⟨ I ⟩
   id-to-edge' (𝓐 /ᵤ) (edge-to-id' 𝓐 p)                          ＝⟨ II ⟩
   p                                                             ∎
 where
  I = ap (λ - → id-to-edge' (𝓐 /ᵤ) (edge-to-id' 𝓐 p ∙ -)) (edge-to-id-comp 𝓐)
  II = inverses-are-sections (id-to-edge' (𝓐 /ᵤ)) (is-univalent 𝓐 x y) p

l-sym-edges : {𝓐 : univalent-refl-graph 𝓤 𝓥} {x y : ⊰ 𝓐 ⊱ᵤ}
            → (p : x ≈ᵤ⟨ 𝓐 ⟩ y)
            → (p ᵤ⟨ 𝓐 ⟩ ⁻¹) ∙ᵤ⟨ 𝓐 ⟩ p ＝ 𝓻ᵤ 𝓐 y
l-sym-edges {_} {_} {𝓐} {x} {y} p
 = id-to-edge' (𝓐 /ᵤ) (edge-to-id' 𝓐 (p ᵤ⟨ 𝓐 ⟩ ⁻¹) ∙ edge-to-id' 𝓐 p) ＝⟨ II ⟩
   id-to-edge' (𝓐 /ᵤ) (edge-to-id' 𝓐 p ⁻¹ ∙ edge-to-id' 𝓐 p)          ＝⟨ III ⟩
   id-to-edge' (𝓐 /ᵤ) refl                                            ＝⟨ refl ⟩
   𝓻ᵤ 𝓐 y                                                             ∎ 
 where
  I : edge-to-id' 𝓐 (id-to-edge' (𝓐 /ᵤ) (edge-to-id' 𝓐 p ⁻¹))
    ＝ edge-to-id' 𝓐 p ⁻¹
  I = inverses-are-retractions (id-to-edge' (𝓐 /ᵤ)) (is-univalent 𝓐 y x)
       (edge-to-id' 𝓐 p ⁻¹)
  II = ap (λ - → id-to-edge' (𝓐 /ᵤ) (- ∙ edge-to-id' 𝓐 p)) I
  III = ap (id-to-edge' (𝓐 /ᵤ)) (left-inverse (edge-to-id' 𝓐 p))

r-sym-edges : {𝓐 : univalent-refl-graph 𝓤 𝓥} {x y : ⊰ 𝓐 ⊱ᵤ}
            → (p : x ≈ᵤ⟨ 𝓐 ⟩ y)
            → p ∙ᵤ⟨ 𝓐 ⟩ (p ᵤ⟨ 𝓐 ⟩ ⁻¹) ＝ 𝓻ᵤ 𝓐 x
r-sym-edges {_} {_} {𝓐} {x} {y} p
 = id-to-edge' (𝓐 /ᵤ) (edge-to-id' 𝓐 p ∙ edge-to-id' 𝓐 (p ᵤ⟨ 𝓐 ⟩ ⁻¹)) ＝⟨ II ⟩
   id-to-edge' (𝓐 /ᵤ) (edge-to-id' 𝓐 p ∙ edge-to-id' 𝓐 p ⁻¹)          ＝⟨ III ⟩
   id-to-edge' (𝓐 /ᵤ) refl                                            ＝⟨ refl ⟩
   𝓻ᵤ 𝓐 x                                                             ∎ 
 where
  I : edge-to-id' 𝓐 (id-to-edge' (𝓐 /ᵤ) (edge-to-id' 𝓐 p ⁻¹))
    ＝ edge-to-id' 𝓐 p ⁻¹
  I = inverses-are-retractions (id-to-edge' (𝓐 /ᵤ)) (is-univalent 𝓐 y x)
       (edge-to-id' 𝓐 p ⁻¹)
  II = ap (λ - → id-to-edge' (𝓐 /ᵤ) (edge-to-id' 𝓐 p ∙ -)) I
  III = ap (id-to-edge' (𝓐 /ᵤ)) (right-inverse (edge-to-id' 𝓐 p) ⁻¹)

edge-to-id-preserves-edge-comp
 : {𝓐 : univalent-refl-graph 𝓤 𝓥} {x y z : ⊰ 𝓐 ⊱ᵤ}
 → (p : x ≈ᵤ⟨ 𝓐 ⟩ y) (q : y ≈ᵤ⟨ 𝓐 ⟩ z)
 → edge-to-id' 𝓐 (p ∙ᵤ⟨ 𝓐 ⟩ q) ＝ edge-to-id' 𝓐 p ∙ edge-to-id' 𝓐 q
edge-to-id-preserves-edge-comp {_} {_} {𝓐} {x} {y} {z} p q
 = II (I x (x , 𝓻 (𝓐 /ᵤ) x) (y , p))
 where
  I : ((x : ⊰ 𝓐 ⊱ᵤ) → is-prop (fan (𝓐 /ᵤ) x))
  I = id-to-edge-equiv-implies-prop-fans (is-univalent 𝓐)
  II : (x , 𝓻 (𝓐 /ᵤ) x) ＝ (y , p)
     → edge-to-id' 𝓐 (p ∙ᵤ⟨ 𝓐 ⟩ q) ＝ edge-to-id' 𝓐 p ∙ edge-to-id' 𝓐 q
  II refl = edge-to-id' 𝓐 ((𝓻 (𝓐 /ᵤ) x) ∙ᵤ⟨ 𝓐 ⟩ q)       ＝⟨ III ⟩
            edge-to-id' 𝓐 q                              ＝⟨ IV ⟩
            refl ∙ edge-to-id' 𝓐 q                       ＝⟨ V ⟩ 
            edge-to-id' 𝓐 (𝓻 (𝓐 /ᵤ) x) ∙ edge-to-id' 𝓐 q ∎
   where
    III = ap (edge-to-id' 𝓐) (l-unit-edges {_} {_} {𝓐} q)
    IV = refl-left-neutral ⁻¹
    V = ap (λ - → - ∙ edge-to-id' 𝓐 q) (edge-to-id-comp 𝓐 ⁻¹)

assoc-edges : {𝓐 : univalent-refl-graph 𝓤 𝓥} {x y z w : ⊰ 𝓐 ⊱ᵤ}
            → (p : x ≈ᵤ⟨ 𝓐 ⟩ y) (q : y ≈ᵤ⟨ 𝓐 ⟩ z) (r : z ≈ᵤ⟨ 𝓐 ⟩ w)
            → (p ∙ᵤ⟨ 𝓐 ⟩ q) ∙ᵤ⟨ 𝓐 ⟩ r ＝ p ∙ᵤ⟨ 𝓐 ⟩ (q ∙ᵤ⟨ 𝓐 ⟩ r)
assoc-edges {_} {_} {𝓐} {x} {y} {z} {w} p q r
 = I (II (p ∙ᵤ⟨ 𝓐 ⟩ q) ∙ II r) ＝⟨ III ⟩
   I ((II p ∙ II q) ∙ II r)    ＝⟨ ap I (∙assoc (II p) (II q) (II r)) ⟩
   I (II p ∙ (II q ∙ II r))    ＝⟨ IV ⟩
   I (II p ∙ II (q ∙ᵤ⟨ 𝓐 ⟩ r)) ∎
 where
  I = id-to-edge' (𝓐 /ᵤ)
  II = edge-to-id' 𝓐
  III = ap (λ - → I (- ∙ II r)) (edge-to-id-preserves-edge-comp {_} {_} {𝓐} p q)
  IV = ap (λ - → I (II p ∙ -))
        (edge-to-id-preserves-edge-comp {_} {_} {𝓐} q r ⁻¹)

\end{code}
