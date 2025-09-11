\begin{code}

{-# OPTIONS --safe --without-K #-}

module DURGs.PathAlgebraToolkit where

open import MLTT.Spartan
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

concat-helper : (𝓐 : univalent-refl-graph 𝓤 𝓥) {x y z : ⊰ 𝓐 ⊱ᵤ}
              → (p : x ≈ᵤ⟨ 𝓐 ⟩ y)
              → y ≈ᵤ⟨ 𝓐 ⟩ z
              → (x , 𝓻ᵤ 𝓐 x) ＝ (y , p)
              → x ≈ᵤ⟨ 𝓐 ⟩ z
concat-helper 𝓐 p q refl = q

concat-edges : (𝓐 : univalent-refl-graph 𝓤 𝓥) {x y z : ⊰ 𝓐 ⊱ᵤ}
             → x ≈ᵤ⟨ 𝓐 ⟩ y
             → y ≈ᵤ⟨ 𝓐 ⟩ z
             → x ≈ᵤ⟨ 𝓐 ⟩ z
concat-edges 𝓐 {x} {y} {z} p q
 = concat-helper 𝓐 p q (I x (x , 𝓻ᵤ 𝓐 x) (y , p))
 module edge-comp where
  I : (x : ⊰ 𝓐 ⊱ᵤ) → is-prop (fan (underlying-refl-graph 𝓐) x)
  I x = id-to-edge-equiv-implies-prop-fans (is-univalent 𝓐) x

syntax concat-edges 𝓐 p q = p ∙ᵤ⟨ 𝓐 ⟩ q

inverse-edge : {𝓐 : univalent-refl-graph 𝓤 𝓥} {x y : ⊰ 𝓐 ⊱ᵤ}
             → x ≈ᵤ⟨ 𝓐 ⟩ y
             → y ≈ᵤ⟨ 𝓐 ⟩ x
inverse-edge {_} {_} {𝓐} {x} {y} p = II p (I x (x , 𝓻ᵤ 𝓐 x) (y , p))
 where
  I : (x : ⊰ 𝓐 ⊱ᵤ) → is-prop (fan (underlying-refl-graph 𝓐) x)
  I x = id-to-edge-equiv-implies-prop-fans (is-univalent 𝓐) x
  II : (p : x ≈ᵤ⟨ 𝓐 ⟩ y)
     → (x , 𝓻ᵤ 𝓐 x) ＝ (y , p)
     → y ≈ᵤ⟨ 𝓐 ⟩ x
  II p refl = 𝓻ᵤ 𝓐 x

syntax inverse-edge p = p ᵤ⁻¹

\end{code}

Computation lemmas

\begin{code}

concat-on-𝓻 : {𝓐 : univalent-refl-graph 𝓤 𝓥} (x : ⊰ 𝓐 ⊱ᵤ)
            → 𝓻ᵤ 𝓐 x ∙ᵤ⟨ 𝓐 ⟩ 𝓻ᵤ 𝓐 x ＝ 𝓻ᵤ 𝓐 x
concat-on-𝓻 {_} {_} {𝓐} x
 = transport (λ - → concat-helper {!!} {!!} {!!} {!!}) (II x) {!!}
 where
  I : (x : ⊰ 𝓐 ⊱ᵤ) → is-prop (fan (underlying-refl-graph 𝓐) x)
  I x = id-to-edge-equiv-implies-prop-fans (is-univalent 𝓐) x
  II : (x : ⊰ 𝓐 ⊱ᵤ) → refl ＝ I x (x , 𝓻ᵤ 𝓐 x) (x , 𝓻ᵤ 𝓐 x) 
  II x = props-are-sets (I x) refl (I x (x , 𝓻ᵤ 𝓐 x) (x , 𝓻ᵤ 𝓐 x)) 

\end{code}

We will record unit, symmetry and associativity laws.

\begin{code}

r-unit-edges : {𝓐 : univalent-refl-graph 𝓤 𝓥} {x y : ⊰ 𝓐 ⊱ᵤ}
             → (p : x ≈ᵤ⟨ 𝓐 ⟩ y)
             → 𝓻ᵤ 𝓐 x ∙ᵤ⟨ 𝓐 ⟩ p ＝ p
r-unit-edges {𝓤} {𝓥} {𝓐} {x} {y} p
 = II p (I x (x , 𝓻ᵤ 𝓐 x) (y , p))
 where
  I : (x : ⊰ 𝓐 ⊱ᵤ) → is-prop (fan (underlying-refl-graph 𝓐) x)
  I x = id-to-edge-equiv-implies-prop-fans (is-univalent 𝓐) x
  II : (p : x ≈ᵤ⟨ 𝓐 ⟩ y)
     → (x , 𝓻ᵤ 𝓐 x) ＝ (y , p)
     → 𝓻ᵤ 𝓐 x ∙ᵤ⟨ 𝓐 ⟩ p ＝ p
  II p q = ?

l-unit-edges : {𝓐 : univalent-refl-graph 𝓤 𝓥} {x y : ⊰ 𝓐 ⊱ᵤ}
             → (p : x ≈ᵤ⟨ 𝓐 ⟩ y)
             → p ∙ᵤ⟨ 𝓐 ⟩ 𝓻ᵤ 𝓐 y ＝ p
l-unit-edges p = {!!}

\end{code}
