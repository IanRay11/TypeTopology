Ian Ray. 28th August 2025.

We provide some basic contructions on (displayed) reflexive graphs (see
Sterling, Ulrik, etc.)

TODO. Consider a nice syntax for these basic constructions in line with
Sterling.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module DURGs.BasicConstructionsonReflexiveGraphs where

open import MLTT.Spartan
open import DURGs.DisplayedReflexiveGraphs
open import DURGs.ReflexiveGraphs
open import UF.Powerset-MultiUniverse
open import UF.UniverseEmbedding

\end{code}

Given a reflexive graph and a displayed reflexive graph over it we can define
the total reflexive graph as follows.

\begin{code}

total-refl-graph : (𝓐 : refl-graph 𝓤 𝓥)
                 → displayed-refl-graph 𝓣 𝓦 𝓐
                 → refl-graph (𝓤 ⊔ 𝓣) (𝓥 ⊔ 𝓦)
total-refl-graph {𝓤} {𝓥} {𝓣} {𝓦} 𝓐 𝓑 = ((Σ x ꞉ ⊰ 𝓐 ⊱ , [ 𝓑 ] x) , I , II)
 where
  I : Σ x ꞉ ⊰ 𝓐 ⊱ , [ 𝓑 ] x
    → Σ x ꞉ ⊰ 𝓐 ⊱ , [ 𝓑 ] x
    → 𝓥 ⊔ 𝓦 ̇
  I (a , b) (a' , b') = Σ p ꞉ a ≈⟨ 𝓐 ⟩ a' , b ≈＜ 𝓑 , p ＞ b'
  II : (t : Σ x ꞉ ⊰ 𝓐 ⊱ , [ 𝓑 ] x)
     → I t t
  II (a , b) = (𝓻 𝓐 a , 𝓻𝓭 𝓑 b)

syntax total-refl-graph 𝓐 𝓑 = 𝓐 ﹐ 𝓑

\end{code}

We define the projection map from the total reflexive graph to the base
reflexive graph.

\begin{code}

proj-refl-graph : (𝓐 : refl-graph 𝓤 𝓥) (𝓑 : displayed-refl-graph 𝓣 𝓦 𝓐)
                → refl-graph-hom (𝓐 ﹐ 𝓑) 𝓐
proj-refl-graph 𝓐 𝓑 = (pr₁ , (λ t t' → pr₁) , ∼-refl)

\end{code}

We define the binary product of reflexive graphs as follows.

\begin{code}

binary-prod-refl-graph : refl-graph 𝓤 𝓥
                       → refl-graph 𝓤' 𝓥'
                       → refl-graph (𝓤 ⊔ 𝓤') (𝓥 ⊔ 𝓥')
binary-prod-refl-graph {𝓤} {𝓥} {𝓤'} {𝓥'} 𝓐 𝓐' = ((⊰ 𝓐 ⊱ × ⊰ 𝓐' ⊱) , I , II)
 where
  I : ⊰ 𝓐 ⊱ × ⊰ 𝓐' ⊱ → ⊰ 𝓐 ⊱ × ⊰ 𝓐' ⊱ → 𝓥 ⊔ 𝓥' ̇
  I (x , x') (y , y') = (x ≈⟨ 𝓐 ⟩ y) × (x' ≈⟨ 𝓐' ⟩ y')
  II : (t : ⊰ 𝓐 ⊱ × ⊰ 𝓐' ⊱) → I t t
  II (x , x') = (𝓻 𝓐 x , 𝓻 𝓐' x')

syntax binary-prod-refl-graph 𝓐 𝓐' = 𝓐 ⊗ 𝓐' 

\end{code}

Of course, we can generalize to products of reflexive graphs as follows.

\begin{code}

prod-refl-graphs : (A : 𝓤' ̇)
                 → (A → refl-graph 𝓤 𝓥)
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

syntax prod-refl-graphs A 𝓑 = ∏ A , 𝓑

\end{code}

We define the 'coproduct' of reflexive graphs in terms of sigma types.

\begin{code}

coprod-refl-graphs : (A : 𝓤' ̇)
                   → (A → refl-graph 𝓤 𝓥)
                   → refl-graph (𝓤' ⊔ 𝓤) (𝓤' ⊔ 𝓥)
coprod-refl-graphs {𝓤'} {𝓤} {𝓥} A 𝓑
 = ((Σ x ꞉ A , ⊰ 𝓑 x ⊱) , I , II)
 where
  I : Σ x ꞉ A , ⊰ 𝓑 x ⊱
    → Σ x ꞉ A , ⊰ 𝓑 x ⊱
    → 𝓤' ⊔ 𝓥 ̇
  I (a , b) (a' , b')
   = Σ p ꞉ a ＝ a' , transport (λ - → ⊰ 𝓑 - ⊱) p b ≈⟨ 𝓑 a' ⟩ b'
  II : (t : Σ x ꞉ A , ⊰ 𝓑 x ⊱) → I t t
  II (a , b) = (refl , 𝓻 (𝓑 a) b)

syntax coprod-refl-graphs A 𝓑 = ∐ A , 𝓑

\end{code}

The tensor and cotensor of reflexive graphs can be defined in terms of product
and coproduct.

\begin{code}

tensor-refl-graph : 𝓤' ̇
                  → refl-graph 𝓤 𝓥
                  → refl-graph (𝓤' ⊔ 𝓤) (𝓤' ⊔ 𝓥)
tensor-refl-graph A B = ∏ A , (λ - → B)

cotensor-refl-graph : 𝓤' ̇
                    → refl-graph 𝓤 𝓥
                    → refl-graph (𝓤' ⊔ 𝓤) (𝓤' ⊔ 𝓥)
cotensor-refl-graph A B = ∐ A , (λ - → B)

\end{code}

We have a canonical discrete reflexive graph given by the identity type.
On the other end of the extreme we can define codiscrete reflexive graph.

\begin{code}

discrete-reflexive-graph : 𝓤 ̇
                         → refl-graph 𝓤 𝓤
discrete-reflexive-graph A = (A , _＝_ , ∼-refl)

codiscrete-reflexive-graph : 𝓤 ̇
                           → refl-graph 𝓤 𝓤
codiscrete-reflexive-graph A = (A , (λ - → λ - → 𝟙) , λ - → ⋆)

\end{code}

We can give the constant displayed reflexive graph.

\begin{code}

constant-displayed-reflexive-graph : (𝓐 : refl-graph 𝓤 𝓥)
                                   → refl-graph 𝓤' 𝓥'
                                   → displayed-refl-graph 𝓤' 𝓥' 𝓐
constant-displayed-reflexive-graph {𝓤} {𝓥} {𝓤'} {𝓥'} 𝓐 𝓑 = (I , II , 𝓻 𝓑)
 where
  I : ⊰ 𝓐 ⊱ → 𝓤' ̇
  I x = ⊰ 𝓑 ⊱
  II : {x y : ⊰ 𝓐 ⊱} → edge-rel 𝓐 x y → ⊰ 𝓑 ⊱ → ⊰ 𝓑 ⊱ → 𝓥' ̇
  II _ u v = u ≈⟨ 𝓑 ⟩ v

syntax constant-displayed-reflexive-graph 𝓐 𝓑 = 𝓐 * 𝓑

private
 observation0 : (𝓐 : refl-graph 𝓤 𝓥) (𝓑 : refl-graph 𝓤' 𝓥')
              → (x : ⊰ 𝓐 ⊱)
              → ⋖ 𝓐 * 𝓑 ⋗ x ＝ 𝓑 
 observation0 𝓐 𝓑 x = refl

 observation1 : (𝓐 : refl-graph 𝓤 𝓥) (𝓑 : refl-graph 𝓤' 𝓥')
              → 𝓐 ﹐ (𝓐 * 𝓑) ＝ 𝓐 ⊗ 𝓑
 observation1 𝓐 𝓑 = refl

\end{code}

We can give a reflexive-graph structure to subsets.

\begin{code}

sub-refl-graph : (𝓐 : refl-graph 𝓤 𝓥) 
               → 𝓟 {𝓣} ⊰ 𝓐 ⊱
               → refl-graph (𝓤 ⊔ 𝓣) 𝓥
sub-refl-graph {𝓤} {𝓥} {𝓣} 𝓐 S = (𝕋 S , I , II)
 where
  I : 𝕋 S → 𝕋 S → 𝓥 ̇
  I (x , _) (y , _) = x ≈⟨ 𝓐 ⟩ y
  II : (p : 𝕋 S) → I p p
  II (x , _) = 𝓻 𝓐 x

syntax sub-refl-graph 𝓐 S = x ∶ 𝓐 ∣ S x

\end{code}

We can give opposite constructions for (displayed) reflexive graphs.

\begin{code}

opposite-refl-graph : (refl-graph 𝓤 𝓥)
                    → refl-graph 𝓤 𝓥
opposite-refl-graph {𝓤} {𝓥} 𝓐 = (⊰ 𝓐 ⊱ , I , 𝓻 𝓐)
 where
  I : ⊰ 𝓐 ⊱ → ⊰ 𝓐 ⊱ → 𝓥 ̇
  I x y = y ≈⟨ 𝓐 ⟩ x

syntax opposite-refl-graph 𝓐 = 𝓐 ᵒᵖ

private
 observation2 : (𝓐 : refl-graph 𝓤 𝓥)
              → (𝓐 ᵒᵖ) ᵒᵖ ＝ 𝓐
 observation2 𝓐 = refl

opposite-displayed-refl-graph
 : (𝓐 : refl-graph 𝓤 𝓥)
 → displayed-refl-graph 𝓣 𝓦 𝓐
 → displayed-refl-graph 𝓣 𝓦 (opposite-refl-graph 𝓐)
opposite-displayed-refl-graph {_} {_} {_} {𝓦} 𝓐 𝓑 = ([ 𝓑 ] , I , 𝓻𝓭 𝓑)
 where
  I : {x y : ⊰ 𝓐 ⊱} (p : x ≈⟨ opposite-refl-graph 𝓐 ⟩ y)
    → [ 𝓑 ] x → [ 𝓑 ] y → 𝓦 ̇
  I p u v = v ≈＜ 𝓑 , p ＞ u

syntax opposite-displayed-refl-graph 𝓐 𝓑 = 𝓑 ⟨ 𝓐 ⟩ ᵒᵖ

private
 observation3
  : (𝓐 : refl-graph 𝓤 𝓥) (𝓑 : displayed-refl-graph 𝓣 𝓦 𝓐)
  → (𝓑 ⟨ 𝓐 ⟩ ᵒᵖ) ⟨ 𝓐 ᵒᵖ ⟩ ᵒᵖ ＝ 𝓑
 observation3 𝓐 𝓑 = refl

\end{code}

We can iterate displayed reflexive graphs.

\begin{code}

restriction-iterated-displayed-refl-graph
 : {𝓐 : refl-graph 𝓤 𝓥} (𝓑 : displayed-refl-graph 𝓣 𝓦 𝓐)
 → displayed-refl-graph 𝓣 𝓦 (𝓐 ﹐ 𝓑)
 → (x : ⊰ 𝓐 ⊱)
 → displayed-refl-graph 𝓣 𝓦 (⋖ 𝓑 ⋗ x)
restriction-iterated-displayed-refl-graph {𝓤} {𝓥} {𝓣} {𝓦} {𝓐} 𝓑 𝓒 x
 = (I , II , III)
 where
  I : [ 𝓑 ] x → 𝓣 ̇
  I u = [ 𝓒 ] (x , u)
  II : {u v : [ 𝓑 ] x} (p : u ≈＜ 𝓑 , 𝓻 𝓐 x ＞ v)
     → [ 𝓒 ] (x , u) → [ 𝓒 ] (x , v) → 𝓦 ̇
  II p c c' = c ≈＜ 𝓒 , (𝓻 𝓐 x , p) ＞ c'
  III : {u : [ 𝓑 ] x} (c : I u)
      → c ≈＜ 𝓒 , (𝓻 𝓐 x , 𝓻𝓭 𝓑 u) ＞ c
  III c = 𝓻𝓭 𝓒 c

syntax restriction-iterated-displayed-refl-graph 𝓑 𝓒 x = 𝓒 ∣ 𝓑 , x 

\end{code}
