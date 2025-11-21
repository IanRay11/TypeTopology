Ian Ray. 4th November 2025.

We provide some applications of (displayed) univalent reflexive graphs to
existing identity characterization results. This provides evidence that DURGs
provide a unified framework for developing structured identity principles (SIP).

\begin{code}

{-# OPTIONS --safe --without-K #-}

module DURGs.Examples where

open import MLTT.Spartan
open import UF.Base
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.FunExt
open import UF.Pullback
open import UF.Subsingletons
open import DURGs.BasicConstructionsonReflexiveGraphs
open import DURGs.ClosurePropertiesofUnivalentReflexiveGraphs
open import DURGs.DisplayedReflexiveGraphs
open import DURGs.DisplayedUnivalentReflexiveGraphs
open import DURGs.Lenses
open import DURGs.ReflexiveGraphs
open import DURGs.UnivalentReflexiveGraphs
open import DURGs.UnivalenceProperty

\end{code}

We can recover the standard characterizations of the identity type of products
using reflexive graphs.

\begin{code}

product-characterization-from-univalent-refl-graphs
 : {A : 𝓤 ̇} {B : 𝓥 ̇} {a a' : A} {b b' : B}
 → ((a , b) ＝ (a' , b')) ≃ (a ＝ a') × (b ＝ b')
product-characterization-from-univalent-refl-graphs
 {_} {_} {A} {B} {a} {a'} {b} {b'}
 = (id-to-edge' ((Δ A) ⊗ (Δ B)) , II (a , b) (a' , b'))
 where
  I : is-univalent-refl-graph ((Δ A) ⊗ (Δ B))
  I = univalence-closed-under-binary-product (Δ A) (Δ B)
       (discrete-refl-graph-is-univalent A) (discrete-refl-graph-is-univalent B)
  II : (p q : A × B) → is-equiv (id-to-edge' ((Δ A) ⊗ (Δ B)) {p} {q})
  II = prop-fans-implies-id-to-edge-equiv I

\end{code}

Similarly for Sigma types.

\begin{code}

sigma-characterization-from-univalent-refl-graphs
 : {A : 𝓤 ̇} {B : A → 𝓥 ̇} {a a' : A} {b : B a} {b' : B a'}
 → ((a , b) ＝ (a' , b')) ≃ (Σ p ꞉ (a ＝ a') , transport B p b ＝ b')
sigma-characterization-from-univalent-refl-graphs
 {𝓤} {𝓥} {A} {B} {a} {a'} {b} {b'}
 = (id-to-edge' (∐ A , λ a → Δ (B a)) , II (a , b) (a' , b'))
 where
  I : is-univalent-refl-graph (∐ A , λ a → Δ (B a))
  I = univalence-closed-under-coproduct A (λ a → Δ (B a))
       (λ a → discrete-refl-graph-is-univalent (B a))
  II : (p q : (Σ a ꞉ A , B a))
     → is-equiv (id-to-edge' (∐ A , λ a → Δ (B a)) {p} {q})
  II = prop-fans-implies-id-to-edge-equiv I

\end{code}

Just a reminder: 
Function spaces have univalent reflexive graph structure.

\begin{code}

function-refl-graph : (A : 𝓤 ̇) (B : 𝓥 ̇)
                    → refl-graph (𝓤 ⊔ 𝓥) (𝓤 ⊔ 𝓥)
function-refl-graph A B = ((A → B) , (λ f g → f ∼ g) , λ f → ∼-refl)

function-univalent-refl-graph
 : {A : 𝓤 ̇} {B : 𝓥 ̇}
 → Fun-Ext
 → is-univalent-refl-graph (function-refl-graph A B)
function-univalent-refl-graph {𝓤} {_} {A} {B} fe f
 = univalence-closed-under-cotensor fe A (Δ B)
    (discrete-refl-graph-is-univalent B) f

\end{code}

We wish to move towards a more unified approach to SIP. We will try to give
some illustrative examples.

Example 1:

We give a detailed characaterization of the identity type of cones over a
cospan using reflexive graphs. This illustration is not intended to be brief.

Two cones with commutative graphs witnessed by 

             q                                 q'
        A ───────→ X                      A ───────→ X       
        │          │                      │          │
  H : p │          │ g            H' : p' │          │ g
        │          │                      │          │
        ↓          ↓                      ↓          ↓
        Y ───────→ Z                      Y ───────→ Z
              f                                 f

are the same when we have homotopies α : p ∼ p' and β : q ∼ q' and a natural
coherence

                           H
                 f ∘ p  ───────→ g ∘ q
                   |               |
               α*  |               |  β*
                   |               |
                   ↓               ↓
                 f ∘ p' ───────→ g ∘ q'
                           H'
between the homotopies.

\begin{code}

module _ (fe : Fun-Ext) {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ }
         (f : X → Z) (g : Y → Z)
       where

 open pullback f g

\end{code}

We define reflexive graph structure on the base of cone whose underlying type
must be (A → X) × (A → Y) with edges corresponding to the pair of homotopes
p ∼ p' and q ∼ q'.

\begin{code}

 cone-base-refl-graph : (A : 𝓣 ̇) → refl-graph (𝓤 ⊔ 𝓥 ⊔ 𝓣) (𝓤 ⊔ 𝓥 ⊔ 𝓣)
 cone-base-refl-graph A
  = (((A → X) × (A → Y)) ,
    (λ (p , q) (p' , q') → (p ∼ p') × (q ∼ q')) ,
     λ (p , q) → (∼-refl , ∼-refl))

\end{code}

That this reflexive graph is univalent is automatic as univalence is closed
under product, functions and use of the discrete reflexive graph.

\begin{code}
     
 cone-base-is-univalent : (A : 𝓣 ̇)
                        → is-univalent-refl-graph (cone-base-refl-graph A)
 cone-base-is-univalent A = univalence-closed-under-binary-product
                             (∏ A , (λ - → Δ X)) (∏ A , (λ - → Δ Y))
                             (univalence-closed-under-cotensor fe A (Δ X)
                              (discrete-refl-graph-is-univalent X))
                             (univalence-closed-under-cotensor fe A (Δ Y)
                              (discrete-refl-graph-is-univalent Y))

\end{code}

We now give the structure of a displayed reflexive graph over the base
whose type family takes pairs of maps and returns commutative squares. The
edges correspond to the natural coherence condition mentioned above.

\begin{code}
                              
 cone-displayed-refl-graph
  : (A : 𝓣 ̇)
  → displayed-refl-graph (𝓦 ⊔ 𝓣) (𝓦 ⊔ 𝓣) (cone-base-refl-graph A)
 cone-displayed-refl-graph A
  = ((λ (p , q) → commutative-square (p , q)) ,
    (λ (α , β) H H' → ∼-trans H (∼-ap-∘ g β) ∼ ∼-trans (∼-ap-∘ f α) H') ,
     λ H - → refl-left-neutral ⁻¹)

\end{code}

To see that the displayed reflexive graph is univalent we only have to look
at the fibers. The luxury here is that the base edges are taken to be the
reflexive data. The fan of interest here is equivalent to a fan over what is
essentially the discrete reflexive graph of f ∘ p ∼ g ∘ q (which is manifestly
univalent).

\begin{code}

 cone-display-is-univalent
  : (A : 𝓣 ̇)
  → is-displayed-univalent-refl-graph (cone-base-refl-graph A)
     (cone-displayed-refl-graph A) 
 cone-display-is-univalent A (p , q) H
  = equiv-to-prop I
     (univalence-closed-under-product fe A (λ x → Δ (f (p x) ＝ g (q x)))
      (λ - → discrete-refl-graph-is-univalent (f (p -) ＝ g (q -))) H)
  where
   I : fan (⋖ cone-displayed-refl-graph A ⋗ (p , q)) H
     ≃ fan (∏ A , (λ x → Δ (f (p x) ＝ g (q x)))) H
   I = (Σ H' ꞉ commutative-square (p , q) ,
        ∼-trans H (∼-refl) ∼ ∼-trans (∼-refl) H')
                                                           ≃⟨ II ⟩
       (Σ H' ꞉ commutative-square (p , q) , H ∼ H')        ■
    where
     II = Σ-cong (λ - → transport-≃ (λ - → H ∼ -)
          (dfunext fe (λ x → refl-left-neutral)))

\end{code}

The hard work is done. Since we have a displaye univalent reflexive graph
over a univalent reflexive graph the total reflexive graph is also univalent.
The carrier of this total reflexive graph corresponds to the type of cones.

\begin{code}

 cone-total-refl-graph : (A : 𝓣 ̇) → refl-graph (𝓤 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓣) (𝓤 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓣)
 cone-total-refl-graph A
  = (cone-base-refl-graph A ﹐ cone-displayed-refl-graph A)

 private
  observation : (A : 𝓣 ̇)
              → ⊰ cone-total-refl-graph A ⊱ ＝ cone A
  observation A = refl

 cone-total-is-univalent : (A : 𝓣 ̇)
                         → is-univalent-refl-graph (cone-total-refl-graph A)
 cone-total-is-univalent A
  = univalence-closed-under-total (cone-base-refl-graph A)
     (cone-displayed-refl-graph A)
     (cone-base-is-univalent A)
     (cone-display-is-univalent A)

 cone-characterization
  : {A : 𝓣 ̇ } {p p' : A → X} {q q' : A → Y}
    {H : f ∘ p ∼ g ∘ q} {H' : f ∘ p' ∼ g ∘ q'}
  → (((p , q) , H) ＝ ((p' , q') , H'))
  ≃ (Σ (α , β) ꞉ (p ∼ p') × (q ∼ q') ,
     ∼-trans H (∼-ap-∘ g β) ∼ ∼-trans (∼-ap-∘ f α) H')
 cone-characterization {𝓣} {A} {p} {p'} {q} {q'} {H} {H'}
  = (id-to-edge' (cone-total-refl-graph A) , I ((p , q) , H) ((p' , q') , H'))
  where
   I : (c c' : cone A)
      → is-equiv (id-to-edge'
         (cone-base-refl-graph A ﹐ cone-displayed-refl-graph A) {c} {c'})
   I = prop-fans-implies-id-to-edge-equiv (cone-total-is-univalent A)

\end{code}

We now use lenses to recreate an existing characterization of transport (see
file FundamentalLemmaOfTransportAlongEquivalences).

\begin{code}

module _ (𝓐 : refl-graph 𝓤 𝓥) (ua-𝓐 : is-univalent-refl-graph 𝓐)
       where

 transport-along-≈ : (P : ⊰ 𝓐 ⊱ → 𝓣 ̇) {x y : ⊰ 𝓐 ⊱}
                   → x ≈⟨ 𝓐 ⟩ y
                   → P x → P y
 transport-along-≈ P {x} {y} e = transport P (edge-to-id' (𝓐 , ua-𝓐) e)

 transport-along-≈-comp : (P : ⊰ 𝓐 ⊱ → 𝓣 ̇) {x : ⊰ 𝓐 ⊱}
                        → (u : P x)
                        → transport-along-≈ P (𝓻 𝓐 x) u ＝ u
 transport-along-≈-comp P {x} u
  = transport (λ - → transport P - u ＝ u)
     (edge-to-id-comp (𝓐 , ua-𝓐) {x} ⁻¹) refl

\end{code}

We now show that if a univalent reflexive graph has an oplax covariant lens
structure on it then push and transport share an edge.

\begin{code}

module _ {𝓤' 𝓥' : Universe}
         (𝓐 : refl-graph 𝓤 𝓥) (ua-𝓐 : is-univalent-refl-graph 𝓐)
         (𝓑 : oplax-covariant-lens 𝓤' 𝓥' 𝓐)
       where

 open oplax-covariant-lens 𝓑

 fundamental-theorem-of-transport-for-edges
  : {x y : ⊰ 𝓐 ⊱}
  → (e : x ≈⟨ 𝓐 ⟩ y)
  → (u : ⊰ lens-fam x ⊱)
  → lens-push e u ≈⟨ lens-fam y ⟩ transport-along-≈ 𝓐 ua-𝓐 lens-fam-car e u
 fundamental-theorem-of-transport-for-edges {x} {y} = I II IV x y
  where
   I : edge-induction (𝓤' ⊔ 𝓥') 𝓐
   I = univalence-implies-edge-induction ua-𝓐
   II : (x y : ⊰ 𝓐 ⊱) → x ≈⟨ 𝓐 ⟩ y → 𝓤' ⊔ 𝓥' ̇
   II x y e = (u : ⊰ lens-fam x ⊱)
    → lens-push e u ≈⟨ lens-fam y ⟩ transport-along-≈ 𝓐 ua-𝓐 lens-fam-car e u
   III : (x : ⊰ 𝓐 ⊱) (u : ⊰ lens-fam x ⊱)
       → u ＝ transport-along-≈ 𝓐 ua-𝓐 lens-fam-car (𝓻 𝓐 x) u
   III x u = ap (λ - → transport lens-fam-car - u)
             (edge-to-id-comp (𝓐 , ua-𝓐)) ⁻¹
   IV : (x : ⊰ 𝓐 ⊱) (u : ⊰ lens-fam x ⊱)
      → lens-push (𝓻 𝓐 x) u
      ≈⟨ lens-fam x ⟩ transport-along-≈ 𝓐 ua-𝓐 lens-fam-car (𝓻 𝓐 x) u
   IV x u = transport (λ - → lens-push (𝓻 𝓐 x) u ≈⟨ lens-fam x ⟩ -) (III x u)
             (lens-push-R u)

\end{code}

If the oplax lens is univalent then we can upgrade the edge to identity.

\begin{code}

module _ {𝓤' 𝓥' : Universe}
         (𝓐 : refl-graph 𝓤 𝓥) (ua-𝓐 : is-univalent-refl-graph 𝓐)
         (𝓑 : oplax-covariant-lens 𝓤' 𝓥' 𝓐)
         (ua-𝓑 : oplax-covariant-lens-is-univalent 𝓐 𝓑)
       where

 open oplax-covariant-lens 𝓑

 fundamental-theorem-of-transport
  : {x y : ⊰ 𝓐 ⊱}
  → (e : x ≈⟨ 𝓐 ⟩ y)
  → lens-push e ∼ transport-along-≈ 𝓐 ua-𝓐 lens-fam-car e
 fundamental-theorem-of-transport {x} {y} e u
  = edge-to-id' (lens-fam y , ua-𝓑 y)
     (fundamental-theorem-of-transport-for-edges 𝓐 ua-𝓐 𝓑 e u)

\end{code}

It is worth noting that this result follows immediatly from the fact that
oplax structure is contractible (or a pointed proposition!)

\begin{code}

 transport-along-≈-is-oplax-structure
  : oplax-covariant-lens-structure 𝓐 lens-fam
 transport-along-≈-is-oplax-structure = (I , II)
  where
   I : (x y : ⊰ 𝓐 ⊱) → (x ≈⟨ 𝓐 ⟩ y) → ⊰ lens-fam x ⊱ → ⊰ lens-fam y ⊱
   I x y = transport-along-≈ 𝓐 ua-𝓐 lens-fam-car
   II : (x : ⊰ 𝓐 ⊱) (u : ⊰ lens-fam x ⊱)
      → (I x x (𝓻 𝓐 x) u) ≈⟨ lens-fam x ⟩ u
   II x u = id-to-edge' (lens-fam x)
             (transport-along-≈-comp 𝓐 ua-𝓐 lens-fam-car u)

 oplax-＝-transport-structure
  : FunExt
  → oplax-data-is-oplax-structure ＝ transport-along-≈-is-oplax-structure
 oplax-＝-transport-structure fe
  = oplax-lens-structure-is-a-property fe 𝓐 lens-fam ua-𝓐 ua-𝓑
     oplax-data-is-oplax-structure transport-along-≈-is-oplax-structure

 private
  observation
   : FunExt
   → {x y : ⊰ 𝓐 ⊱}
   → (e : x ≈⟨ 𝓐 ⟩ y)
   → lens-push e ∼ transport-along-≈ 𝓐 ua-𝓐 lens-fam-car e
  observation fe e u = ap (λ - → (pr₁ -) _ _ e u) (oplax-＝-transport-structure fe)

\end{code}
