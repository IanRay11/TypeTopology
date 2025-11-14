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
open import DURGs.ReflexiveGraphs
open import DURGs.UnivalentReflexiveGraphs

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

Function spaces have univalent reflexive graph structure.

This needs to be deleted lol.

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

We illustrate the standard procedure by giving a characaterization of the
identity of cones over a cospan.

\begin{code}

module _ (fe : Fun-Ext) {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ }
         (f : X → Z) (g : Y → Z)
       where

 open pullback f g

 cone-base-refl-graph : (A : 𝓣 ̇) → refl-graph (𝓤 ⊔ 𝓥 ⊔ 𝓣) (𝓤 ⊔ 𝓥 ⊔ 𝓣)
 cone-base-refl-graph A
  = (((A → X) × (A → Y)) ,
    (λ (p , q) (p' , q') → (p ∼ p') × (q ∼ q')) ,
     λ (p , q) → (∼-refl , ∼-refl))
     
 cone-base-is-univalent : (A : 𝓣 ̇)
                        → is-univalent-refl-graph (cone-base-refl-graph A)
 cone-base-is-univalent A = univalence-closed-under-binary-product
                             (∏ A , (λ - → Δ X)) (∏ A , (λ - → Δ Y))
                             (univalence-closed-under-cotensor fe A (Δ X)
                              (discrete-refl-graph-is-univalent X))
                             (univalence-closed-under-cotensor fe A (Δ Y)
                              (discrete-refl-graph-is-univalent Y))
                              
 cone-displayed-refl-graph
  : (A : 𝓣 ̇)
  → displayed-refl-graph (𝓦 ⊔ 𝓣) (𝓦 ⊔ 𝓣) (cone-base-refl-graph A)
 cone-displayed-refl-graph A
  = ((λ (p , q) → commutative-square (p , q)) ,
    (λ (α , β) H H' → ∼-trans H (∼-ap-∘ g β) ∼ ∼-trans (∼-ap-∘ f α) H') ,
     λ H - → refl-left-neutral ⁻¹)

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

 cone-characterization
  : {A : 𝓣 ̇ } {p p' : A → X} {q q' : A → Y}
    {H : f ∘ p ∼ g ∘ q} {H' : f ∘ p' ∼ g ∘ q'}
  → (((p , q) , H) ＝ ((p' , q') , H'))
  ≃ (Σ (α , β) ꞉ (p ∼ p') × (q ∼ q') ,
     ∼-trans H (∼-ap-∘ g β) ∼ ∼-trans (∼-ap-∘ f α) H')
 cone-characterization {𝓣} {A} {p} {p'} {q} {q'} {H} {H'}
  = (id-to-edge' (cone-base-refl-graph A ﹐ cone-displayed-refl-graph A)
    , II ((p , q) , H) ((p' , q') , H'))
  where
   I : is-univalent-refl-graph
        (cone-base-refl-graph A ﹐ cone-displayed-refl-graph A)
   I = univalence-closed-under-total (cone-base-refl-graph A)
        (cone-displayed-refl-graph A) (cone-base-is-univalent A)
        (cone-display-is-univalent A)
   II : (c c' : cone A)
      → is-equiv (id-to-edge'
         (cone-base-refl-graph A ﹐ cone-displayed-refl-graph A) {c} {c'})
   II = prop-fans-implies-id-to-edge-equiv I

\end{code}
