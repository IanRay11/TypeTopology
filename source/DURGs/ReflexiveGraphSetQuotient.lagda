Ian Ray. 15th February 2026.

Investigating set quotients of reflexive graphs.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module DURGs.ReflexiveGraphSetQuotient where

open import MLTT.Spartan
open import DURGs.BivariantMidpointLenses
open import DURGs.ReflexiveGraphConstructions
open import DURGs.UnivalentReflexiveGraphClosureProperties
open import DURGs.DisplayedReflexiveGraphs
open import DURGs.DisplayedUnivalentReflexiveGraphs
open import DURGs.Lenses
open import DURGs.ReflexiveGraphs
open import DURGs.UnivalentFamilies
open import DURGs.UnivalentReflexiveGraphs
open import DURGs.UnivalenceProperty
open import UF.Equiv
open import UF.FunExt
open import UF.PropTrunc
open import UF.Sets-Properties
open import UF.Subsingletons
open import UF.SubtypeClassifier
open import UF.SubtypeClassifier-Properties
open import Quotient.Type
open import Quotient.Effectivity

module _ (fe : Fun-Ext)
         (pe : Prop-Ext)
         (gs : general-set-quotients-exist (λ 𝓤 → 𝓤))
         (pt : propositional-truncations-exist)
         (A : 𝓤 ̇)
         (R@(_≋_ , eq-prop-val , eq-refl , _) : EqRel {𝓤} {𝓣} A)
          where

 open import UF.ImageAndSurjection pt
 open general-set-quotients-exist gs
 open PropositionalTruncation pt

 set-quotient-refl-graph : refl-graph (𝓤 ⊔ 𝓣) (𝓤 ⊔ 𝓣)
 set-quotient-refl-graph = (A / R , I , II)
  where
   I : A / R → A / R → 𝓤 ⊔ 𝓣 ̇
   I u v = ∃ x ꞉ A , ∃ y ꞉ A , (η/ R x ＝ u) × (η/ R y ＝ v) × (x ≋ y)
   II : (u : A / R) → I u u
   II u = IV III
    where
     III : u ∈image (η/ R)
     III = η/-is-surjection R pt u
     IV : u ∈image (η/ R) → I u u
     IV = ∥∥-rec ∃-is-prop (λ (x , p) → ∣ x , ∣ x , p , p , eq-refl x ∣ ∣)

 char-set-quotient-＝ : (x y : A)
                     → (η/ R x ＝ η/ R y) ≃ (x ≋ y)
 char-set-quotient-＝ x y
  = logically-equivalent-props-are-equivalent (/-is-set R) (eq-prop-val x y)
     (effectivity fe pe gs R) (η/-identifies-related-points R)

\end{code}

TODO use effectivity of quotients to show that this reflexive graph is
univalent.

\begin{code}

 return-map-set-quo : (u v : A / R)
                    → u ≈⟨ set-quotient-refl-graph ⟩ v
                    → u ＝ v
 return-map-set-quo u v = ∥∥-rec (/-is-set R) III
  where
   I : (x : A) → (Σ y ꞉ A , (η/ R x ＝ u) × (η/ R y ＝ v) × (x ≋ y)) → u ＝ v
   I x (y , p , q , r) = u      ＝⟨ p ⁻¹ ⟩ 
                         η/ R x ＝⟨ ⌜ (char-set-quotient-＝ x y) ⌝⁻¹ r ⟩
                         η/ R y ＝⟨ q ⟩
                         v      ∎
   II : (x : A) → (∃ y ꞉ A , (η/ R x ＝ u) × (η/ R y ＝ v) × (x ≋ y)) → u ＝ v
   II x = ∥∥-rec (/-is-set R) (I x)
   III : (Σ x ꞉ A , ∃ y ꞉ A , (η/ R x ＝ u) × (η/ R y ＝ v) × (x ≋ y)) → u ＝ v
   III = uncurry II

 canonical-map-set-quo-is-equiv : (u v : A / R)
                                → is-equiv (id-to-edge set-quotient-refl-graph)
 canonical-map-set-quo-is-equiv u v
  = logical-equivs-of-props-are-equivs (/-is-set R) ∃-is-prop
     (id-to-edge set-quotient-refl-graph) (return-map-set-quo u v)
 
 char-/-＝ : (u v : A / R)
           → (u ＝ v) ≃ (u ≈⟨ set-quotient-refl-graph ⟩ v)
 char-/-＝ u v
  = (id-to-edge set-quotient-refl-graph , canonical-map-set-quo-is-equiv u v)

 set-quotient-refl-graph-univalent
  : is-univalent-refl-graph set-quotient-refl-graph
 set-quotient-refl-graph-univalent
  = id-to-edge-equiv-implies-prop-fans canonical-map-set-quo-is-equiv



 


