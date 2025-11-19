Ian Ray. 7th November 2025.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module DURGs.UnivalenceProperty where

open import MLTT.Spartan
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.FunExt
open import DURGs.BasicConstructionsonReflexiveGraphs
open import DURGs.BivariantMidpointLenses
open import DURGs.ClosurePropertiesofUnivalentReflexiveGraphs
open import DURGs.DisplayedReflexiveGraphs
open import DURGs.DisplayedUnivalentReflexiveGraphs
open import DURGs.Lenses
open import DURGs.ReflexiveGraphs
open import DURGs.UnivalentReflexiveGraphs

\end{code}

We show that univalence is a proposition.

\begin{code}

refl-graph-univalence-is-a-property : Fun-Ext
                                    → (𝓐 : refl-graph 𝓤 𝓥)
                                    → is-prop (is-univalent-refl-graph 𝓐)
refl-graph-univalence-is-a-property fe 𝓐
 = Π-is-prop fe (λ - → being-prop-is-prop fe)

displayed-refl-graph-univalence-is-a-property
 : Fun-Ext
 → (𝓐 : refl-graph 𝓤 𝓥) (𝓑 : displayed-refl-graph 𝓤' 𝓥' 𝓐)
 → is-prop (is-displayed-univalent-refl-graph 𝓐 𝓑)
displayed-refl-graph-univalence-is-a-property fe 𝓐 𝓑
 = Π-is-prop fe (λ - → refl-graph-univalence-is-a-property fe (⋖ 𝓑 ⋗ -))

\end{code}

To show lens structure is a property we will require the following (cursed)
lemmas.

\begin{code}

oplax-structure-is-property-lemma
 : FunExt
 → Fun-Ext
 → (𝓐 : refl-graph 𝓤 𝓥) (𝓑 : ⊰ 𝓐 ⊱ → refl-graph 𝓤' 𝓥')
 → is-univalent-refl-graph 𝓐
 → ((x : ⊰ 𝓐 ⊱) → is-univalent-refl-graph (𝓑 x))
 → (x : ⊰ 𝓐 ⊱)
 → (Σ ϕ ꞉ ((y : ⊰ 𝓐 ⊱) (p : x ≈⟨ 𝓐 ⟩ y) → ⊰ 𝓑 x ⊱ → ⊰ 𝓑 y ⊱) ,
        ((u : ⊰ 𝓑 x ⊱) → ϕ x (𝓻 𝓐 x) u ≈⟨ 𝓑 x ⟩ u))
 ≃ (Σ ϕ ꞉ (⊰ 𝓑 x ⊱ → ⊰ 𝓑 x ⊱) , ((u : ⊰ 𝓑 x ⊱) → ϕ u ≈⟨ 𝓑 x ⟩ u))
oplax-structure-is-property-lemma {𝓤} fe fe' 𝓐 𝓑 is-ua-𝓐 is-ua-𝓑 x
 = ((Σ ϕ ꞉ ((y : ⊰ 𝓐 ⊱) (p : x ≈⟨ 𝓐 ⟩ y) → ⊰ 𝓑 x ⊱ → ⊰ 𝓑 y ⊱) ,
        ((u : ⊰ 𝓑 x ⊱) → ϕ x (𝓻 𝓐 x) u ≈⟨ 𝓑 x ⟩ u)))           ≃⟨ I ⟩
   (Σ ϕ ꞉ (((y , p) : fan 𝓐 x) → ⊰ 𝓑 x ⊱ → ⊰ 𝓑 y ⊱) ,
        ((u : ⊰ 𝓑 x ⊱) → ϕ (x , (𝓻 𝓐 x)) u ≈⟨ 𝓑 x ⟩ u))        ≃⟨ IV ⟩
   cofan (∏ ⊰ 𝓑 x ⊱ , (λ - → 𝓑 x)) id                          ■
 where
  I = Σ-change-of-variable-≃ (λ ϕ → (u : ⊰ 𝓑 x ⊱) → ϕ (x , 𝓻 𝓐 x) u ≈⟨ 𝓑 x ⟩ u)
       (≃-sym (curry-uncurry fe))
  II : fan 𝓐 x ≃ 𝟙 {𝓤}
  II = singleton-≃-𝟙 (prop-fan-to-contr {_} {_} {𝓐} is-ua-𝓐 x)
  III : (((y , p) : fan 𝓐 x) → ⊰ 𝓑 x ⊱ → ⊰ 𝓑 y ⊱)
      ≃ (⊰ 𝓑 x ⊱ → ⊰ 𝓑 x ⊱)
  III = (((y , p) : fan 𝓐 x) → ⊰ 𝓑 x ⊱ → ⊰ 𝓑 y ⊱)   ≃⟨ I' ⟩
         (𝟙 → ⊰ 𝓑 x ⊱ → ⊰ 𝓑 x ⊱)                    ≃⟨ ≃-sym (𝟙→ fe') ⟩
         (⊰ 𝓑 x ⊱ → ⊰ 𝓑 x ⊱)                        ■
   where
    I' = ≃-sym (Π-change-of-variable-≃ {𝓤} {_} {_} fe
          (λ (y , p) → ⊰ 𝓑 x ⊱ → ⊰ 𝓑 y ⊱) (≃-sym II))
  IV = Σ-change-of-variable-≃ (λ - → - ≈⟨ ∏ ⊰ 𝓑 x ⊱ , (λ - → 𝓑 x) ⟩ id ) III

lax-structure-is-property-lemma
 : FunExt
 → Fun-Ext
 → (𝓐 : refl-graph 𝓤 𝓥) (𝓑 : ⊰ 𝓐 ⊱ → refl-graph 𝓤' 𝓥')
 → is-univalent-refl-graph 𝓐
 → ((x : ⊰ 𝓐 ⊱) → is-univalent-refl-graph (𝓑 x))
 → (x : ⊰ 𝓐 ⊱)
 → (Σ ϕ ꞉ ((y : ⊰ 𝓐 ⊱) (p : x ≈⟨ 𝓐 ⟩ y) → ⊰ 𝓑 y ⊱ → ⊰ 𝓑 x ⊱) ,
        ((u : ⊰ 𝓑 x ⊱) → u ≈⟨ 𝓑 x ⟩ ϕ x (𝓻 𝓐 x) u))
 ≃ (Σ ϕ ꞉ (⊰ 𝓑 x ⊱ → ⊰ 𝓑 x ⊱) , ((u : ⊰ 𝓑 x ⊱) → u ≈⟨ 𝓑 x ⟩ ϕ u))
lax-structure-is-property-lemma {𝓤} fe fe' 𝓐 𝓑 is-ua-𝓐 is-ua-𝓑 x
 = ((Σ ϕ ꞉ ((y : ⊰ 𝓐 ⊱) (p : x ≈⟨ 𝓐 ⟩ y) → ⊰ 𝓑 y ⊱ → ⊰ 𝓑 x ⊱) ,
        ((u : ⊰ 𝓑 x ⊱) → u ≈⟨ 𝓑 x ⟩ ϕ x (𝓻 𝓐 x) u)))           ≃⟨ I ⟩
   (Σ ϕ ꞉ (((y , p) : fan 𝓐 x) → ⊰ 𝓑 y ⊱ → ⊰ 𝓑 x ⊱) ,
        ((u : ⊰ 𝓑 x ⊱) → u ≈⟨ 𝓑 x ⟩ ϕ (x , (𝓻 𝓐 x)) u))        ≃⟨ IV ⟩
   fan (∏ ⊰ 𝓑 x ⊱ , (λ - → 𝓑 x)) id                            ■
 where
  I = Σ-change-of-variable-≃ (λ ϕ → (u : ⊰ 𝓑 x ⊱) → u ≈⟨ 𝓑 x ⟩ ϕ (x , 𝓻 𝓐 x) u)
       (≃-sym (curry-uncurry fe))
  II : fan 𝓐 x ≃ 𝟙 {𝓤}
  II = singleton-≃-𝟙 (prop-fan-to-contr {_} {_} {𝓐} is-ua-𝓐 x)
  III : (((y , p) : fan 𝓐 x) → ⊰ 𝓑 y ⊱ → ⊰ 𝓑 x ⊱)
      ≃ (⊰ 𝓑 x ⊱ → ⊰ 𝓑 x ⊱)
  III = (((y , p) : fan 𝓐 x) → ⊰ 𝓑 y ⊱ → ⊰ 𝓑 x ⊱)   ≃⟨ I' ⟩
         (𝟙 → ⊰ 𝓑 x ⊱ → ⊰ 𝓑 x ⊱)                    ≃⟨ ≃-sym (𝟙→ fe') ⟩
         (⊰ 𝓑 x ⊱ → ⊰ 𝓑 x ⊱)                        ■
   where
    I' = ≃-sym (Π-change-of-variable-≃ {𝓤} {_} {_} fe
          (λ (y , p) → ⊰ 𝓑 y ⊱ → ⊰ 𝓑 x ⊱) (≃-sym II))
  IV = Σ-change-of-variable-≃ (λ - → id ≈⟨ ∏ ⊰ 𝓑 x ⊱ , (λ - → 𝓑 x) ⟩ - ) III

bivariant-structure-is-property-lemma
 : FunExt
 → Fun-Ext
 → (𝓐 : refl-graph 𝓤 𝓥) (𝓑 : (x y : ⊰ 𝓐 ⊱) → (x ≈⟨ 𝓐 ⟩ y) → refl-graph 𝓤' 𝓥')
 → is-univalent-refl-graph 𝓐
 → ((x y : ⊰ 𝓐 ⊱) (p : x ≈⟨ 𝓐 ⟩ y) → is-univalent-refl-graph (𝓑 x y p))
 → (bivariant-midpoint-lens-structure 𝓐 𝓑)
 ≃ ((x : ⊰ 𝓐 ⊱)
 → Σ ϕ ꞉ ((y : ⊰ 𝓐 ⊱) (p : x ≈⟨ 𝓐 ⟩ y) → ⊰ 𝓑 x x (𝓻 𝓐 x) ⊱ → ⊰ 𝓑 x y p ⊱)
 , Σ ψ ꞉ ((y : ⊰ 𝓐 ⊱) (p : x ≈⟨ 𝓐 ⟩ y) → ⊰ 𝓑 y y (𝓻 𝓐 y) ⊱ → ⊰ 𝓑 x y p ⊱)
 , ((u : ⊰ 𝓑 x x (𝓻 𝓐 x) ⊱) → ϕ x (𝓻 𝓐 x) u ≈⟨ 𝓑 x x (𝓻 𝓐 x) ⟩ ψ x (𝓻 𝓐 x) u)
 × ((u : ⊰ 𝓑 x x (𝓻 𝓐 x) ⊱) → u ≈⟨ 𝓑 x x (𝓻 𝓐 x) ⟩ ψ x (𝓻 𝓐 x) u))
bivariant-structure-is-property-lemma fe fe' 𝓐 𝓑 is-ua-𝓐 is-ua-𝓑
 = bivariant-midpoint-lens-structure 𝓐 𝓑                                ≃⟨ I ⟩
   (Σ ϕ ꞉ ((x y : ⊰ 𝓐 ⊱) (p : x ≈⟨ 𝓐 ⟩ y) → ⊰ 𝓑 x x (𝓻 𝓐 x) ⊱ → ⊰ 𝓑 x y p ⊱) ,
    Σ ψ ꞉ ((x y : ⊰ 𝓐 ⊱) (p : x ≈⟨ 𝓐 ⟩ y) → ⊰ 𝓑 y y (𝓻 𝓐 y) ⊱ → ⊰ 𝓑 x y p ⊱) ,
   ((x : ⊰ 𝓐 ⊱)
    → ((u : ⊰ 𝓑 x x (𝓻 𝓐 x) ⊱)
       → ϕ x x (𝓻 𝓐 x) u ≈⟨ 𝓑 x x (𝓻 𝓐 x) ⟩ ψ x x (𝓻 𝓐 x) u)
    × ((u : ⊰ 𝓑 x x (𝓻 𝓐 x) ⊱) → u ≈⟨ 𝓑 x x (𝓻 𝓐 x) ⟩ ψ x x (𝓻 𝓐 x) u)))                                                                                ≃⟨ II ⟩
   (Σ ϕ ꞉ ((x y : ⊰ 𝓐 ⊱) (p : x ≈⟨ 𝓐 ⟩ y) → ⊰ 𝓑 x x (𝓻 𝓐 x) ⊱ → ⊰ 𝓑 x y p ⊱) ,
   ((x : ⊰ 𝓐 ⊱)
    → Σ ψ ꞉ ((y : ⊰ 𝓐 ⊱) (p : x ≈⟨ 𝓐 ⟩ y) → ⊰ 𝓑 y y (𝓻 𝓐 y) ⊱ → ⊰ 𝓑 x y p ⊱) ,
    ((u : ⊰ 𝓑 x x (𝓻 𝓐 x) ⊱) → ϕ x x (𝓻 𝓐 x) u ≈⟨ 𝓑 x x (𝓻 𝓐 x) ⟩ ψ x (𝓻 𝓐 x) u)
    × ((u : ⊰ 𝓑 x x (𝓻 𝓐 x) ⊱) → u ≈⟨ 𝓑 x x (𝓻 𝓐 x) ⟩ ψ x (𝓻 𝓐 x) u)))
                                                                       ≃⟨ III ⟩
   ((x : ⊰ 𝓐 ⊱)
   → Σ ϕ ꞉ ((y : ⊰ 𝓐 ⊱) (p : x ≈⟨ 𝓐 ⟩ y) → ⊰ 𝓑 x x (𝓻 𝓐 x) ⊱ → ⊰ 𝓑 x y p ⊱)
   , Σ ψ ꞉ ((y : ⊰ 𝓐 ⊱) (p : x ≈⟨ 𝓐 ⟩ y) → ⊰ 𝓑 y y (𝓻 𝓐 y) ⊱ → ⊰ 𝓑 x y p ⊱)
   , ((u : ⊰ 𝓑 x x (𝓻 𝓐 x) ⊱) → ϕ x (𝓻 𝓐 x) u ≈⟨ 𝓑 x x (𝓻 𝓐 x) ⟩ ψ x (𝓻 𝓐 x) u)
   × ((u : ⊰ 𝓑 x x (𝓻 𝓐 x) ⊱) → u ≈⟨ 𝓑 x x (𝓻 𝓐 x) ⟩ ψ x (𝓻 𝓐 x) u))    ■
  where
   I = Σ-cong (λ ϕ → Σ-cong (λ ψ → ≃-sym Π×-distr))
   II = Σ-cong (λ ϕ → ≃-sym ΠΣ-distr-≃)
   III = ≃-sym ΠΣ-distr-≃

-- now that it's simple, suggest just inlining where used -Carlo
Σ-×-assoc-lemma : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {A : X → 𝓦 ̇ } {B : X → Y → 𝓣 ̇ }
                → (Σ x ꞉ X , Σ y ꞉ Y , (B x y × A x))
                ≃ (Σ x ꞉ X , ((Σ y ꞉ Y , B x y) × A x))
Σ-×-assoc-lemma = Σ-cong (λ - → ≃-sym Σ-assoc)

bivariant-structure-is-property-lemma'
 : FunExt
 → Fun-Ext
 → (𝓐 : refl-graph 𝓤 𝓥) (𝓑 : (x y : ⊰ 𝓐 ⊱) → (x ≈⟨ 𝓐 ⟩ y) → refl-graph 𝓤' 𝓥')
 → is-univalent-refl-graph 𝓐
 → ((x y : ⊰ 𝓐 ⊱) (p : x ≈⟨ 𝓐 ⟩ y) → is-univalent-refl-graph (𝓑 x y p))
 → (x : ⊰ 𝓐 ⊱)
 → (Σ ϕ ꞉ ((y : ⊰ 𝓐 ⊱) (p : x ≈⟨ 𝓐 ⟩ y) → ⊰ 𝓑 x x (𝓻 𝓐 x) ⊱ → ⊰ 𝓑 x y p ⊱)
  , Σ ψ ꞉ ((y : ⊰ 𝓐 ⊱) (p : x ≈⟨ 𝓐 ⟩ y) → ⊰ 𝓑 y y (𝓻 𝓐 y) ⊱ → ⊰ 𝓑 x y p ⊱)
  , ((u : ⊰ 𝓑 x x (𝓻 𝓐 x) ⊱) → ϕ x (𝓻 𝓐 x) u ≈⟨ 𝓑 x x (𝓻 𝓐 x) ⟩ ψ x (𝓻 𝓐 x) u)
 × ((u : ⊰ 𝓑 x x (𝓻 𝓐 x) ⊱) → u ≈⟨ 𝓑 x x (𝓻 𝓐 x) ⟩ ψ x (𝓻 𝓐 x) u))
 ≃ (Σ ψ ꞉ (⊰ 𝓑 x x (𝓻 𝓐 x) ⊱ → ⊰ 𝓑 x x (𝓻 𝓐 x) ⊱)
  , id ≈⟨ ∏ ⊰ 𝓑 x x (𝓻 𝓐 x) ⊱ , (λ - → 𝓑 x x (𝓻 𝓐 x)) ⟩ ψ)
bivariant-structure-is-property-lemma' {𝓤} {𝓥} {𝓤'} {𝓥'} fe fe' 𝓐 𝓑
 is-ua-𝓐 is-ua-𝓑 x
 = (Σ ϕ ꞉ ((y : ⊰ 𝓐 ⊱) (p : x ≈⟨ 𝓐 ⟩ y) → ⊰ 𝓑 x x (𝓻 𝓐 x) ⊱ → ⊰ 𝓑 x y p ⊱)
  , Σ ψ ꞉ ((y : ⊰ 𝓐 ⊱) (p : x ≈⟨ 𝓐 ⟩ y) → ⊰ 𝓑 y y (𝓻 𝓐 y) ⊱ → ⊰ 𝓑 x y p ⊱)
  , ((u : ⊰ 𝓑 x x (𝓻 𝓐 x) ⊱) → ϕ x (𝓻 𝓐 x) u ≈⟨ 𝓑 x x (𝓻 𝓐 x) ⟩ ψ x (𝓻 𝓐 x) u)
 × ((u : ⊰ 𝓑 x x (𝓻 𝓐 x) ⊱) → u ≈⟨ 𝓑 x x (𝓻 𝓐 x) ⟩ ψ x (𝓻 𝓐 x) u))
                                                           ≃⟨ I ⟩
 (Σ ϕ ꞉ (((y , p) : fan 𝓐 x) → ⊰ 𝓑 x x (𝓻 𝓐 x) ⊱ → ⊰ 𝓑 x y p ⊱)
  , Σ ψ ꞉ (((y , p) : fan 𝓐 x) → ⊰ 𝓑 y y (𝓻 𝓐 y) ⊱ → ⊰ 𝓑 x y p ⊱)
  , ((u : ⊰ 𝓑 x x (𝓻 𝓐 x) ⊱)
    → ϕ (x , (𝓻 𝓐 x)) u ≈⟨ 𝓑 x x (𝓻 𝓐 x) ⟩ ψ (x , (𝓻 𝓐 x)) u)
 × ((u : ⊰ 𝓑 x x (𝓻 𝓐 x) ⊱) → u ≈⟨ 𝓑 x x (𝓻 𝓐 x) ⟩ ψ (x , (𝓻 𝓐 x)) u))
                                                           ≃⟨ IV ⟩
 (Σ ϕ ꞉ (⊰ 𝓑 x x (𝓻 𝓐 x) ⊱ → ⊰ 𝓑 x x (𝓻 𝓐 x) ⊱)
  , Σ ψ ꞉ (⊰ 𝓑 x x (𝓻 𝓐 x) ⊱ → ⊰ 𝓑 x x (𝓻 𝓐 x) ⊱)
  , (ϕ ≈⟨ ∏ ⊰ 𝓑 x x (𝓻 𝓐 x) ⊱ , (λ - → 𝓑 x x (𝓻 𝓐 x)) ⟩ ψ)
 × (id ≈⟨ ∏ ⊰ 𝓑 x x (𝓻 𝓐 x) ⊱ , (λ - → 𝓑 x x (𝓻 𝓐 x)) ⟩ ψ))
                                                           ≃⟨ V ⟩
 (Σ ψ ꞉ (⊰ 𝓑 x x (𝓻 𝓐 x) ⊱ → ⊰ 𝓑 x x (𝓻 𝓐 x) ⊱)
  , (cofan (∏ ⊰ 𝓑 x x (𝓻 𝓐 x) ⊱ , (λ - → 𝓑 x x (𝓻 𝓐 x))) ψ)
  × (id ≈⟨ ∏ ⊰ 𝓑 x x (𝓻 𝓐 x) ⊱ , (λ - → 𝓑 x x (𝓻 𝓐 x)) ⟩ ψ))
                                                           ≃⟨ VI ⟩
 fan (∏ ⊰ 𝓑 x x (𝓻 𝓐 x) ⊱ , (λ - → 𝓑 x x (𝓻 𝓐 x))) id      ■
  where
   I = ≃-comp (Σ-change-of-variable-≃
         (λ ϕ → Σ ψ ꞉ ((y : ⊰ 𝓐 ⊱) (p : x ≈⟨ 𝓐 ⟩ y)
                → ⊰ 𝓑 y y (𝓻 𝓐 y) ⊱ → ⊰ 𝓑 x y p ⊱)
           , ((u : ⊰ 𝓑 x x (𝓻 𝓐 x) ⊱)
                → ϕ (x , (𝓻 𝓐 x)) u ≈⟨ 𝓑 x x (𝓻 𝓐 x) ⟩ ψ x (𝓻 𝓐 x) u)
         × ((u : ⊰ 𝓑 x x (𝓻 𝓐 x) ⊱) → u ≈⟨ 𝓑 x x (𝓻 𝓐 x) ⟩ ψ x (𝓻 𝓐 x) u))
         (≃-sym (curry-uncurry fe)))
        (Σ-cong (λ - → Σ-change-of-variable-≃
         (λ ψ → ((u : ⊰ 𝓑 x x (𝓻 𝓐 x) ⊱)
                → - (x , (𝓻 𝓐 x)) u ≈⟨ 𝓑 x x (𝓻 𝓐 x) ⟩ ψ (x , (𝓻 𝓐 x)) u)
         × ((u : ⊰ 𝓑 x x (𝓻 𝓐 x) ⊱) → u ≈⟨ 𝓑 x x (𝓻 𝓐 x) ⟩ ψ (x , (𝓻 𝓐 x)) u))
         (≃-sym (curry-uncurry fe))))
   II  = (((y , p) : fan 𝓐 x) → ⊰ 𝓑 x x (𝓻 𝓐 x) ⊱ → ⊰ 𝓑 x y p ⊱) ≃⟨ II' ⟩
         (𝟙{𝓤} → ⊰ 𝓑 x x (𝓻 𝓐 x) ⊱ → ⊰ 𝓑 x x (𝓻 𝓐 x) ⊱)      ≃⟨ ≃-sym (𝟙→ fe') ⟩
         (⊰ 𝓑 x x (𝓻 𝓐 x) ⊱ → ⊰ 𝓑 x x (𝓻 𝓐 x) ⊱)             ■
    where
     II' = ≃-sym (Π-change-of-variable-≃ fe
            (λ (y , p) → ⊰ 𝓑 x x (𝓻 𝓐 x) ⊱ → ⊰ 𝓑 x y p ⊱)
            (≃-sym (singleton-≃-𝟙 (prop-fan-to-contr {_} {_} {𝓐} is-ua-𝓐 x))))
   III = (((y , p) : fan 𝓐 x) → ⊰ 𝓑 y y (𝓻 𝓐 y) ⊱ → ⊰ 𝓑 x y p ⊱) ≃⟨ III' ⟩
         (𝟙{𝓤} → ⊰ 𝓑 x x (𝓻 𝓐 x) ⊱ → ⊰ 𝓑 x x (𝓻 𝓐 x) ⊱)      ≃⟨ ≃-sym (𝟙→ fe') ⟩
         (⊰ 𝓑 x x (𝓻 𝓐 x) ⊱ → ⊰ 𝓑 x x (𝓻 𝓐 x) ⊱)             ■
    where
     III' = ≃-sym (Π-change-of-variable-≃ fe
             (λ (y , p) → ⊰ 𝓑 y y (𝓻 𝓐 y) ⊱ → ⊰ 𝓑 x y p ⊱)
             (≃-sym (singleton-≃-𝟙 (prop-fan-to-contr {_} {_} {𝓐} is-ua-𝓐 x))))
   IV = ≃-comp (Σ-change-of-variable-≃ (λ ϕ → _) II)
         (Σ-cong (λ ϕ → Σ-change-of-variable-≃ (λ ψ → _) III))
   V = ≃-comp Σ-flip Σ-×-assoc-lemma
   VI = Σ-cong (λ ψ → ≃-comp (Σ-change-of-variable-≃ {𝓤' ⊔ 𝓥'}
        (λ z → id ≈⟨ ∏ ⊰ 𝓑 x x (𝓻 𝓐 x) ⊱ , (λ - → 𝓑 x x (𝓻 𝓐 x)) ⟩ ψ)
         (singleton-≃-𝟙 (contr-fan-to-cofan {_} {_}
                         {∏ ⊰ 𝓑 x x (𝓻 𝓐 x) ⊱ , (λ - → 𝓑 x x (𝓻 𝓐 x))}
          (prop-fan-to-contr {_} {_}
           {∏ ⊰ 𝓑 x x (𝓻 𝓐 x) ⊱ , (λ - → 𝓑 x x (𝓻 𝓐 x))}
          VI'') ψ)))
         𝟙-lneutral)
    where
     VI'' : (ψ : ⊰ ∏ ⊰ 𝓑 x x (𝓻 𝓐 x) ⊱ , (λ - → 𝓑 x x (𝓻 𝓐 x)) ⊱)
          → is-prop (fan (∏ ⊰ 𝓑 x x (𝓻 𝓐 x) ⊱ , (λ - → 𝓑 x x (𝓻 𝓐 x))) ψ)
     VI'' ψ = univalence-closed-under-product fe' ⊰ 𝓑 x x (𝓻 𝓐 x) ⊱
               (λ - → 𝓑 x x (𝓻 𝓐 x)) (λ - → is-ua-𝓑 x x (𝓻 𝓐 x)) ψ

\end{code}

Now we can show that lens structure is a proposition.

\begin{code}

oplax-lens-structure-is-a-property
 : FunExt
 → (𝓐 : refl-graph 𝓤 𝓥) (𝓑 : ⊰ 𝓐 ⊱ → refl-graph 𝓤' 𝓥')
 → is-univalent-refl-graph 𝓐
 → ((x : ⊰ 𝓐 ⊱) → is-univalent-refl-graph (𝓑 x))
 → is-prop (oplax-covariant-lens-structure 𝓐 𝓑)
oplax-lens-structure-is-a-property fe 𝓐 𝓑 is-ua-𝓐 is-ua-𝓑 = equiv-to-prop I III
 where
  fe' : Fun-Ext
  fe' = fe _ _
  I : oplax-covariant-lens-structure 𝓐 𝓑
    ≃ ((x : ⊰ 𝓐 ⊱)
      → Σ ϕ ꞉ (⊰ 𝓑 x ⊱ → ⊰ 𝓑 x ⊱) , ((u : ⊰ 𝓑 x ⊱) → ϕ u ≈⟨ 𝓑 x ⟩ u))
  I = oplax-covariant-lens-structure 𝓐 𝓑                  ≃⟨ I' ⟩
      ((x : ⊰ 𝓐 ⊱)
       → Σ ϕ ꞉ ((y : ⊰ 𝓐 ⊱) (p : x ≈⟨ 𝓐 ⟩ y) → ⊰ 𝓑 x ⊱ → ⊰ 𝓑 y ⊱) ,
        ((u : ⊰ 𝓑 x ⊱) → ϕ x (𝓻 𝓐 x) u ≈⟨ 𝓑 x ⟩ u))       ≃⟨ II' ⟩
      ((x : ⊰ 𝓐 ⊱) → cofan (∏ ⊰ 𝓑 x ⊱ , (λ - → 𝓑 x)) id)  ■
   where
    I' = ≃-sym ΠΣ-distr-≃
    II' = Π-cong fe' fe'
          (oplax-structure-is-property-lemma fe fe' 𝓐 𝓑 is-ua-𝓐 is-ua-𝓑)
  II : (x : ⊰ 𝓐 ⊱) → is-univalent-refl-graph (∏ ⊰ 𝓑 x ⊱ , (λ - → 𝓑 x))
  II x = univalence-closed-under-product fe' ⊰ 𝓑 x ⊱ (λ - → 𝓑 x)
          (λ - → is-ua-𝓑 x)
  III : is-prop ((x : ⊰ 𝓐 ⊱) → cofan (∏ ⊰ 𝓑 x ⊱ , (λ - → 𝓑 x)) id)
  III = Π-is-prop fe'
         (λ - → prop-fan-to-cofan {_} {_} {∏ ⊰ 𝓑 - ⊱ , (λ u → 𝓑 -)} (II -) id)

-- Carlo's version, NB doesn't rely on lemma
oplax-lens-structure-is-contr
 : FunExt
 → (𝓐 : refl-graph 𝓤 𝓥) (𝓑 : ⊰ 𝓐 ⊱ → refl-graph 𝓤' 𝓥')
 → is-univalent-refl-graph 𝓐
 → ((x : ⊰ 𝓐 ⊱) → is-univalent-refl-graph (𝓑 x))
 → is-contr (oplax-covariant-lens-structure 𝓐 𝓑)
oplax-lens-structure-is-contr {𝓤} fe 𝓐 𝓑 is-ua-𝓐 is-ua-𝓑 =
 equiv-to-singleton I
  (Π-is-singleton (fe _ _) (λ x → equiv-to-singleton (IV x) 𝟙-is-singleton))
 where
  I : oplax-covariant-lens-structure 𝓐 𝓑 ≃
      ((x : ⊰ 𝓐 ⊱)
       → Σ ϕ ꞉ ((y : ⊰ 𝓐 ⊱) (p : x ≈⟨ 𝓐 ⟩ y) → ⊰ 𝓑 x ⊱ → ⊰ 𝓑 y ⊱)
       , ((u : ⊰ 𝓑 x ⊱) → ϕ x (𝓻 𝓐 x) u ≈⟨ 𝓑 x ⟩ u))
  I = ≃-sym ΠΣ-distr-≃
  II : (x : ⊰ 𝓐 ⊱) → 𝟙 {𝓥} ≃ fan 𝓐 x
  II x = singleton-≃-𝟙' (prop-fan-to-contr {_} {_} {𝓐} is-ua-𝓐 x)
  III : (x : ⊰ 𝓐 ⊱) → is-contr (cofan (∏ ⊰ 𝓑 x ⊱ , λ _ → 𝓑 x) id)
  III x = prop-fan-to-contr-cofan {_} {_} {∏ ⊰ 𝓑 x ⊱ , λ _ → 𝓑 x}
          (univalence-closed-under-product (fe _ _) ⊰ 𝓑 x ⊱ (λ _ → 𝓑 x) (λ _ → is-ua-𝓑 x))
          id
  IV : (x : ⊰ 𝓐 ⊱) → _ ≃ 𝟙
  IV x = (Σ ϕ ꞉ ((y : ⊰ 𝓐 ⊱) (p : x ≈⟨ 𝓐 ⟩ y) → ⊰ 𝓑 x ⊱ → ⊰ 𝓑 y ⊱) ,
           ((u : ⊰ 𝓑 x ⊱) → ϕ x (𝓻 𝓐 x) u ≈⟨ 𝓑 x ⟩ u))
           ≃⟨ Σ-change-of-variable-≃ _ (≃-sym (curry-uncurry fe)) ⟩
         (Σ ϕ ꞉ (((y , p) : fan 𝓐 x) → ⊰ 𝓑 x ⊱ → ⊰ 𝓑 y ⊱) ,
           ((u : ⊰ 𝓑 x ⊱) → ϕ (x , (𝓻 𝓐 x)) u ≈⟨ 𝓑 x ⟩ u))
           ≃⟨ Σ-change-of-variable-≃ _ (≃-sym (Π-change-of-variable-≃ {𝓤} fe _ (II x))) ⟩
         (Σ ϕ ꞉ (𝟙 → ⊰ 𝓑 x ⊱ → ⊰ 𝓑 x ⊱) , ((u : ⊰ 𝓑 x ⊱) → ϕ ⋆ u ≈⟨ 𝓑 x ⟩ u))
           ≃⟨ Σ-change-of-variable-≃ _ (≃-sym (𝟙→ (fe _ _))) ⟩
         (Σ ϕ ꞉ (⊰ 𝓑 x ⊱ → ⊰ 𝓑 x ⊱) , ((u : ⊰ 𝓑 x ⊱) → ϕ u ≈⟨ 𝓑 x ⟩ u))
           ≃⟨ 𝕚𝕕 ⟩
         cofan (∏ ⊰ 𝓑 x ⊱ , λ _ → 𝓑 x) id
           ≃⟨ singleton-≃-𝟙 (III x) ⟩
         𝟙 {𝓤} ■

lax-lens-structure-is-a-property
 : FunExt
 → (𝓐 : refl-graph 𝓤 𝓥) (𝓑 : ⊰ 𝓐 ⊱ → refl-graph 𝓤' 𝓥')
 → is-univalent-refl-graph 𝓐
 → ((x : ⊰ 𝓐 ⊱) → is-univalent-refl-graph (𝓑 x))
 → is-prop (lax-contravariant-lens-structure 𝓐 𝓑)
lax-lens-structure-is-a-property fe 𝓐 𝓑 is-ua-𝓐 is-ua-𝓑 = equiv-to-prop I III
 where
  fe' : Fun-Ext
  fe' = fe _ _
  I : lax-contravariant-lens-structure 𝓐 𝓑
    ≃ ((x : ⊰ 𝓐 ⊱)
      → Σ ϕ ꞉ (⊰ 𝓑 x ⊱ → ⊰ 𝓑 x ⊱) , ((u : ⊰ 𝓑 x ⊱) → u ≈⟨ 𝓑 x ⟩ ϕ u))
  I = lax-contravariant-lens-structure 𝓐 𝓑                ≃⟨ I' ⟩
      ((x : ⊰ 𝓐 ⊱)
       → Σ ϕ ꞉ ((y : ⊰ 𝓐 ⊱) (p : x ≈⟨ 𝓐 ⟩ y) → ⊰ 𝓑 y ⊱ → ⊰ 𝓑 x ⊱) ,
        ((u : ⊰ 𝓑 x ⊱) → u ≈⟨ 𝓑 x ⟩ ϕ x (𝓻 𝓐 x) u))       ≃⟨ II' ⟩
      ((x : ⊰ 𝓐 ⊱) → fan (∏ ⊰ 𝓑 x ⊱ , (λ - → 𝓑 x)) id)  ■
   where
    I' = ≃-sym ΠΣ-distr-≃
    II' = Π-cong fe' fe'
          (lax-structure-is-property-lemma fe fe' 𝓐 𝓑 is-ua-𝓐 is-ua-𝓑)
  II : (x : ⊰ 𝓐 ⊱) → is-univalent-refl-graph (∏ ⊰ 𝓑 x ⊱ , (λ - → 𝓑 x))
  II x = univalence-closed-under-product fe' ⊰ 𝓑 x ⊱ (λ - → 𝓑 x)
          (λ - → is-ua-𝓑 x)
  III : is-prop ((x : ⊰ 𝓐 ⊱) → fan (∏ ⊰ 𝓑 x ⊱ , (λ - → 𝓑 x)) id)
  III = Π-is-prop fe' (λ - → II - id)

bivariant-lens-structure-is-a-property
 : FunExt
 → (𝓐 : refl-graph 𝓤 𝓥) (𝓑 : (x y : ⊰ 𝓐 ⊱) → (x ≈⟨ 𝓐 ⟩ y) → refl-graph 𝓤' 𝓥')
 → is-univalent-refl-graph 𝓐
 → ((x y : ⊰ 𝓐 ⊱) (p : x ≈⟨ 𝓐 ⟩ y) → is-univalent-refl-graph (𝓑 x y p))
 → is-prop (bivariant-midpoint-lens-structure 𝓐 𝓑)
bivariant-lens-structure-is-a-property fe 𝓐 𝓑 is-ua-𝓐 is-ua-𝓑
 = equiv-to-prop I III
 where
  fe' : Fun-Ext
  fe' = fe _ _
  I : bivariant-midpoint-lens-structure 𝓐 𝓑
    ≃ ((x : ⊰ 𝓐 ⊱)
    → Σ ϕ ꞉ (⊰ 𝓑 x x (𝓻 𝓐 x) ⊱ → ⊰ 𝓑 x x (𝓻 𝓐 x) ⊱)
    , id ≈⟨ ∏ ⊰ 𝓑 x x (𝓻 𝓐 x) ⊱ , (λ - → 𝓑 x x (𝓻 𝓐 x)) ⟩ ϕ)
  I = bivariant-midpoint-lens-structure 𝓐 𝓑                           ≃⟨ I' ⟩
      ((x : ⊰ 𝓐 ⊱)
    → Σ ϕ ꞉ ((y : ⊰ 𝓐 ⊱) (p : x ≈⟨ 𝓐 ⟩ y) → ⊰ 𝓑 x x (𝓻 𝓐 x) ⊱ → ⊰ 𝓑 x y p ⊱)
    , Σ ψ ꞉ ((y : ⊰ 𝓐 ⊱) (p : x ≈⟨ 𝓐 ⟩ y) → ⊰ 𝓑 y y (𝓻 𝓐 y) ⊱ → ⊰ 𝓑 x y p ⊱)
    , ((u : ⊰ 𝓑 x x (𝓻 𝓐 x) ⊱) → ϕ x (𝓻 𝓐 x) u ≈⟨ 𝓑 x x (𝓻 𝓐 x) ⟩ ψ x (𝓻 𝓐 x) u)
    × ((u : ⊰ 𝓑 x x (𝓻 𝓐 x) ⊱) → u ≈⟨ 𝓑 x x (𝓻 𝓐 x) ⟩ ψ x (𝓻 𝓐 x) u))                                                                                 ≃⟨ II' ⟩
      ((x : ⊰ 𝓐 ⊱) → fan (∏ ⊰ 𝓑 x x (𝓻 𝓐 x) ⊱ , (λ - → 𝓑 x x (𝓻 𝓐 x))) id)
                                                                      ■
   where
    I' = bivariant-structure-is-property-lemma fe fe' 𝓐 𝓑 is-ua-𝓐 is-ua-𝓑
    II' = Π-cong fe' fe'
           (bivariant-structure-is-property-lemma' fe fe' 𝓐 𝓑 is-ua-𝓐 is-ua-𝓑)
  II : (x : ⊰ 𝓐 ⊱)
     → is-univalent-refl-graph (∏ ⊰ 𝓑 x x (𝓻 𝓐 x) ⊱ , (λ - → 𝓑 x x (𝓻 𝓐 x)))
  II x = univalence-closed-under-product fe' ⊰ 𝓑 x x (𝓻 𝓐 x) ⊱
          (λ - → 𝓑 x x (𝓻 𝓐 x)) (λ - → is-ua-𝓑 x x (𝓻 𝓐 x))
  III : is-prop ((x : ⊰ 𝓐 ⊱)
                  → fan (∏ ⊰ 𝓑 x x (𝓻 𝓐 x) ⊱ , (λ - → 𝓑 x x (𝓻 𝓐 x))) id)
  III = Π-is-prop fe' (λ - → II - id)

\end{code}
