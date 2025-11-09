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

To show lens structure is a property we will require the following lemmas.

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

\end{code}

Now we can show the type of lens structures is a proposition.

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
          (λ - → oplax-structure-is-property-lemma fe fe' 𝓐 𝓑 is-ua-𝓐 is-ua-𝓑 -)
  II : (x : ⊰ 𝓐 ⊱) → is-univalent-refl-graph (∏ ⊰ 𝓑 x ⊱ , (λ - → 𝓑 x))
  II x = univalence-closed-under-product fe' ⊰ 𝓑 x ⊱ (λ - → 𝓑 x)
          (λ - → is-ua-𝓑 x)
  III : is-prop ((x : ⊰ 𝓐 ⊱) → cofan (∏ ⊰ 𝓑 x ⊱ , (λ - → 𝓑 x)) id)
  III = Π-is-prop fe'
         (λ - → prop-fan-to-cofan {_} {_} {∏ ⊰ 𝓑 - ⊱ , (λ u → 𝓑 -)} (II -) id)

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
          (λ - → lax-structure-is-property-lemma fe fe' 𝓐 𝓑 is-ua-𝓐 is-ua-𝓑 -)
  II : (x : ⊰ 𝓐 ⊱) → is-univalent-refl-graph (∏ ⊰ 𝓑 x ⊱ , (λ - → 𝓑 x))
  II x = univalence-closed-under-product fe' ⊰ 𝓑 x ⊱ (λ - → 𝓑 x)
          (λ - → is-ua-𝓑 x)
  III : is-prop ((x : ⊰ 𝓐 ⊱) → fan (∏ ⊰ 𝓑 x ⊱ , (λ - → 𝓑 x)) id)
  III = Π-is-prop fe' (λ - → II - id)

\end{code}


