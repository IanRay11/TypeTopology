Ian Ray. 7th November 2025.

Internal code review and addition by Carlo Angiuli 18th November 2025.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module DURGs.UnivalenceProperty where

open import MLTT.Spartan
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.FunExt
open import UF.PropIndexedPiSigma
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

We show that lens structure is contracible.

\begin{code}

oplax-lens-structure-is-contr
 : FunExt
 → (𝓐 : refl-graph 𝓤 𝓥) (𝓑 : ⊰ 𝓐 ⊱ → refl-graph 𝓤' 𝓥')
 → is-univalent-refl-graph 𝓐
 → ((x : ⊰ 𝓐 ⊱) → is-univalent-refl-graph (𝓑 x))
 → is-contr (oplax-covariant-lens-structure 𝓐 𝓑)
oplax-lens-structure-is-contr {𝓤} fe 𝓐 𝓑 is-ua-𝓐 is-ua-𝓑 =
 equiv-to-singleton I
  (Π-is-singleton (fe _ _) (λ x → equiv-to-singleton (III x) (II x)))
 where
  I : oplax-covariant-lens-structure 𝓐 𝓑
    ≃ ((x : ⊰ 𝓐 ⊱)
       → Σ ϕ ꞉ ((y : ⊰ 𝓐 ⊱) (p : x ≈⟨ 𝓐 ⟩ y) → ⊰ 𝓑 x ⊱ → ⊰ 𝓑 y ⊱)
         , ((u : ⊰ 𝓑 x ⊱) → ϕ x (𝓻 𝓐 x) u ≈⟨ 𝓑 x ⟩ u))
  I = ≃-sym ΠΣ-distr-≃
  II : (x : ⊰ 𝓐 ⊱) → is-contr (cofan (⊰ 𝓑 x ⊱ ➙ 𝓑 x) id)
  II x = prop-fan-to-contr-cofan (⊰ 𝓑 x ⊱ ➙ 𝓑 x)
          (univalence-closed-under-cotensor (fe _ _) _ (𝓑 x) (is-ua-𝓑 x))
          id
  III : (x : ⊰ 𝓐 ⊱) → _ ≃ (cofan (⊰ 𝓑 x ⊱ ➙ 𝓑 x) id)
  III x = (Σ ϕ ꞉ ((y : ⊰ 𝓐 ⊱) (p : x ≈⟨ 𝓐 ⟩ y) → ⊰ 𝓑 x ⊱ → ⊰ 𝓑 y ⊱) ,
            ((u : ⊰ 𝓑 x ⊱) → ϕ x (𝓻 𝓐 x) u ≈⟨ 𝓑 x ⟩ u))
           ≃⟨ Σ-change-of-variable-≃ _ (≃-sym (curry-uncurry fe)) ⟩
          (Σ ϕ ꞉ (((y , p) : fan 𝓐 x) → ⊰ 𝓑 x ⊱ → ⊰ 𝓑 y ⊱) ,
            ((u : ⊰ 𝓑 x ⊱) → ϕ (x , (𝓻 𝓐 x)) u ≈⟨ 𝓑 x ⟩ u))
           ≃⟨ Σ-change-of-variable-≃ _
               (prop-indexed-product (x , 𝓻 𝓐 x) (fe _ _) (is-ua-𝓐 x)) ⟩
          (Σ ϕ ꞉ (⊰ 𝓑 x ⊱ → ⊰ 𝓑 x ⊱) , ((u : ⊰ 𝓑 x ⊱) → ϕ u ≈⟨ 𝓑 x ⟩ u))
           ≃⟨by-definition⟩
          cofan (⊰ 𝓑 x ⊱ ➙ 𝓑 x) id ■

lax-lens-structure-is-contr
 : FunExt
 → (𝓐 : refl-graph 𝓤 𝓥) (𝓑 : ⊰ 𝓐 ⊱ → refl-graph 𝓤' 𝓥')
 → is-univalent-refl-graph 𝓐
 → ((x : ⊰ 𝓐 ⊱) → is-univalent-refl-graph (𝓑 x))
 → is-contr (lax-contravariant-lens-structure 𝓐 𝓑)
lax-lens-structure-is-contr {𝓤} fe 𝓐 𝓑 is-ua-𝓐 is-ua-𝓑 =
 equiv-to-singleton I
  (Π-is-singleton (fe _ _) (λ x → equiv-to-singleton (III x) (II x)))
 where
  I : lax-contravariant-lens-structure 𝓐 𝓑
    ≃ ((x : ⊰ 𝓐 ⊱)
       → Σ ϕ ꞉ ((y : ⊰ 𝓐 ⊱) (p : x ≈⟨ 𝓐 ⟩ y) → ⊰ 𝓑 y ⊱ → ⊰ 𝓑 x ⊱)
         , ((u : ⊰ 𝓑 x ⊱) → u ≈⟨ 𝓑 x ⟩ ϕ x (𝓻 𝓐 x) u))
  I = ≃-sym ΠΣ-distr-≃
  II : (x : ⊰ 𝓐 ⊱) → is-contr (fan (⊰ 𝓑 x ⊱ ➙ 𝓑 x) id)
  II x = prop-fan-to-contr (⊰ 𝓑 x ⊱ ➙ 𝓑 x)
          (univalence-closed-under-cotensor (fe _ _) _ (𝓑 x) (is-ua-𝓑 x)) id
  III : (x : ⊰ 𝓐 ⊱) → _ ≃ fan (⊰ 𝓑 x ⊱ ➙ 𝓑 x) id
  III x = (Σ ϕ ꞉ ((y : ⊰ 𝓐 ⊱) (p : x ≈⟨ 𝓐 ⟩ y) → ⊰ 𝓑 y ⊱ → ⊰ 𝓑 x ⊱) ,
            ((u : ⊰ 𝓑 x ⊱) → u ≈⟨ 𝓑 x ⟩ ϕ x (𝓻 𝓐 x) u))
            ≃⟨ Σ-change-of-variable-≃ _ (≃-sym (curry-uncurry fe)) ⟩
          (Σ ϕ ꞉ (((y , p) : fan 𝓐 x) → ⊰ 𝓑 y ⊱ → ⊰ 𝓑 x ⊱) ,
            ((u : ⊰ 𝓑 x ⊱) → u ≈⟨ 𝓑 x ⟩ ϕ (x , (𝓻 𝓐 x)) u))
            ≃⟨ Σ-change-of-variable-≃ _
                (prop-indexed-product (x , 𝓻 𝓐 x) (fe _ _) (is-ua-𝓐 x)) ⟩
          (Σ ϕ ꞉ (⊰ 𝓑 x ⊱ → ⊰ 𝓑 x ⊱) , ((u : ⊰ 𝓑 x ⊱) → u ≈⟨ 𝓑 x ⟩ ϕ u))
            ≃⟨by-definition⟩
          fan (⊰ 𝓑 x ⊱ ➙ 𝓑 x) id ■ 

bivariant-lens-structure-is-contr
 : FunExt
 → (𝓐 : refl-graph 𝓤 𝓥) (𝓑 : (x y : ⊰ 𝓐 ⊱) → (x ≈⟨ 𝓐 ⟩ y) → refl-graph 𝓤' 𝓥')
 → is-univalent-refl-graph 𝓐
 → ((x y : ⊰ 𝓐 ⊱) (p : x ≈⟨ 𝓐 ⟩ y) → is-univalent-refl-graph (𝓑 x y p))
 → is-contr (bivariant-midpoint-lens-structure 𝓐 𝓑)
bivariant-lens-structure-is-contr {𝓤} fe 𝓐 𝓑 is-ua-𝓐 is-ua-𝓑
 = equiv-to-singleton I
    (Π-is-singleton (fe _ _) (λ x → equiv-to-singleton (III x) (II x id)))
 where
  I : bivariant-midpoint-lens-structure 𝓐 𝓑
    ≃ ((x : ⊰ 𝓐 ⊱)
    → Σ ϕ ꞉ ((y : ⊰ 𝓐 ⊱) (p : x ≈⟨ 𝓐 ⟩ y) → ⊰ 𝓑 x x (𝓻 𝓐 x) ⊱ → ⊰ 𝓑 x y p ⊱)
    , Σ ψ ꞉ ((y : ⊰ 𝓐 ⊱) (p : x ≈⟨ 𝓐 ⟩ y) → ⊰ 𝓑 y y (𝓻 𝓐 y) ⊱ → ⊰ 𝓑 x y p ⊱)
    , ((u : ⊰ 𝓑 x x (𝓻 𝓐 x) ⊱)
      → ϕ x (𝓻 𝓐 x) u ≈⟨ 𝓑 x x (𝓻 𝓐 x) ⟩ ψ x (𝓻 𝓐 x) u)
    × ((u : ⊰ 𝓑 x x (𝓻 𝓐 x) ⊱) → u ≈⟨ 𝓑 x x (𝓻 𝓐 x) ⟩ ψ x (𝓻 𝓐 x) u))
  I = ≃-comp (Σ-cong (λ ϕ → Σ-cong (λ ψ → ≃-sym Π×-distr)))
             (≃-comp (Σ-cong (λ ϕ → ≃-sym ΠΣ-distr-≃)) (≃-sym ΠΣ-distr-≃))
  II : (x : ⊰ 𝓐 ⊱) (ϕ : ⊰ ⊰ 𝓑 x x (𝓻 𝓐 x) ⊱ ➙ 𝓑 x x (𝓻 𝓐 x) ⊱)
     → is-contr (fan (⊰ 𝓑 x x (𝓻 𝓐 x) ⊱ ➙ 𝓑 x x (𝓻 𝓐 x)) ϕ)
  II x ϕ = prop-fan-to-contr (⊰ 𝓑 x x (𝓻 𝓐 x) ⊱ ➙ 𝓑 x x (𝓻 𝓐 x))
            (univalence-closed-under-cotensor (fe _ _) _ (𝓑 x x (𝓻 𝓐 x))
             (is-ua-𝓑 x x (𝓻 𝓐 x))) ϕ
  III : (x : ⊰ 𝓐 ⊱) → _ ≃ fan (⊰ 𝓑 x x (𝓻 𝓐 x) ⊱ ➙ 𝓑 x x (𝓻 𝓐 x)) id
  III x =
    (Σ ϕ ꞉ ((y : ⊰ 𝓐 ⊱) (p : x ≈⟨ 𝓐 ⟩ y) → ⊰ 𝓑 x x (𝓻 𝓐 x) ⊱ → ⊰ 𝓑 x y p ⊱)
    , Σ ψ ꞉ ((y : ⊰ 𝓐 ⊱) (p : x ≈⟨ 𝓐 ⟩ y) → ⊰ 𝓑 y y (𝓻 𝓐 y) ⊱ → ⊰ 𝓑 x y p ⊱)
    , ((u : ⊰ 𝓑 x x (𝓻 𝓐 x) ⊱) → ϕ x (𝓻 𝓐 x) u ≈⟨ 𝓑 x x (𝓻 𝓐 x) ⟩ ψ x (𝓻 𝓐 x) u)
    × ((u : ⊰ 𝓑 x x (𝓻 𝓐 x) ⊱) → u ≈⟨ 𝓑 x x (𝓻 𝓐 x) ⟩ ψ x (𝓻 𝓐 x) u))
       ≃⟨ Σ-bicong _ _ (≃-sym (curry-uncurry fe))
           (λ _ → Σ-change-of-variable-≃ _ (≃-sym (curry-uncurry fe))) ⟩
    (Σ ϕ ꞉ (((y , p) : fan 𝓐 x) → ⊰ 𝓑 x x (𝓻 𝓐 x) ⊱ → ⊰ 𝓑 x y p ⊱)
    , Σ ψ ꞉ (((y , p) : fan 𝓐 x) → ⊰ 𝓑 y y (𝓻 𝓐 y) ⊱ → ⊰ 𝓑 x y p ⊱)
    , ((u : ⊰ 𝓑 x x (𝓻 𝓐 x) ⊱)
     → ϕ (x , (𝓻 𝓐 x)) u ≈⟨ 𝓑 x x (𝓻 𝓐 x) ⟩ ψ (x , (𝓻 𝓐 x)) u)
    × ((u : ⊰ 𝓑 x x (𝓻 𝓐 x) ⊱) → u ≈⟨ 𝓑 x x (𝓻 𝓐 x) ⟩ ψ (x , (𝓻 𝓐 x)) u))
       ≃⟨ Σ-bicong _ _ (prop-indexed-product (x , 𝓻 𝓐 x) (fe _ _) (is-ua-𝓐 x))
           (λ _ → Σ-change-of-variable-≃ _
            (prop-indexed-product (x , 𝓻 𝓐 x) (fe _ _) (is-ua-𝓐 x))) ⟩
    (Σ ϕ ꞉ (⊰ 𝓑 x x (𝓻 𝓐 x) ⊱ → ⊰ 𝓑 x x (𝓻 𝓐 x) ⊱)
    , Σ ψ ꞉ (⊰ 𝓑 x x (𝓻 𝓐 x) ⊱ → ⊰ 𝓑 x x (𝓻 𝓐 x) ⊱)
    , ((u : ⊰ 𝓑 x x (𝓻 𝓐 x) ⊱) → ϕ u ≈⟨ 𝓑 x x (𝓻 𝓐 x) ⟩ ψ u)
    × ((u : ⊰ 𝓑 x x (𝓻 𝓐 x) ⊱) → u ≈⟨ 𝓑 x x (𝓻 𝓐 x) ⟩ ψ u))
       ≃⟨by-definition⟩
    (Σ ϕ ꞉ (⊰ 𝓑 x x (𝓻 𝓐 x) ⊱ → ⊰ 𝓑 x x (𝓻 𝓐 x) ⊱)
    , Σ ψ ꞉ (⊰ 𝓑 x x (𝓻 𝓐 x) ⊱ → ⊰ 𝓑 x x (𝓻 𝓐 x) ⊱)
    , (ϕ ≈⟨ ⊰ 𝓑 x x (𝓻 𝓐 x) ⊱ ➙ 𝓑 x x (𝓻 𝓐 x) ⟩ ψ)
    × (id ≈⟨ ⊰ 𝓑 x x (𝓻 𝓐 x) ⊱ ➙ 𝓑 x x (𝓻 𝓐 x) ⟩ ψ))
       ≃⟨ Σ-cong (λ _ → ≃-sym Σ-assoc) ⟩
    (Σ ϕ ꞉ (⊰ 𝓑 x x (𝓻 𝓐 x) ⊱ → ⊰ 𝓑 x x (𝓻 𝓐 x) ⊱)
    , Σ (ψ , _) ꞉ fan (⊰ 𝓑 x x (𝓻 𝓐 x) ⊱ ➙ 𝓑 x x (𝓻 𝓐 x)) ϕ
    , (id ≈⟨ ⊰ 𝓑 x x (𝓻 𝓐 x) ⊱ ➙ 𝓑 x x (𝓻 𝓐 x) ⟩ ψ))
       ≃⟨ Σ-cong (λ - → prop-indexed-sum (center (II x -))
           (singletons-are-props (II x -))) ⟩
    ((Σ ϕ ꞉ (⊰ 𝓑 x x (𝓻 𝓐 x) ⊱ → ⊰ 𝓑 x x (𝓻 𝓐 x) ⊱)
    , (id ≈⟨ ⊰ 𝓑 x x (𝓻 𝓐 x) ⊱ ➙ 𝓑 x x (𝓻 𝓐 x) ⟩ ϕ)))
       ≃⟨by-definition⟩
    fan (⊰ 𝓑 x x (𝓻 𝓐 x) ⊱ ➙ 𝓑 x x (𝓻 𝓐 x)) id ■

\end{code}

Additionally, we observe that lens structure is a property of the underlying
family. 

\begin{code}

oplax-lens-structure-is-a-property
 : FunExt
 → (𝓐 : refl-graph 𝓤 𝓥) (𝓑 : ⊰ 𝓐 ⊱ → refl-graph 𝓤' 𝓥')
 → is-univalent-refl-graph 𝓐
 → ((x : ⊰ 𝓐 ⊱) → is-univalent-refl-graph (𝓑 x))
 → is-prop (oplax-covariant-lens-structure 𝓐 𝓑)
oplax-lens-structure-is-a-property fe 𝓐 𝓑 is-ua-𝓐 is-ua-𝓑
 = singletons-are-props (oplax-lens-structure-is-contr fe 𝓐 𝓑 is-ua-𝓐 is-ua-𝓑)

lax-lens-structure-is-a-property
 : FunExt
 → (𝓐 : refl-graph 𝓤 𝓥) (𝓑 : ⊰ 𝓐 ⊱ → refl-graph 𝓤' 𝓥')
 → is-univalent-refl-graph 𝓐
 → ((x : ⊰ 𝓐 ⊱) → is-univalent-refl-graph (𝓑 x))
 → is-prop (lax-contravariant-lens-structure 𝓐 𝓑)
lax-lens-structure-is-a-property fe 𝓐 𝓑 is-ua-𝓐 is-ua-𝓑
 = singletons-are-props (lax-lens-structure-is-contr fe 𝓐 𝓑 is-ua-𝓐 is-ua-𝓑)

bivariant-lens-structure-is-a-property
 : FunExt
 → (𝓐 : refl-graph 𝓤 𝓥) (𝓑 : (x y : ⊰ 𝓐 ⊱) → (x ≈⟨ 𝓐 ⟩ y) → refl-graph 𝓤' 𝓥')
 → is-univalent-refl-graph 𝓐
 → ((x y : ⊰ 𝓐 ⊱) (p : x ≈⟨ 𝓐 ⟩ y) → is-univalent-refl-graph (𝓑 x y p))
 → is-prop (bivariant-midpoint-lens-structure 𝓐 𝓑)
bivariant-lens-structure-is-a-property fe 𝓐 𝓑 is-ua-𝓐 is-ua-𝓑
 = singletons-are-props
    (bivariant-lens-structure-is-contr fe 𝓐 𝓑 is-ua-𝓐 is-ua-𝓑)

\end{code}
