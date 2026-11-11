Ian Ray. 29th October 2026.

...

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons
open import UF.Univalence

module UF.DedekindInfiniteSet
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : Prop-Ext)
        (ua : Univalence)
       where

private
 fe' : FunExt
 fe' 𝓤 𝓥 = fe {𝓤} {𝓥}

open import MLTT.Spartan
open import MLTT.Plus-Properties
open import UF.Base
open import UF.DiscreteAndSeparated
open import UF.Embeddings
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.Equiv-FunExt
open import UF.Subsingletons-FunExt
open import UF.Sets
open import Factorial.PlusOneLC
open import ReflexiveGraphs.Constructions using
             (refl-graph-×; cotensor-refl-graph; Δ; total-refl-graph)
open import ReflexiveGraphs.Displayed
open import ReflexiveGraphs.DisplayedUnivalent
open import ReflexiveGraphs.Lenses
open import ReflexiveGraphs.Type
open import ReflexiveGraphs.UnbiasedLenses
open import ReflexiveGraphs.Univalent
open import ReflexiveGraphs.UnivalentClosureProperties
open import ReflexiveGraphs.UnivalentFamilies

\end{code}

TODO: Check imports.

TODO: Spellcheck.

We define the type of dedekind infinite sets.

\begin{code}

record is-dedekind-infinite-set (I : 𝓤 ̇) : 𝓤 ⁺ ̇
 where
 field
  is-set-Inf : is-set I
  el-Inf : I
  map-Inf : I → I
  map-inj : (x y : I) → map-Inf x ＝ map-Inf y → x ＝ y
  el-not-img : (x : I) → ¬ (map-Inf x ＝ el-Inf)

Dedekind-Infinite : (𝓤 : Universe) → 𝓤 ⁺ ̇
Dedekind-Infinite 𝓤 = Σ I ꞉ 𝓤 ̇ , is-dedekind-infinite-set I

\end{code}

We will now give some examples of large* dedekind infinite sets.

*By large we mean the underlying type itself lives in a successor universe.*

\begin{code}

Pointed : (𝓤 : Universe) → 𝓤 ⁺ ̇
Pointed 𝓤 = Σ X ꞉ 𝓤 ̇ , X

_≅∙_ : Pointed 𝓤 → Pointed 𝓤 → 𝓤 ̇
(X , x) ≅∙ (Y , y) = Σ e ꞉ X ≃ Y , ⌜ e ⌝ x ＝ y

Pointed-＝-characterization : (𝓧 𝓨 : Pointed 𝓤)
                            → (𝓧 ＝ 𝓨) ≃ (𝓧 ≅∙ 𝓨)
Pointed-＝-characterization 𝓧 𝓨 = {!!}

point∙ : Pointed 𝓤
point∙ = (𝟙 , ⋆)

succ∙ : Pointed 𝓤 → Pointed 𝓤
succ∙ {𝓤} (X , x) = ((X + 𝟙{𝓤}) , inl x)

point-is-not-succ∙ : (𝓧 : Pointed 𝓤)
                   → ¬ (point∙ ≅∙ succ∙ 𝓧)
point-is-not-succ∙ (X , x) (e , e-point) = ⌜ X≃𝟘 ⌝ x
 where
  X≃𝟘 : X ≃ 𝟘
  X≃𝟘 = adjoined-point-contractible-implies-empty X (≃-sym e)

succ∙-injective : (𝓧 𝓨 : Pointed 𝓤)
                → succ∙ 𝓧 ≅∙ succ∙ 𝓨
                → 𝓧 ≅∙ 𝓨
succ∙-injective (X , x) (Y , y) (e , e-point) = (+𝟙-cancellable e , I)
 where
 {- TODO: Either redo the proof here so you can use the properties you need or
          refactor the existing code -}
  I : ⌜ +𝟙-cancellable e ⌝ x ＝ y
  I = inl-lc (inl (⌜ +𝟙-cancellable e ⌝ x)      ＝⟨ {!!} ⟩
              {!!} (inl x)                      ＝⟨ {!!} ⟩
              ⌜ e ⌝ (inl x)                     ＝⟨ e-point ⟩
              inl y                             ∎)

\end{code}


