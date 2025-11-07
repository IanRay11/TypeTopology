Ian Ray. 7th November 2025.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module DURGs.DualityLenses where

open import MLTT.Spartan
open import DURGs.BasicConstructionsonReflexiveGraphs
open import DURGs.DisplayedReflexiveGraphs
open import DURGs.DisplayedUnivalentReflexiveGraphs
open import DURGs.Lenses
open import DURGs.ReflexiveGraphs
open import DURGs.UnivalentReflexiveGraphs

\end{code}

Duality involution is investigated for lenses.

\begin{code}

total-opposite-for-oplax-lenses : {𝓤' 𝓥' : Universe} (𝓐 : refl-graph 𝓤 𝓥)
                                → oplax-covariant-lens 𝓤' 𝓥' 𝓐
                                → lax-contravariant-lens 𝓤' 𝓥' (𝓐 ᵒᵖ)
total-opposite-for-oplax-lenses 𝓐 𝓑 = record
 { lens-fam = λ x → lens-fam x ᵒᵖ
 ; lens-pull = λ {x} {y} p u → lens-push p u
 ; lens-pull-R = λ {x} u → lens-push-R u
 }
 where
  open oplax-covariant-lens 𝓑

syntax total-opposite-for-oplax-lenses 𝓐 𝓑 = 𝓐 , 𝓑 ᵒᵖ

total-opposite-for-lax-lenses : {𝓤' 𝓥' : Universe} (𝓐 : refl-graph 𝓤 𝓥)
                              → lax-contravariant-lens 𝓤' 𝓥' 𝓐
                              → oplax-covariant-lens 𝓤' 𝓥' (𝓐 ᵒᵖ)
total-opposite-for-lax-lenses 𝓐 𝓑 = record
 { lens-fam = λ x → lens-fam x ᵒᵖ
 ; lens-push = λ {x} {y} p u → lens-pull p u
 ; lens-push-R = λ {x} u → lens-pull-R u
 }
 where
  open lax-contravariant-lens 𝓑

syntax total-opposite-for-lax-lenses 𝓐 𝓑 = 𝓐 , 𝓑 ₒₚ

\end{code}

This doesn't quite make sense...

private
 observation : {𝓤' 𝓥' : Universe} (𝓐 : refl-graph 𝓤 𝓥)
             → (𝓑 : oplax-covariant-lens 𝓤' 𝓥' 𝓐)
             → disp⁻ (𝓐 ᵒᵖ) , (𝓐 , 𝓑 ᵒᵖ) ＝ (disp⁺ 𝓐 , 𝓑) ᵒᵖ
 observation = ?
