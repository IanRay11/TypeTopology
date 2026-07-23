Ian Ray. 07/21/2026.

We define the the Precategory of sets relative to a universe.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.Sets
open import UF.Sets-Properties
open import UF.FunExt
open import Categories.Functor
open import Categories.Functor-Composition
open import Categories.Pre
open import Categories.Wild
open import Categories.Notation.Functor
open import Categories.Notation.Pre
open import Categories.Notation.Wild

module Categories.Sets where

module _ (fe : Fun-Ext) where

 Pre-Cat-Set : (𝓤 : Universe) → Precategory (𝓤 ⁺) 𝓤
 Pre-Cat-Set 𝓤 = (I , λ X Y → Π-is-set fe (λ _ → underlying-set-is-set Y))
  where
   I : WildCategory (𝓤 ⁺) 𝓤
   I = record
        {obj = hSet 𝓤 ;
         hom = λ X Y → underlying-set X → underlying-set Y ;
         𝒊𝒅 = id ;
         _◦_ = _∘_ ;
         𝒊𝒅-is-left-neutral = ∼-refl ;
         𝒊𝒅-is-right-neutral = ∼-refl ;
         assoc = λ _ _ _ → refl}
  
