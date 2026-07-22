Ian Ray. 07/21/2026.

We define a locally small category.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.Equiv
open import UF.FunExt
open import Categories.Functor
open import Categories.Functor-Composition
open import Categories.Pre
open import Categories.Sets
open import Categories.Wild
open import Categories.Notation.Functor
open import Categories.Notation.Pre
open import Categories.Notation.Wild

module Categories.LocallySmall where

module _ {𝓤 𝓥 : Universe} where

 is-locally-small : (C : Precategory 𝓤 𝓥) → (𝓤 ⁺) ⊔ 𝓥 ̇
 is-locally-small C = (x y : obj C) → Σ h ꞉ 𝓤 ̇ , hom x y ≃ h
  where
   open PrecategoryNotation C

Locally-Small-Precat : (𝓤 𝓥 : Universe) → (𝓤 ⊔ 𝓥)⁺ ̇
Locally-Small-Precat 𝓤 𝓥 = Σ C ꞉ Precategory 𝓤 𝓥 , is-locally-small C
