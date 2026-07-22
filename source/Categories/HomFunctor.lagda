Ian Ray. 07/21/2026.

We define the hom functor.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.FunExt
open import Categories.Functor
open import Categories.Functor-Composition
open import Categories.Pre
open import Categories.Sets
open import Categories.Wild
open import Categories.Notation.Functor
open import Categories.Notation.Pre
open import Categories.Notation.Wild

module Categories.HomFunctor where

module _ (fe : Fun-Ext) (X : Precategory 𝓤 𝓥) where

 open PrecategoryNotation X

 covariant-hom : (x : obj X) → Functor X (Cat-Set fe 𝓤)
 covariant-hom x = record{F₀ = λ x' → ({!!} , {!!}) ;
                          F₁ = {!!} ;
                          id-preserved = {!!} ;
                          distributivity = {!!}}

{- TODO locally small categories -}
 


