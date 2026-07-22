Ian Ray. 07/21/2026.

We define the hom functor.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.Equiv
open import UF.FunExt
open import UF.Sets
open import UF.Sets-Properties
open import Categories.Functor
open import Categories.Functor-Composition
open import Categories.LocallySmall
open import Categories.Pre
open import Categories.Sets
open import Categories.Wild
open import Categories.Notation.Functor 
open import Categories.Notation.Pre hiding (⌜_⌝)
open import Categories.Notation.Wild hiding (⌜_⌝)

module Categories.HomFunctor where

module _ (fe : Fun-Ext) (𝓧@(X , loc) : Locally-Small-Precategory 𝓤 𝓥) where

 open PrecategoryNotation X

 covariant-hom : (x : obj X) → Functor X (Cat-Set fe 𝓤)
 covariant-hom x
  = record{F₀ = λ x'
              → (small-hom 𝓧 x x' ,
                 equiv-to-set (≃-sym (small-hom-equiv 𝓧)) (hom-is-set X)) ;
           F₁ = λ {a} {b} (f : hom a b) (g : small-hom 𝓧 x a)
              → small-hom-comp 𝓧 g (small-hom-→ 𝓧 f) ;
           id-preserved = λ a → dfunext fe (small-hom-id 𝓧) ;
           distributivity = λ {a} {b} {c} (g : hom b c) (f : hom a b)
                          → dfunext fe (λ - → small-hom-func 𝓧 - f g)}
 


