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

module _ (fe : Fun-Ext) (X : Precategory 𝓤 𝓥) where

 open PrecategoryNotation X

 covariant-hom : (x : obj X) → Functor X (Pre-Cat-Set fe 𝓥)
 covariant-hom x
  = record
    {F₀ = λ a → (hom x a , hom-is-set X) ;
     F₁ = λ {a} {b} (g : hom a b) → (λ (f : hom x a) → g ◦ f) ;
     id-preserved = λ a → dfunext fe 𝒊𝒅-is-left-neutral ;
     distributivity = λ h g → dfunext fe (λ f → assoc f g h ⁻¹)}

\end{code}

We can also define a more generalized hom functor in case we have a locally
small precategory.

\begin{code}

module _ (𝓣 : Universe)
         (fe : Fun-Ext)
         (𝓧@(X , loc) : Locally-Small-Precategory 𝓤 𝓥 𝓣)
       where

 open PrecategoryNotation X
 open Local-Smallness-Properties 𝓣 𝓧

 small-covariant-hom : (x : obj X) → Functor X (Pre-Cat-Set fe 𝓣)
 small-covariant-hom x
  = record
    {F₀ = λ a → (small-hom x a
                 , equiv-to-set (≃-sym small-hom-equiv) (hom-is-set X)) ;
     F₁ = λ {a} {b} (g : hom a b) (f : small-hom x a)
        → (small-hom-→ g) ∘small f ;
     id-preserved = λ a → dfunext fe small-hom-id ;
     distributivity = λ {a} {b} {c} (g : hom b c) (f : hom a b)
                    → dfunext fe (λ - → small-hom-distr-assoc - f g)}

 
