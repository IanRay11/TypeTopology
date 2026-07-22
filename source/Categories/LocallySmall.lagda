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
open import Categories.Notation.Pre hiding (⌜_⌝)
open import Categories.Notation.Wild hiding (⌜_⌝)
open import Notation.UnderlyingType

module Categories.LocallySmall where

module _ {𝓤 𝓥 : Universe} where

 is-locally-small : (C : Precategory 𝓤 𝓥) → (𝓤 ⁺) ⊔ 𝓥 ̇
 is-locally-small C = (x y : obj C) → Σ h ꞉ 𝓤 ̇ , hom x y ≃ h
  where
   open PrecategoryNotation C

Locally-Small-Precategory : (𝓤 𝓥 : Universe) → (𝓤 ⊔ 𝓥)⁺ ̇
Locally-Small-Precategory 𝓤 𝓥 = Σ C ꞉ Precategory 𝓤 𝓥 , is-locally-small C

\end{code}

We give some boiler-plate that allows us to work with small-homs.

\begin{code}

module _ ((C , loc) : Locally-Small-Precategory 𝓤 𝓥) where

 open PrecategoryNotation C

 small-hom : (x y : obj C) → 𝓤 ̇
 small-hom x y = pr₁ (loc x y)

 small-hom-equiv : {x y : obj C}
                 → hom x y ≃ small-hom x y
 small-hom-equiv {x} {y} = pr₂ (loc x y)

 small-hom-→ : {x y : obj C}
             → hom x y → small-hom x y 
 small-hom-→ = ⌜ small-hom-equiv ⌝

 small-id : {x : obj C}
          → small-hom x x
 small-id = small-hom-→ 𝒊𝒅

 small-hom-← : {x y : obj C}
             → small-hom x y → hom x y
 small-hom-← {x} {y} = ⌜ small-hom-equiv ⌝⁻¹

 small-hom-comp : {x y z : obj C}
                → small-hom x y
                → small-hom y z
                → small-hom x z
 small-hom-comp {x} {y} {z} f g
  = small-hom-→ (small-hom-← g ◦ small-hom-← f)

 small-hom-id : {x y : obj C}
              → (f : small-hom x y)
              → small-hom-comp f small-id ＝ f
 small-hom-id {x} {y} f
  = small-hom-comp f small-id                            ＝⟨refl⟩
    small-hom-→ (small-hom-← small-id ◦ small-hom-← f)   ＝⟨ I ⟩
    small-hom-→ (𝒊𝒅 ◦ small-hom-← f)                     ＝⟨ II ⟩
    small-hom-→ (small-hom-← f)                          ＝⟨ III ⟩
    f                                                    ∎
  where
   I = ap (λ - → small-hom-→ (- ◦ small-hom-← f))
          (inverses-are-retractions' small-hom-equiv 𝒊𝒅)
   II = ap small-hom-→ (𝒊𝒅-is-left-neutral (small-hom-← f))
   III = inverses-are-sections' small-hom-equiv f

 small-hom-func
  : {x y z w : obj C}
  → (f : small-hom x y) (g : hom y z) (h : hom z w)
  → small-hom-comp f (small-hom-→ (h ◦ g))
  ＝ small-hom-comp (small-hom-comp f (small-hom-→ g)) (small-hom-→ h)
 small-hom-func {x} {y} {z} {w} f g h
  = small-hom-comp f (small-hom-→ (h ◦ g))                            ＝⟨refl⟩
    small-hom-→ (small-hom-← (small-hom-→ (h ◦ g)) ◦ small-hom-← f)   ＝⟨ I ⟩
    small-hom-→ ((h ◦ g) ◦ small-hom-← f)                             ＝⟨ II ⟩
    small-hom-→ (h ◦ (g ◦ small-hom-← f))                             ＝⟨ III ⟩
    small-hom-→ (h ◦ (small-hom-← (small-hom-→ g) ◦ small-hom-← f))   ＝⟨ IV ⟩
    small-hom-→ (h
     ◦ small-hom-← (small-hom-→ (small-hom-← (small-hom-→ g) ◦ small-hom-← f)))                                                                       ＝⟨refl⟩
    small-hom-→ (h ◦ small-hom-← (small-hom-comp f (small-hom-→ g)))  ＝⟨ V ⟩
    small-hom-→ (small-hom-← (small-hom-→ h)
                 ◦ small-hom-← (small-hom-comp f (small-hom-→ g)))    ＝⟨refl⟩
    small-hom-comp (small-hom-comp f (small-hom-→ g)) (small-hom-→ h) ∎
  where
   I = ap (λ - → small-hom-→ (- ◦ small-hom-← f) )
          (inverses-are-retractions' small-hom-equiv (h ◦ g))
   II = ap small-hom-→ (assoc (small-hom-← f) g h ⁻¹)
   III = ap (λ - → small-hom-→ (h ◦ (- ◦ small-hom-← f)))
            (inverses-are-retractions' small-hom-equiv g ⁻¹)
   IV = ap (λ - → small-hom-→ (h ◦ -))
           (inverses-are-retractions' small-hom-equiv
             (small-hom-← (small-hom-→ g) ◦ small-hom-← f) ⁻¹)
   V = ap
       (λ - → small-hom-→ (- ◦ small-hom-← (small-hom-comp f (small-hom-→ g))))
       (inverses-are-retractions' small-hom-equiv h ⁻¹)

\end{code}


