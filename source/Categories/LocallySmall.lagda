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

is-locally_small : (𝓣 : Universe) (C : Precategory 𝓤 𝓥) → 𝓤 ⊔ 𝓥 ⊔ (𝓣 ⁺) ̇
is-locally 𝓣 small C = (x y : obj C) → Σ h ꞉ 𝓣 ̇ , hom x y ≃ h
 where
  open PrecategoryNotation C

Locally-Small-Precategory : (𝓤 𝓥 𝓣 : Universe) → (𝓤 ⊔ 𝓥 ⊔ 𝓣) ⁺ ̇
Locally-Small-Precategory 𝓤 𝓥 𝓣 = Σ C ꞉ Precategory 𝓤 𝓥 , is-locally 𝓣 small C

\end{code}

We give some boiler-plate that allows us to work with small-homs.

\begin{code}

module Local-Smallness-Properties
         (𝓣 : Universe) ((C , loc) : Locally-Small-Precategory 𝓤 𝓥 𝓣)
       where

 open PrecategoryNotation C

 small-hom : (x y : obj C) → 𝓣 ̇
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

 _∘small_ : {x y z : obj C}
          → small-hom y z
          → small-hom x y
          → small-hom x z
 g ∘small f
  = small-hom-→ (small-hom-← g ◦ small-hom-← f)

 small-hom-id : {x y : obj C}
              → (f : small-hom x y)
              → small-id ∘small f ＝ f
 small-hom-id {x} {y} f
  = small-id ∘small f                                    ＝⟨refl⟩
    small-hom-→ (small-hom-← small-id ◦ small-hom-← f)   ＝⟨ I ⟩
    small-hom-→ (𝒊𝒅 ◦ small-hom-← f)                     ＝⟨ II ⟩
    small-hom-→ (small-hom-← f)                          ＝⟨ III ⟩
    f                                                    ∎
  where
   I = ap (λ - → small-hom-→ (- ◦ small-hom-← f))
          (inverses-are-retractions' small-hom-equiv 𝒊𝒅)
   II = ap small-hom-→ (𝒊𝒅-is-left-neutral (small-hom-← f))
   III = inverses-are-sections' small-hom-equiv f

 small-hom-distr-assoc
  : {x y z w : obj C}
  → (f : small-hom x y) (g : hom y z) (h : hom z w)
  → (small-hom-→ (h ◦ g)) ∘small f 
  ＝ (small-hom-→ h) ∘small ((small-hom-→ g) ∘small f) 
 small-hom-distr-assoc f g h
  = (small-hom-→ (h ◦ g)) ∘small f                                    ＝⟨refl⟩
    small-hom-→ (small-hom-← (small-hom-→ (h ◦ g)) ◦ small-hom-← f)   ＝⟨ I ⟩
    small-hom-→ ((h ◦ g) ◦ small-hom-← f)                             ＝⟨ II ⟩
    small-hom-→ (h ◦ (g ◦ small-hom-← f))                             ＝⟨ III ⟩
    small-hom-→ (h ◦ (small-hom-← (small-hom-→ g) ◦ small-hom-← f))   ＝⟨ IV ⟩
{-  small-hom-→
     (h ◦ small-hom-← (small-hom-→ (small-hom-← (small-hom-→ g)
        ◦ small-hom-← f)))                                                                                                                          ＝⟨refl⟩ -}
    small-hom-→ (h ◦ small-hom-← ((small-hom-→ g) ∘small f))          ＝⟨ V ⟩
{-  small-hom-→
     (small-hom-← (small-hom-→ h) ◦ small-hom-← ((small-hom-→ g) ∘small f))                                                                         ＝⟨refl⟩ -}
    (small-hom-→ h) ∘small ((small-hom-→ g) ∘small f)                 ∎
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
       (λ - → small-hom-→ (- ◦ small-hom-← ((small-hom-→ g) ∘small f)))
       (inverses-are-retractions' small-hom-equiv h ⁻¹)

\end{code}


