Martin Escardo, 27 April 2014.

With additions 18th December 2017, and slightly refactored
15th May 2025, with minor improvements in the code.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan

module UF.PropIndexedPiSigma
        {X : 𝓤 ̇ }
        {Y : X → 𝓥 ̇ }
       where

open import UF.Base
open import UF.Equiv
open import UF.FunExt
open import UF.Subsingletons
open import UF.Subsingletons-Properties

private
 transport-lemma : {x : X} {y : Y x} (i : is-prop X)
                 → transport Y (i x x) y ＝ y
 transport-lemma {x} {y} i = ap (λ - → transport Y - y)
                                (identifications-in-props-are-refl i x)

module _ (a : X) where

 Π-proj : Π Y → Y a
 Π-proj f = f a

 Π-proj⁻¹ : is-prop X → Y a → Π Y
 Π-proj⁻¹ i y x = transport Y (i a x) y

 Π-proj-is-equiv : funext 𝓤 𝓥
                 → is-prop X
                 → is-equiv Π-proj
 Π-proj-is-equiv fe i = qinvs-are-equivs Π-proj (Π-proj⁻¹ i , η , ε)
  where
   ε : Π-proj ∘ Π-proj⁻¹ i ∼ id
   ε y =
    (Π-proj ∘ Π-proj⁻¹ i) y ＝⟨ refl ⟩
    transport Y (i a a) y   ＝⟨ transport-lemma i ⟩
    transport Y refl y      ＝⟨ refl ⟩
    y                       ∎

   II : (f : Π Y) {x : X} → x ＝ a → transport Y (i a x) (f a) ＝ f x
   II f refl =
    transport Y (i a a) (f a) ＝⟨ transport-lemma i ⟩
    transport Y refl (f a)    ＝⟨ refl ⟩
    f a                       ∎

   III : (f : Π Y) → Π-proj⁻¹ i (Π-proj f) ∼ f
   III f x =
    Π-proj⁻¹ i (Π-proj f) x   ＝⟨ refl ⟩
    transport Y (i a x) (f a) ＝⟨ II f (i x a) ⟩
    f x                       ∎

   η : Π-proj⁻¹ i ∘ Π-proj ∼ id
   η φ = dfunext fe (III φ)

 prop-indexed-product : funext 𝓤 𝓥
                      → is-prop X
                      → Π Y ≃ Y a
 prop-indexed-product fe i = Π-proj , Π-proj-is-equiv fe i

empty-indexed-product-is-𝟙 : funext 𝓤 𝓥
                           → (X → 𝟘 {𝓦})
                           → Π Y ≃ 𝟙 {𝓣}
empty-indexed-product-is-𝟙 {𝓦} {𝓣} fe v = γ
 where
  g : 𝟙 → Π Y
  g ⋆ x = unique-from-𝟘 {𝓥} {𝓦} (v x)

  η : (u : 𝟙) → ⋆ ＝ u
  η ⋆ = refl

  ε : (φ : Π Y) → g ⋆ ＝ φ
  ε φ = dfunext fe u
   where
    u : (x : X) → g (unique-to-𝟙 φ) x ＝ φ x
    u x = unique-from-𝟘 (v x)

  γ : Π Y ≃ 𝟙 {𝓣}
  γ = qinveq unique-to-𝟙 (g , ε , η)

\end{code}

Added 18th December 2017.

\begin{code}

module _ (a : X) where

 Σ-in : Y a → Σ Y
 Σ-in y = (a , y)

 Σ-in⁻¹ : is-prop X → Σ Y → Y a
 Σ-in⁻¹ i (x , y) = transport Y (i x a) y

 Σ-in-is-equiv : is-prop X → is-equiv Σ-in
 Σ-in-is-equiv i = qinvs-are-equivs Σ-in (Σ-in⁻¹ i , η , ε)
  where
   η : (y : Y a) → Σ-in⁻¹ i (Σ-in y) ＝ y
   η y =
    Σ-in⁻¹ i (Σ-in y)     ＝⟨ refl ⟩
    transport Y (i a a) y ＝⟨ transport-lemma i ⟩
    transport Y refl y    ＝⟨ refl ⟩
    y                     ∎

   ε : (σ : Σ Y) → Σ-in (Σ-in⁻¹ i σ) ＝ σ
   ε (x , y) =
    Σ-in (Σ-in⁻¹ i (x , y))     ＝⟨ refl ⟩
    (a , transport Y (i x a) y) ＝⟨ to-Σ-＝ (i a x , I (i x a)) ⟩
    (x , y)                     ∎
     where
      I : x ＝ a → transport Y (i a x) (transport Y (i x a) y) ＝ y
      I refl =
       transport Y (i a a) (transport Y (i a a) y) ＝⟨ transport-lemma i ⟩
       transport Y (i a a) y                       ＝⟨ transport-lemma i ⟩
       y                                           ∎

 prop-indexed-sum : is-prop X → Σ Y ≃ Y a
 prop-indexed-sum i = ≃-sym (Σ-in , Σ-in-is-equiv i)

empty-indexed-sum-is-𝟘 : (X → 𝟘 {𝓦}) → Σ Y ≃ (𝟘 {𝓣})
empty-indexed-sum-is-𝟘 {𝓦} {𝓣} φ = qinveq f (g , η , ε)
 where
  f : Σ Y → 𝟘
  f (x , y) = 𝟘-elim (φ x)

  g : 𝟘 → Σ Y
  g = unique-from-𝟘

  ε : (x : 𝟘) → f (g x) ＝ x
  ε = 𝟘-induction

  η : (σ : Σ Y) → g (f σ) ＝ σ
  η (x , y) = 𝟘-elim (φ x)

\end{code}
