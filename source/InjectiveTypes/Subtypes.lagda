Martin Escardo 21st October 2024

A necessary and sufficient condition for the injectivity of a subtype
of an injective type.s

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.Univalence

module InjectiveTypes.Subtypes
        (ua : Univalence)
        (𝓤 : Universe)
       where

open import UF.Embeddings
open import UF.FunExt
open import UF.Retracts
open import UF.Subsingletons
open import UF.UA-FunExt

private
 fe : FunExt
 fe = Univalence-gives-FunExt ua

open import InjectiveTypes.Blackboard fe

module _ (D : 𝓤 ̇ )
         (P : D → 𝓥 ̇ )
         (P-is-prop-valued : (d : D) → is-prop (P d))
         (D-ainj : ainjective-type D 𝓦 𝓣)
       where

 necessary-condition-for-injectivity-of-subtype
  : ainjective-type (Σ P) (𝓤 ⊔ 𝓥) 𝓤
  → Σ f ꞉ (D → D) , ((d : D) → P (f d)) × ((d : D) → P d → f d ＝ d)
 necessary-condition-for-injectivity-of-subtype Σ-ainj = f , g , h
  where
   ρ : retract Σ P of D
   ρ = embedding-retract (Σ P) D pr₁ (pr₁-is-embedding P-is-prop-valued) Σ-ainj

   r : D → Σ P
   r = retraction ρ

   s : Σ P → D
   s = pr₁

   rs : r ∘ s ∼ id
   rs = retract-condition ρ

   f : D → D
   f = s ∘ r

   g : (d : D) → P (f d)
   g d = pr₂ (r d)

   fg : (d : D) (p : P d) → (f d , g d) ＝ (d , p)
   fg d p = f d , g d     ＝⟨ refl ⟩
            r (s (d , p)) ＝⟨ rs (d , p) ⟩
            (d , p)       ∎

   h : (d : D) → P d → f d ＝ d
   h d p = ap pr₁ (fg d p)

 sufficient-condition-for-injectivity-of-subtype
  : (Σ f ꞉ (D → D) , ((d : D) → P (f d)) × ((d : D) → P d → f d ＝ d))
  → ainjective-type (Σ P) 𝓦 𝓣
 sufficient-condition-for-injectivity-of-subtype (f , g , h)
  = retract-of-ainjective (Σ P) D D-ainj (r , s , rs)
  where
   r : D → Σ P
   r d = f d , g d

   s : Σ P → D
   s = pr₁

   rs : r ∘ s ∼ id
   rs (d , p) = r (s (d , p)) ＝⟨ refl ⟩
                r d           ＝⟨ refl ⟩
                f d , g d     ＝⟨ to-subtype-＝ P-is-prop-valued (h d p) ⟩
                d , p         ∎

\end{code}

The following choice of universes makes the condition trully
sufficient and necessary.

\begin{code}

module _ (D : 𝓤 ̇ )
         (P : D → 𝓥 ̇ )
         (P-is-prop-valued : (d : D) → is-prop (P d))
         (D-ainj : ainjective-type D (𝓤 ⊔ 𝓥) 𝓤)
       where

 necessary-and-sufficient-condition-for-injectivity-of-subtype
  : ainjective-type (Σ P) (𝓤 ⊔ 𝓥) 𝓤
  ↔ (Σ f ꞉ (D → D) , ((d : D) → P (f d)) × ((d : D) → P d → f d ＝ d))
 necessary-and-sufficient-condition-for-injectivity-of-subtype
  = necessary-condition-for-injectivity-of-subtype D P P-is-prop-valued D-ainj ,
    sufficient-condition-for-injectivity-of-subtype D P P-is-prop-valued D-ainj

\end{code}

TODO. Perhaps using aflabbiness we would get more general universe
levels.
