Ian Ray, 7 February 2024

Singleton Properties. Of course there are alot more we can add to this file.
For now we will show that singletons are closed under Σ types and equivalence.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.Equiv
open import UF.Equiv-FunExt
open import UF.EquivalenceExamples
open import UF.FunExt
open import UF.Retracts
open import UF.Subsingletons

module UF.Singleton-Properties where

Σ-is-singleton : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
               → is-singleton X
               → ((x : X) → is-singleton (A x))
               → is-singleton (Σ A)
Σ-is-singleton {X = X} {A = A} (c , C) h = ((c , center (h c)) , Σ-centrality)
 where
  Σ-centrality : is-central (Σ A) (c , center (h c))
  Σ-centrality (x , a) = ⌜ Σ-＝-≃ ⌝⁻¹ (C x , p)
   where
    p = transport A (C x) (center (h c)) ＝⟨ centrality (h x)
                                                (transport A (C x)
                                                     (center (h c))) ⁻¹ ⟩
        center (h x)                     ＝⟨ centrality (h x) a ⟩
        a                                ∎

≃-is-singleton : FunExt
               → {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
               → is-singleton X
               → is-singleton Y
               → is-singleton (X ≃ Y)
≃-is-singleton fe i j = pointed-props-are-singletons
                         (singleton-≃ i j)
                         (≃-is-prop fe (singletons-are-props j))

\end{code}
