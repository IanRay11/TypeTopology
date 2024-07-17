Martin Escardo, 17th July 2024.

Sequentially Hausdorff types.

Motivated by https://grossack.site/2024/07/03/life-in-johnstones-topological-topos

The idea in this file, and many files in TypeTopology, is that we are
working in an arbitrary topos, which may or may not be a topological
topos, and we are interested in proving things synthetically in
topological toposes.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module TypeTopology.SequentiallyHausdorff
        (fe₀ : funext₀)
       where

open import CoNaturals.Type
open import MLTT.Spartan
open import Notation.CanonicalMap
open import Taboos.BasicDiscontinuity fe₀
open import Taboos.WLPO

\end{code}

A topological space is sequentially Hausdorff if every sequence of
points converges to at most one point. In our synthetic setting, this
can be formulated as follows, following the above blog post by Chris
Grossack.

\begin{code}

is-sequentially-Hausdorff : 𝓤 ̇ → 𝓤 ̇
is-sequentially-Hausdorff X = (f g : ℕ∞ → X)
                            → ((n : ℕ) → f (ι n) ＝ g (ι n))
                            → f ∞ ＝ g ∞

\end{code}

If WLPO holds in our topos, then our topos is not topological, in any
conceivable sense, and no non-trivial type is sequentially Hausdorff.

\begin{code}

no-non-trivial-sequentially-Hausdorff-types-under-WLPO
 : WLPO
 → (X : 𝓤 ̇ )
 → (Σ (x₀ , x₁) ꞉ X × X , x₀ ≠ x₁)
 → ¬ is-sequentially-Hausdorff X
no-non-trivial-sequentially-Hausdorff-types-under-WLPO
 wlpo X ((x₀ , x₁), d) X-is-seq-Haus = III
 where
  f : ℕ∞ → X
  f u = x₀

  g' : (u : ℕ∞) → (u ＝ ∞) + (u ≠ ∞) → X
  g' u (inl _) = x₁
  g' u (inr _) = x₀

  g : ℕ∞ → X
  g u = g' u (wlpo u)

  I : (n : ℕ) (c : (ι n ＝ ∞) + (ι n ≠ ∞)) → g' (ι n) c ＝ x₀
  I n (inl e) = 𝟘-elim (∞-is-not-finite n (e ⁻¹))
  I n (inr _) = refl

  a : (n : ℕ) →  f (ι n) ＝ g (ι n)
  a n =  f (ι n) ＝⟨ refl ⟩
         x₀      ＝⟨ (I n (wlpo (ι n)))⁻¹ ⟩
         g (ι n) ∎

  II : (c : (∞ ＝ ∞) + (∞ ≠ ∞)) → g' ∞ c ＝ x₁
  II (inl _) = refl
  II (inr ν) = 𝟘-elim (ν refl)

  III : 𝟘
  III = d (x₀  ＝⟨ refl ⟩
           f ∞ ＝⟨ X-is-seq-Haus f g a ⟩
           g ∞ ＝⟨ II (wlpo ∞) ⟩
           x₁  ∎)

\end{code}

The reason WLPO doesn't hold topological toposes is that the negation
of WLPO is a weak continuity principle [1], which holds in topological
toposes. So it makes sense to investigate which sets are sequentially
Hausdorff assuming ¬ WLPO or stronger continuity principles.

[1] https://doi.org/10.1017/S096012951300042X

To begin with, we show that all totally separated types are
sequentially Hausdorff.

\begin{code}

open import TypeTopology.TotallySeparated
open import UF.DiscreteAndSeparated

totally-separated-types-are-sequentially-Hausdorff
 : ¬ WLPO
 → (X : 𝓤 ̇ )
 → is-totally-separated X
 → is-sequentially-Hausdorff X
totally-separated-types-are-sequentially-Hausdorff nwlpo X X-is-ts f g a = II
 where
  I : (p : X → 𝟚) → p (f ∞) ＝ p (g ∞)
  I p = I₃
   where
    I₀ : (n : ℕ) → p (f (ι n)) ＝ p (g (ι n))
    I₀ n = ap p (a n)

    I₁ : p (f ∞) ≠ p (g ∞) → WLPO
    I₁ = disagreement-taboo (p ∘ f) (p ∘ g) I₀

    I₂ : ¬ (p (f ∞) ≠ p (g ∞))
    I₂ = contrapositive I₁ nwlpo

    I₃ : p (f ∞) ＝ p (g ∞)
    I₃ = 𝟚-is-¬¬-separated (p (f ∞)) (p (g ∞)) I₂

  II : f ∞ ＝ g ∞
  II = X-is-ts I

\end{code}

There are plenty of totally separated types. For example, the types 𝟚
and ℕ are totally separated, and the totally separated types are
closed under products (and hence function spaces and more generally
form an exponential ideal) and under retracts, as proved in the above
import TypeTopology.TotallySeparated.

But there are also counterexamples, which, in particular, show that
totally separated types are not necessarily closed under sums.

\begin{code}

import TypeTopology.FailureOfTotalSeparatedness

\end{code}

It is a fact that the types defined in the above import are not
sequentially Hausdorff in Johnstone's topological topos.

TODO. Prove this synthetically here, assuming ¬ WLPO. It is not
possible to prove this without assuming anything, given what we proved
above. I think I know how to prove this, but I haven't tested this
here yet.
