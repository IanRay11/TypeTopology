Martin Escardo, 7 May 2014, with additions 25th July 2024.

For any function f : ℕ∞ → ℕ, it is decidable whether f is non-continuous.

  (f : ℕ∞ → ℕ) → ¬ continuous f + ¬¬ continuous f.

Based on the paper

[1] Martin Escardo. Constructive decidability of classical continuity.
    Mathematical Structures in Computer Science , Volume 25,
    October 2015 , pp. 1578 - 1589
    https://doi.org/10.1017/S096012951300042X

The title of this paper is a bit misleading. It should probably have
been called "Decidability of non-continuity".

\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import MLTT.Spartan
open import UF.FunExt

module TypeTopology.DecidabilityOfNonContinuity (fe : funext 𝓤₀ 𝓤₀) where

open import CoNaturals.Type
open import MLTT.Two-Properties
open import Notation.CanonicalMap
open import NotionsOfDecidability.Decidable
open import NotionsOfDecidability.SemiDecidable
open import TypeTopology.ADecidableQuantificationOverTheNaturals fe
open import UF.DiscreteAndSeparated

Lemma-3·1 : (q : ℕ∞ → ℕ∞ → 𝟚)
          → is-decidable ((m : ℕ) → ¬ ((n : ℕ) → q (ι m) (ι n) ＝ ₁))
Lemma-3·1 q = claim₄
 where
  A : ℕ∞ → 𝓤₀ ̇
  A u = (n : ℕ) → q u (ι n) ＝ ₁

  claim₀ :  (u : ℕ∞) → is-decidable (A u)
  claim₀ u = Theorem-8·2 (q u)

  p : ℕ∞ → 𝟚
  p = indicator-map claim₀

  claim₁ : is-decidable ((n : ℕ) → p (ι n) ＝ ₁)
  claim₁ = Theorem-8·2 p

  claim₂ : ((n : ℕ) → ¬ A (ι n)) → (n : ℕ) → p (ι n) ＝ ₁
  claim₂ φ n = different-from-₀-equal-₁
                (λ v → φ n (indicator-property₀ claim₀ (ι n) v))

  claim₃ : ((n : ℕ) → p (ι n) ＝ ₁) → (n : ℕ) → ¬ A (ι n)
  claim₃ f n = indicator-property₁ claim₀ (ι n) (f n)

  claim₄ : is-decidable ((n : ℕ) → ¬ (A (ι n)))
  claim₄ = map-decidable claim₃ claim₂ claim₁

\end{code}

Omitting the inclusion function, or coercion,

   ι : ℕ → ℕ∞,

a map f : ℕ∞ → ℕ is called continuous iff

   ∃ m. ∀ n ≥ m. f n ＝ f ∞,

where m and n range over the natural numbers.

The negation of this statement is equivalent to

   ∀ m. ¬ ∀ n ≥ m. f n ＝ f ∞.

We can implement ∀ y ≥ x. A y as ∀ x. A (max x y), so that the
continuity of f amounts to

   ∃ m. ∀ n. f (max m n) ＝ f ∞,

and its negation to

   ∀ m. ¬ ∀ n. f (max m n) ＝ f ∞.

Because we are going to prove facts about the negation of continuity,
it doesn't matter whether we define the notion with ∃ or Σ, and we
choose the latter for convenience.

\begin{code}

continuous : (ℕ∞ → ℕ) → 𝓤₀ ̇
continuous f = Σ m ꞉ ℕ , ((n : ℕ) → f (max (ι m) (ι n)) ＝ f ∞)

continuity-data = continuous

noncontinuous : (ℕ∞ → ℕ) → 𝓤₀ ̇
noncontinuous f = (m : ℕ) → ¬ ((n : ℕ) → f (max (ι m) (ι n)) ＝[ℕ] f ∞)

module _ (f : ℕ∞ → ℕ) where

 noncontinuity-is-decidable : is-decidable (noncontinuous f)
 noncontinuity-is-decidable = Lemma-3·1 (λ x y → χ＝ (f (max x y)) (f ∞))

 not-continuous-gives-noncontinuous : ¬ continuous f → noncontinuous f
 not-continuous-gives-noncontinuous ν m a =
  ν (m , (λ n → rl-implication
                 (＝-agrees-with-＝[ℕ]
                    (f (max (ι m) (ι n)))
                    (f ∞))
                 (a n)))

 noncontinuous-gives-not-continuous : noncontinuous f → ¬ continuous f
 noncontinuous-gives-not-continuous ν (m , a) =
  ν m (λ n → lr-implication
              (＝-agrees-with-＝[ℕ]
                (f (max (ι m) (ι n)))
                (f ∞))
              (a n))

 Theorem-3·2 : is-decidable (¬ continuous f)
 Theorem-3·2 = map-decidable
                noncontinuous-gives-not-continuous
                not-continuous-gives-noncontinuous
                noncontinuity-is-decidable

\end{code}

(Maybe) to be continued (see the paper for the moment).

 1. MP gives that continuity and doubly negated continuity agree.

 2. WLPO is equivalent to the existence of a noncontinuous function ℕ∞ → ℕ.

 3. ¬ WLPO is equivalent to the doubly negated continuity of all functions ℕ∞ → ℕ.

 4. If MP and ¬ WLPO then all functions ℕ∞ → ℕ are continuous.

Added 24th July 2024. Still based on the same paper. We write down the proof of (3).

\begin{code}

open import Taboos.WLPO
open import TypeTopology.CompactTypes
open import TypeTopology.GenericConvergentSequenceCompactness fe

noncontinuous-map-gives-WLPO : (f : ℕ∞ → ℕ) → ¬ continuous f → WLPO
noncontinuous-map-gives-WLPO f f-non-cts = VI
 where
  g : (u : ℕ∞)
    → Σ v₀ ꞉ ℕ∞ , (f (max u v₀) ＝ f ∞ → (v : ℕ∞) → f (max u v) ＝ f ∞)
  g u = ℕ∞-Compact∙
         (λ v → f (max u v) ＝ f ∞)
         (λ v → ℕ-is-discrete (f (max u v)) (f ∞))

  G : ℕ∞ → ℕ∞
  G u = max u (pr₁ (g u))

  G-property₀ : (u : ℕ∞) → f (G u) ＝ f ∞ → (v : ℕ∞) → f (max u v) ＝ f ∞
  G-property₀ u = pr₂ (g u)

  G-property₁ : (u : ℕ∞)
              → (Σ v ꞉ ℕ∞ , f (max u v) ≠ f ∞)
              → f (G u) ≠ f ∞
  G-property₁ u (v , d) = contrapositive
                            (λ (e : f (G u) ＝ f ∞) → G-property₀ u e v)
                            d

  I : (u : ℕ∞)
    → ¬¬ (Σ v ꞉ ℕ∞ , f (max u v) ≠ f ∞)
    → (Σ v ꞉ ℕ∞ , f (max u v) ≠ f ∞)
  I u = Σ-Compactness-gives-Markov
          ℕ∞-Compact
          (λ v → f (max u v) ≠ f ∞)
          (λ v → ¬-preserves-decidability
                  (ℕ-is-discrete (f (max u v)) (f ∞)))

  II : (u : ℕ∞)
     → ¬ (Σ v ꞉ ℕ∞ , f (max u v) ≠ f ∞)
     → (v : ℕ∞) → f (max u v) ＝ f ∞
  II u ν v = discrete-is-¬¬-separated
              ℕ-is-discrete
              (f (max u v))
              (f ∞)
              (λ (d : f (max u v) ≠ f ∞) → ν (v , d))

  III : (u : ℕ∞)
      → ¬ ((v : ℕ∞) → f (max u v) ＝ f ∞)
      → ¬¬ (Σ v ꞉ ℕ∞ , f (max u v) ≠ f ∞)
  III u = contrapositive (II u)

  G-property₂ : (u : ℕ∞)
              → ¬ ((v : ℕ∞) → f (max u v) ＝ f ∞)
              → f (G u) ≠ f ∞
  G-property₂ u a = G-property₁ u (I u (III u a))

  G-propertyₙ : (n : ℕ) → f (G (ι n)) ≠ f ∞
  G-propertyₙ n = G-property₂ (ι n) h
   where
    h : ¬ ((v : ℕ∞) → f (max (ι n) v) ＝ f ∞)
    h a = f-non-cts (n , a ∘ ι)

  G-property∞ : G ∞ ＝ ∞
  G-property∞ = max∞-property (pr₁ (g ∞))

  IV : (u : ℕ∞) → u ＝ ∞ → f (G u) ＝ f ∞
  IV u refl = ap f G-property∞

  V : (u : ℕ∞) → f (G u) ＝ f ∞ → u ＝ ∞
  V u a = not-finite-is-∞ fe h
   where
    h : (n : ℕ) → u ≠ ι n
    h n refl = G-propertyₙ n a

  VI : WLPO
  VI u = map-decidable (V u) (IV u) (ℕ-is-discrete (f (G u)) (f ∞))

\end{code}

In the following fact we can replace Σ by ∃ because WLPO is a
proposition. Hence WLPO is the propositional truncation of the type
Σ f ꞉ (ℕ∞ → ℕ) , ¬ continuous f.

\begin{code}

open import Taboos.BasicDiscontinuity fe
open import Naturals.Properties

WLPO-iff-there-is-a-noncontinous-map : WLPO ↔ (Σ f ꞉ (ℕ∞ → ℕ) , ¬ continuous f)
WLPO-iff-there-is-a-noncontinous-map =
  I ,
  (λ (f , ν) → noncontinuous-map-gives-WLPO f ν)
 where
  I : WLPO → Σ f ꞉ (ℕ∞ → ℕ) , ¬ continuous f
  I wlpo = f , f-non-cts
   where
    p : ℕ∞ → 𝟚
    p = pr₁ (WLPO-is-discontinuous wlpo)

    p-spec : ((n : ℕ) → p (ι n) ＝ ₀) × (p ∞ ＝ ₁)
    p-spec = pr₂ (WLPO-is-discontinuous wlpo)

    g : 𝟚 → ℕ
    g ₀ = 0
    g ₁ = 1

    f : ℕ∞ → ℕ
    f = g ∘ p

    f₀ : (n : ℕ) → f (ι n) ＝ 0
    f₀ n =  f (ι n) ＝⟨ ap g (pr₁ p-spec n) ⟩
            g ₀     ＝⟨ refl ⟩
            0       ∎

    f∞ : (n : ℕ) → f (ι n) ≠ f ∞
    f∞ n e = zero-not-positive 0
              (0       ＝⟨ f₀ n ⁻¹ ⟩
               f (ι n) ＝⟨ e ⟩
               f ∞     ＝⟨ ap g (pr₂ p-spec) ⟩
               1       ∎)

    f-non-cts : ¬ continuous f
    f-non-cts (m , a) = f∞ m
                         (f (ι m)             ＝⟨ ap f ((max-idemp fe (ι m))⁻¹) ⟩
                          f (max (ι m) (ι m)) ＝⟨ a m ⟩
                          f ∞                 ∎)

¬WLPO-iff-all-maps-are-¬¬-continuous : ¬ WLPO ↔ ((f : ℕ∞ → ℕ) → ¬¬ continuous f)
¬WLPO-iff-all-maps-are-¬¬-continuous =
 (λ nwlpo f f-non-cts
   → contrapositive
      (rl-implication WLPO-iff-there-is-a-noncontinous-map)
      nwlpo
      (f , f-non-cts)) ,
 (λ (a : (f : ℕ∞ → ℕ) → ¬¬ continuous f)
   → contrapositive
      (lr-implication WLPO-iff-there-is-a-noncontinous-map)
      (λ (f , f-non-cts) → a f f-non-cts))

\end{code}

Hence ¬ WLPO can be considered as a (rather weak) continuity principle.

It is shown in [1] that negative consistent axioms can be postulated
in MLTT without loss of canonicity, and Andreas Abel filled important
gaps and formalized this in Agda [2] using a logical-relations
technique. Hence we can, if we wish, postulate ¬ WLPO without loss of
canonicity, and get a weak continuity axiom for free.

[1] T. Coquand, N.A. Danielsson, M.H. Escardo, U. Norell and Chuangjie Xu.
Negative consistent axioms can be postulated without loss of canonicity.
https://www.cs.bham.ac.uk/~mhe/papers/negative-axioms.pdf

[2] Andreas Abel. Negative Axioms.
https://github.com/andreasabel/logrel-mltt/tree/master/Application/NegativeAxioms

--

Added 16 August 2024.

The above definition of continuity is "continuity at the point ∞".
(And it is also not a proposition.)

Next I am going to show that this is equivalent to usual continuity,
as in the module Cantor, using the fact that ℕ∞ is a subspace of the
Cantor type ℕ → 𝟚

Moreover, in the particular case of the subspace ℕ∞ of the Cantor
space, continuity of functions ℕ∞ → D, with D discrete, is equivalent
to uniform continuity, constructively, without the need of Brouwerian
axioms.

So I will do next is to show that all imaginable notions of (uniform)
continuity for functions ℕ∞ → D are equivalent, constructively.

Moreover, I will compare typal versus propositional definitions of
(uniform) continuity.

This could be classified as a TODO, but rather it is something I am
doing.

One reason I want to do this is work by other people on realizability
models and light condensed sets models in HoTT/UF.

Added 20th August. Continuity as property gives continuity data.

\begin{code}

open import Naturals.RootsTruncation
open import UF.PropTrunc
open import UF.Subsingletons
open import UF.Subsingletons-FunExt

module continuity-criteria (pt : propositional-truncations-exist) where

 open PropositionalTruncation pt
 open exit-truncations pt

 is-continuous : (ℕ∞ → ℕ) → 𝓤₀ ̇
 is-continuous f = ∃ m ꞉ ℕ , ((n : ℕ) → f (max (ι m) (ι n)) ＝ f ∞)

 module _ (f : ℕ∞ → ℕ) where

  private
   A : ℕ∞ → 𝓤₀ ̇
   A x = (n : ℕ) → f (max x (ι n)) ＝ f ∞

   A-is-prop-valued : (x : ℕ∞) → is-prop (A x)
   A-is-prop-valued x = Π-is-prop fe (λ n → ℕ-is-set)

   A-is-complemented : (x : ℕ∞) → is-decidable (A x)
   A-is-complemented x = γ
    where
     B : 𝓤₀ ̇
     B = (n : ℕ) → f (max x (ι n)) ＝[ℕ] f ∞

     B-is-decidable : is-decidable B
     B-is-decidable = Theorem-8·2 (λ y → χ＝ (f (max x y)) (f ∞))

     γ : is-decidable (A x)
     γ = map-decidable
          (λ b n → rl-implication (＝-agrees-with-＝[ℕ] _ _) (b n))
          (λ a n → lr-implication (＝-agrees-with-＝[ℕ] _ _) (a n))
          B-is-decidable

  continuity-data-gives-continuity-property : continuity-data f → is-continuous f
  continuity-data-gives-continuity-property = ∣_∣

  continuity-property-gives-continuity-data : is-continuous f → continuity-data f
  continuity-property-gives-continuity-data =
   exit-truncation
    (λ m → (n : ℕ) → f (max (ι m) (ι n)) ＝ f ∞)
    (λ m → A-is-complemented (ι m))

\end{code}
