Ian Ray, 17th July 2025.

We formalize the join construction found in Section 3 of The Join Construction
by Egbert Rijke (https://arxiv.org/abs/1701.07538.).

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module UF.JoinConstruction (fe : Fun-Ext) where

open import MLTT.Spartan
open import UF.Pullback
open import UF.Pushouts fe
open import UF.JoinofMaps fe
open import UF.SequentialColimits fe

\end{code}

Given a map f : A → X we define sequences in terms of iterative joins (of types
and maps) which will serve as approximations of the image and image inclusion
respectivly. See the following diagram. 

                 i₀              i₁
      im⁰_* (f) ----> im¹_* (f) ----> im²_* (f) ---> ...
           \             |             /
            \            |            /
             \           |           /
              \          |          /
               \         |         /
           f⁰_* \   f¹_* |   f²_* /   ...
                 \       |       /
                  \      |      /
                   \     |     /
                    \    |    /
                     \   |   /
                      V  V  V
                         X

Where we take im⁰_* (f) := 𝟘 and f⁰_* to be the unique map from 𝟘. Further we
take imⁿ⁺¹_* (f) := A *_X imⁿ_* (f) and fⁿ⁺¹_* := f * fⁿ_*.

\begin{code}

module _ {A : 𝓤 ̇} {X : 𝓥 ̇}
         (f : A → X)
         (Push-Ex : pushouts-exist)
       where

 open pushouts-exist Push-Ex

 im-approx : (n : ℕ) → 𝓤 ⊔ 𝓥 ̇
 join-power : (n : ℕ) → (im-approx n → X)
 im-approx zero = 𝟘
 im-approx (succ n) = join-of-types f (join-power n) Push-Ex
 join-power zero = unique-from-𝟘
 join-power (succ n) = join-of-maps f (join-power n) Push-Ex

\end{code}

We can get a map from A to any approximation with n ≥ 1 but it suffices
to provide a map into the first approximation.

\begin{code}

 im-approx-restriction : A → im-approx (succ zero)
 im-approx-restriction = inll
  where
   open pullback f (join-power zero)
   open pushout-exists (push-ex pb₁ pb₂)

\end{code}

We show that the image approximation forms a type sequence and show that
together with X we have a sequential cocone.

\begin{code}

 im-approx-step : (n : ℕ) → im-approx n → im-approx (succ n)
 im-approx-step zero = unique-from-𝟘
 im-approx-step (succ n) x = inrr x
  where
   open pullback f (join-power (succ n))
   open pushout-exists (push-ex pb₁ pb₂)
    
 im-approx-is-type-seq : type-sequence (𝓤 ⊔ 𝓥)
 im-approx-is-type-seq = (im-approx , im-approx-step)

 join-power-commutes-with-step
  : (n : ℕ)
  → join-power n ∼ join-power (succ n) ∘ im-approx-step n
 join-power-commutes-with-step zero = 𝟘-induction
 join-power-commutes-with-step (succ n)
  = ∼-sym (join-of-maps-inrr f (join-power (succ n)) Push-Ex)
  
 im-approx-is-seq-cocone : sequential-cocone im-approx-is-type-seq X
 im-approx-is-seq-cocone = (join-power , join-power-commutes-with-step)

\end{code}

We will define the image to be the sequential colimit of the sequence of image
approximations.

\begin{code}

 image* : 𝓤 ⊔ 𝓥  ̇
 image* = sequential-colimit im-approx-is-type-seq
           (push-ex (id-case im-approx-is-type-seq)
            (succ-case im-approx-is-type-seq))
  where
   open pushout-exists (push-ex (id-case im-approx-is-type-seq)
                        (succ-case im-approx-is-type-seq))

 image*-embedding : image* → X
 image*-embedding = sequential-colimit-recursion im-approx-is-type-seq
                     (push-ex (id-case im-approx-is-type-seq)
                      (succ-case im-approx-is-type-seq))
                     X im-approx-is-seq-cocone
  where
   open pushout-exists (push-ex (id-case im-approx-is-type-seq)
                        (succ-case im-approx-is-type-seq))

 image*-inclusion : (n : ℕ)
                  → im-approx n → image*
 image*-inclusion
  = ι im-approx-is-type-seq
      (push-ex (id-case im-approx-is-type-seq)
       (succ-case im-approx-is-type-seq))
  where
   open pushout-exists (push-ex (id-case im-approx-is-type-seq)
                        (succ-case im-approx-is-type-seq))

 image*-restriction : A → image*
 image*-restriction = image*-inclusion (succ zero) ∘ im-approx-restriction

\end{code}

 image*-factorization : f ∼ image*-embedding ∘ image*-restriction
 image*-factorization = {!!}

\end{code}

We need to show that this is an image (i.e. satisfies some sort of universal
property or induction).
