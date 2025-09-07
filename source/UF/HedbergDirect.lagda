Ian Ray 4th September 2025

\begin{code}

{-# OPTIONS --safe --without-K #-}

module UF.HedbergDirect where

open import MLTT.Spartan
open import UF.Base

\end{code}

We convert a direct proof of hedberg's lemma, by Carlo Angiuli, which heavily
relies on 'with abstraction' to a proof that only uses 'where'.

(This direct proof is due to Nicolai Kraus see:
https://homotopytypetheory.org/2012/03/30/a-direct-proof-of-hedbergs-theorem/)

\begin{code}

Lemma-Motive : {X : 𝓤 ̇}
             → ((x y : X) → is-decidable (x ＝ y))
             → (a b : X)
             → (a ＝ b)
             → 𝓤 ̇
Lemma-Motive {𝓤} {X} dec a b p = I (dec a a) (dec a b)
 module Lemma-Motive-helper where
  I : is-decidable (a ＝ a) → is-decidable (a ＝ b) → 𝓤 ̇
  I (inl r) (inl q) = p ＝ r ⁻¹ ∙ q
  I (inl _) (inr np) = 𝟘-elim (np p)
  I (inr nr) _ = 𝟘-elim (nr refl)

Lemma : {X : 𝓤 ̇}
      → (dec : (x y : X) → is-decidable (x ＝ y))
      → (a b : X) (p : a ＝ b)
      → Lemma-Motive dec a b p
Lemma {_} {X} dec a a refl = I (dec a a)
 module Lemma-helper where
  I : (d : is-decidable (a ＝ a)) → Lemma-Motive-helper.I dec a a refl d d
  I (inl r) = sym-is-inverse r
  I (inr nr) = 𝟘-elim (nr refl)

hedberg-direct : {X : 𝓤 ̇}
               → (dec : (x y : X) → is-decidable (x ＝ y))
               → (a b : X)
               → (p q : a ＝ b)
               → p ＝ q
hedberg-direct dec a b p q
 = I (dec a a) (dec a b) (Lemma dec a b p) (Lemma dec a b q)
 where
  I : (r : is-decidable (a ＝ a))
    → (s : is-decidable (a ＝ b))
    → Lemma-Motive-helper.I dec a b p r s
    → Lemma-Motive-helper.I dec a b q r s
    → p ＝ q
  I (inl r) (inl s) α β = α ∙ β ⁻¹
  I (inl r) (inr ns) α β = 𝟘-elim (ns p)
  I (inr nr) _ α β = 𝟘-elim (nr refl)
  

\end{code}

Or we could give all top level definitions
(for whatever reason (;)

\begin{code}

Lemma-Motive-helper' : {X : 𝓤 ̇}
                     → (a b : X)
                     → (a ＝ b)
                     → is-decidable (a ＝ a)
                     → is-decidable (a ＝ b)
                     → 𝓤 ̇
Lemma-Motive-helper' a b p (inl r) (inl s) = p ＝ r ⁻¹ ∙ s
Lemma-Motive-helper' a b p (inl _) (inr ns) = 𝟘-elim (ns p)
Lemma-Motive-helper' a b p (inr nr) _ = 𝟘-elim (nr refl)

Lemma-Motive' : {X : 𝓤 ̇}
              → ((x y : X) → is-decidable (x ＝ y))
              → (a b : X)
              → (a ＝ b)
              → 𝓤 ̇
Lemma-Motive' dec a b p = Lemma-Motive-helper' a b p (dec a a) (dec a b)

Lemma-helper' : {X : 𝓤 ̇}
              → (a : X)
              → (d : is-decidable (a ＝ a))
              → Lemma-Motive-helper' a a refl d d
Lemma-helper' a (inl r) = sym-is-inverse r
Lemma-helper' a (inr nr) = 𝟘-elim (nr refl)

Lemma' : {X : 𝓤 ̇}
       → (dec : (x y : X) → is-decidable (x ＝ y))
       → (a b : X) (p : a ＝ b)
       → Lemma-Motive' dec a b p
Lemma' dec a a refl = Lemma-helper' a (dec a a)

hedberg-helper' : {X : 𝓤 ̇}
                → (a b : X)
                → (p q : a ＝ b)
                → (r : is-decidable (a ＝ a))
                → (s : is-decidable (a ＝ b))
                → Lemma-Motive-helper' a b p r s
                → Lemma-Motive-helper' a b q r s
                → p ＝ q
hedberg-helper' a b p q (inl r) (inl s) α β = α ∙ β ⁻¹
hedberg-helper' a b p q (inl r) (inr ns) α β = 𝟘-elim (ns p)
hedberg-helper' a b p q (inr nr) _ α β = 𝟘-elim (nr refl)

hedberg-direct' : {X : 𝓤 ̇}
                → (dec : (x y : X) → is-decidable (x ＝ y))
                → (a b : X)
                → (p q : a ＝ b)
                → p ＝ q
hedberg-direct' dec a b p q
 = hedberg-helper' a b p q (dec a a) (dec a b)
    (Lemma' dec a b p) (Lemma' dec a b q)

\end{code}
