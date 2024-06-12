Martin Escardo, 24th March 2022

This file is a apropos the discussion at the end of the file
Ordinals.NotationInterpretation2.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.FunExt

module Taboos.P2 (fe : FunExt) where

fe₀ : {𝓤 : Universe} → DN-funext 𝓤 𝓤₀
fe₀ {𝓤} = dfunext (fe 𝓤 𝓤₀)

open import MLTT.Two
open import MLTT.Two-Properties

open import UF.Base
open import UF.DiscreteAndSeparated
open import UF.Equiv
open import UF.Equiv-FunExt
open import UF.ClassicalLogic
open import UF.Retracts
open import UF.Subsingletons
open import UF.Subsingletons-FunExt

κ : (P : 𝓤 ̇ ) → 𝟚 → (P → 𝟚)
κ P n = λ _ → n

κ-remark : (P : 𝓤 ̇ ) → (κ P ₀ ＝ κ P ₁) ↔ ¬ P
κ-remark {𝓤} P = (f , g)
 where
  κ₀ = κ P ₀
  κ₁ = κ P ₁

  f : κ₀ ＝ κ₁ → ¬ P
  f e p = zero-is-not-one
           (₀    ＝⟨ refl ⟩
            κ₀ p ＝⟨ happly e p ⟩
            κ₁ p ＝⟨ refl ⟩
            ₁    ∎)

  g : ¬ P → κ₀ ＝ κ₁
  g ν = dfunext (fe 𝓤 𝓤₀) (λ (p : P) → 𝟘-elim (ν p))

κ-remark' : (P : 𝓤 ̇ ) → (κ P ₀ ≠ κ P ₁) ↔ ¬¬ P
κ-remark' {𝓤} P = I (κ-remark P)
 where
  κ₀ = κ P ₀
  κ₁ = κ P ₁

  I : type-of (κ-remark P) → (κ₀ ≠ κ₁) ↔ ¬¬ P
  I (f , g) = contrapositive g ,
              (λ (ν : ¬¬ P) (e : κ₀ ＝ κ₁) → ν (f e))

\end{code}

The following makes sense when P is a proposition. (Then we could say
that a type X is pseudo-inhabited if the proposition ∥ X ∥ is
pseudo-inhabited.)

\begin{code}

is-pseudo-inhabited : 𝓤 ̇ → 𝓤 ̇
is-pseudo-inhabited P = is-equiv (κ P)

is-pseudo-inhabited' : 𝓤 ̇ → 𝓤 ̇
is-pseudo-inhabited' P = is-section (κ P)

retraction-of-κ-is-section : {P : 𝓤 ̇ }
                           → is-prop P
                           → (r : (P → 𝟚) → 𝟚)
                           → r ∘ κ P ∼ id
                           → κ P ∘ r ∼ id
retraction-of-κ-is-section {𝓤} {P} i r h f = IV
 where
  I : (p : P) → r f ＝ f p
  I p = r f           ＝⟨ ap r III ⟩
        r (κ P (f p)) ＝⟨ h (f p) ⟩
        f p           ∎
   where
    II : f ∼ κ P (f p)
    II q = f q         ＝⟨ ap f (i q p) ⟩
           f p         ＝⟨ refl ⟩
           κ P (f p) q ∎

    III : f ＝ κ P (f p)
    III = fe₀ II

  IV : κ P (r f) ＝ f
  IV = fe₀ I

\end{code}

TODO. In light of the above, is-pseudo-inhabited' X should be a
proposition.

\begin{code}

pseudo-inhabitedness-criterion : {P : 𝓤 ̇ }
                               → is-prop P
                               → is-pseudo-inhabited' P
                               → is-pseudo-inhabited  P
pseudo-inhabitedness-criterion {𝓤} {P} i (r , rκ) =
 qinvs-are-equivs (κ P) (r , rκ , retraction-of-κ-is-section i r rκ)

pseudo-inhabitedness-criterion-necessity : {P : 𝓤 ̇ }
                                         → is-pseudo-inhabited P
                                         → is-pseudo-inhabited' P
pseudo-inhabitedness-criterion-necessity {𝓤} {P} = equivs-are-sections (κ P)

inhabited-gives-pseudo-inhabited : {P : 𝓤 ̇ }
                                 → is-prop P
                                 → P
                                 → is-pseudo-inhabited P
inhabited-gives-pseudo-inhabited {𝓤} {P} i p =
  pseudo-inhabitedness-criterion i (γ , γκ)
 where
  γ : (P → 𝟚) → 𝟚
  γ f = f p

  γκ : γ ∘ κ P ∼ id
  γκ n = refl

\end{code}

We will later see that the following implication can't be reversed
unless weak excluded middle holds:

\begin{code}

pseudo-inhabited-gives-irrefutable : {P : 𝓤 ̇ }
                                   → is-pseudo-inhabited P
                                   → ¬¬ P
pseudo-inhabited-gives-irrefutable {𝓤} {P} e n = zero-is-not-one II
 where
  I : inverse (κ P) e (κ P ₀) ＝ inverse (κ P) e (κ P ₁)
  I = ap (inverse (κ P) e) (κ P ₀ ＝⟨ fe₀ (λ p → 𝟘-elim (n p)) ⟩
                            κ P ₁ ∎)

  II = ₀                       ＝⟨ (inverses-are-retractions (κ P) e ₀)⁻¹ ⟩
       inverse (κ P) e (κ P ₀) ＝⟨ I ⟩
       inverse (κ P) e (κ P ₁) ＝⟨ inverses-are-retractions (κ P) e ₁ ⟩
       ₁                       ∎

pseudo-inhabited-gives-irrefutable-special : {P : 𝓤 ̇ }
                                           → is-pseudo-inhabited (¬ P)
                                           → ¬ P
pseudo-inhabited-gives-irrefutable-special h =
 three-negations-imply-one (pseudo-inhabited-gives-irrefutable h)

pseudo-inhabited-gives-irrefutable-special' : {P : 𝓤 ̇ }
                                            → is-pseudo-inhabited (¬¬ P)
                                            → ¬¬ P
pseudo-inhabited-gives-irrefutable-special' =
 pseudo-inhabited-gives-irrefutable-special

P→𝟚-discreteness-criterion : {P : 𝓤 ̇ }
                           → ¬ P + is-pseudo-inhabited P
                           → is-discrete (P → 𝟚)
P→𝟚-discreteness-criterion (inl n) f g = inl (dfunext (fe _ 𝓤₀)
                                               (λ p → 𝟘-elim (n p)))
P→𝟚-discreteness-criterion (inr s) f g = retract-is-discrete
                                          (≃-gives-▷ (κ _ , s))
                                          𝟚-is-discrete
                                          f g

P→𝟚-discreteness-criterion-necessity : {P : 𝓤 ̇ }
                                     → is-prop P
                                     → is-discrete (P → 𝟚)
                                     → ¬ P + is-pseudo-inhabited P
P→𝟚-discreteness-criterion-necessity {𝓤} {P} i δ = ϕ (δ (κ P ₀) (κ P ₁))
 where
  ϕ : is-decidable (κ P ₀ ＝ κ P ₁) → ¬ P + is-pseudo-inhabited P
  ϕ (inl e) = inl (fact e)
   where
    fact : κ P ₀ ＝ κ P ₁ → ¬ P
    fact e p = zero-is-not-one (ap (λ f → f p) e)
  ϕ (inr n) = inr (pseudo-inhabitedness-criterion i (γ , γκ))
   where
    h : (f : P → 𝟚) → is-decidable (f ＝ κ P ₀) → 𝟚
    h f (inl _) = ₀
    h f (inr _) = ₁

    γ : (P → 𝟚) → 𝟚
    γ f = h f (δ f (κ P ₀))

    h₀ : (d : is-decidable (κ P ₀ ＝ κ P ₀)) → h (κ P ₀) d ＝ ₀
    h₀ (inl _) = refl
    h₀ (inr d) = 𝟘-elim (d refl)

    h₁ : (d : is-decidable (κ P ₁ ＝ κ P ₀)) → h (κ P ₁) d ＝ ₁
    h₁ (inl e) = 𝟘-elim (n (e ⁻¹))
    h₁ (inr _) = refl

    γκ : γ ∘ κ P ∼ id
    γκ ₀ = h₀ (δ (κ P ₀) (κ P ₀))
    γκ ₁ = h₁ (δ (κ P ₁) (κ P ₀))

\end{code}

Added 25th March 2022. If every irrefutable proposition is
pseudo-inhabited, then weak excluded middle holds.

TODO. We should actually have the stronger implication
is-pseudo-inhabited (Q + ¬ Q) → ¬ Q + ¬¬ Q with a similar proof.

\begin{code}

pseudo-inhabitedness-wem-lemma : (Q : 𝓤 ̇)
                               → is-pseudo-inhabited (Q + ¬ Q)
                               → ¬ Q + ¬¬ Q
pseudo-inhabitedness-wem-lemma Q h = b
 where
  P = Q + ¬ Q

  f : P → 𝟚
  f (inl _) = ₀
  f (inr _) = ₁

  n : 𝟚
  n = inverse (κ P) h f

  a : (k : 𝟚) → n ＝ k → ¬ Q + ¬¬ Q
  a ₀ e = inr ϕ
   where
    I = f         ＝⟨ (inverses-are-sections (κ P) h f)⁻¹ ⟩
        κ P n     ＝⟨ ap (κ P) e ⟩
        (λ _ → ₀) ∎

    ϕ : ¬¬ Q
    ϕ u = zero-is-not-one
           (₀         ＝⟨ (ap (λ - → - (inr u)) I)⁻¹ ⟩
            f (inr u) ＝⟨ refl ⟩
            ₁         ∎)

  a ₁ e = inl u
   where
    I = f         ＝⟨ (inverses-are-sections (κ P) h f)⁻¹ ⟩
        κ P n     ＝⟨ ap (κ P) e ⟩
        (λ _ → ₁) ∎

    u : ¬ Q
    u q = zero-is-not-one
           (₀         ＝⟨ refl ⟩
            f (inl q) ＝⟨ ap (λ - → - (inl q)) I ⟩
            ₁         ∎)

  b : ¬ Q + ¬¬ Q
  b = a n refl

irrefutable-pseudo-inhabited-taboo
 : ((P : 𝓤 ̇ ) → is-prop P → ¬¬ P → is-pseudo-inhabited P) → WEM 𝓤
irrefutable-pseudo-inhabited-taboo {𝓤} α Q i =
  pseudo-inhabitedness-wem-lemma Q h
 where
  P = Q + ¬ Q

  ν : ¬¬ P
  ν ϕ = ϕ (inr (λ q → ϕ (inl q)))

  h : is-pseudo-inhabited P
  h = α P (decidability-of-prop-is-prop (fe 𝓤 𝓤₀) i) ν

\end{code}

Nathanael Rosnik proved the above taboo independently within a few
hours of difference here:
https://gist.github.com/nrosnick/922250ddcc6bd04272199f59443d7510

A special case of the lemma:

\begin{code}

pseudo-inhabitedness-wem-special : (Q : 𝓤 ̇)
                                 → is-pseudo-inhabited (¬ Q + ¬¬ Q)
                                 → ¬ Q + ¬¬ Q
pseudo-inhabitedness-wem-special Q h =
 Cases (pseudo-inhabitedness-wem-lemma (¬ Q) h)
  inr
  (inl ∘ three-negations-imply-one)

\end{code}


TODO. Derive a constructive taboo from the hypothesis

      (P : 𝓤 ̇ ) → is-prop P → is-pseudo-inhabited P → P.

A monad on propositions (or even on all types?).

\begin{code}

η : {X : 𝓤 ̇ } → X → is-pseudo-inhabited' X
η x = (λ f → f x) , (λ n → refl)

_♯ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
   → (X → is-pseudo-inhabited' Y)
   → (is-pseudo-inhabited' X → is-pseudo-inhabited' Y)
_♯ {𝓤} {𝓥} {X} {Y} h (r , rκ) = q
 where
  a : X → (Y → 𝟚) → 𝟚
  a x = pr₁ (h x)

  b : (x : X) (n : 𝟚) → a x (κ Y n) ＝ n
  b x = pr₂ (h x)

  u : (Y → 𝟚) → 𝟚
  u g = r (λ x → a x g)

  v : u ∘ κ Y ∼ id
  v n = (u ∘ κ Y) n           ＝⟨ refl ⟩
        r (λ x → a x (κ Y n)) ＝⟨ ap r (fe₀ (λ x → b x n)) ⟩
        r (λ _ → n)           ＝⟨ refl ⟩
        r (κ X n)             ＝⟨ rκ n ⟩
        n                     ∎

  q : is-pseudo-inhabited' Y
  q = u , v

functor : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
        → (X → Y)
        → (is-pseudo-inhabited' X → is-pseudo-inhabited' Y)
functor f = (η ∘ f) ♯

μ : (X : 𝓤 ̇ )
  → is-pseudo-inhabited' (is-pseudo-inhabited' X)
  → is-pseudo-inhabited' X
μ X = id ♯

being-pseudo-inhabited'-is-prop : {X : 𝓤 ̇ }
                                → is-prop X
                                → is-prop (is-pseudo-inhabited' X)
being-pseudo-inhabited'-is-prop {𝓤} {X} i =
 prop-criterion
  (λ (r , rκ) → sections-have-at-most-one-retraction fe (κ X)
                 (r , retraction-of-κ-is-section i r rκ))

\end{code}
