Martin Escardo, 13th June 2025

We repackage the definitions of algebraic injective and flabby
structure in a more convenient way for some purposes.

\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import MLTT.Spartan

module InjectiveTypes.Repackaging
        {𝓦 : Universe}
        (D : 𝓦 ̇ )
       where

open import UF.Embeddings
open import UF.SubtypeClassifier

flabby-structure : (𝓤 : Universe) → 𝓤 ⁺ ⊔ 𝓦 ̇
flabby-structure 𝓤
 = Σ ⨆ ꞉ ((P : Ω 𝓤) → (P holds → D) → D)
       , ((P : Ω 𝓤) (f : P holds → D) (p : P holds) → ⨆ P f ＝ f p)

injective-structure : (𝓤 𝓥 : Universe) → 𝓤 ⁺ ⊔ 𝓥 ⁺ ⊔ 𝓦 ̇
injective-structure 𝓤 𝓥
 = Σ _∣_ ꞉ ({X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → D) → (X ↪ Y) → (Y → D))
         , ({X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → D) (𝕛 : X ↪ Y) → (f ∣ 𝕛) ∘ ⌊ 𝕛 ⌋ ∼ f)

flabby-structure-gives-injective-structure
 : flabby-structure (𝓤 ⊔ 𝓥) → injective-structure 𝓤 𝓥
flabby-structure-gives-injective-structure {𝓤} {𝓥} (⨆ , e)
 = _∣_ , e'
 where
  _∣_ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → D) → (X ↪ Y) → (Y → D)
  (f ∣ 𝕛) y = ⨆ ((Fiber 𝕛 y)) (f ∘ pr₁)

  e' : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → D) (𝕛 : X ↪ Y) → (f ∣ 𝕛) ∘ ⌊ 𝕛 ⌋ ∼ f
  e' f 𝕛 x = e (Fiber 𝕛 (⌊ 𝕛 ⌋ x)) (f ∘ pr₁) (x , refl)

injective-structure-gives-flabby-structure
 : injective-structure 𝓤 𝓥 → flabby-structure 𝓤
injective-structure-gives-flabby-structure {𝓤} {𝓥} (_∣_ , e) = ⨆ , e'
 where
  ⨆ : (P : Ω 𝓤) → (P holds → D) → D
  ⨆ P f = (f ∣ embedding-to-𝟙) ⋆

  e' : (P : Ω 𝓤) (f : P holds → D) (p : P holds) → ⨆ P f ＝ f p
  e' P f = e f embedding-to-𝟙

\end{code}

We had already given (in InjectiveTypes.BlackBoard) conversions
between ainjective types and a flabby types. We now record that the
ones we gave here agree definitionally with those there, via the
"repackaging" equivalences gives below.

Unfortunately, InjectiveTypes has a global assumption of function
extensionality, which is not used for the definitions of algebraic
injective and flabby structure. Fortunately, we don't need to use the
proofs below (particularly because they are proved with refl), which
are here only for the purpose of emphasizing that we are working with
the same definitions repackaged in a different way.

\begin{code}

open import UF.FunExt
open import UF.Equiv

module _ (fe : FunExt) where

 open import InjectiveTypes.Blackboard fe

 ainjective-type-repackaging : injective-structure 𝓤 𝓥 ≃ ainjective-type D 𝓤 𝓥
 ainjective-type-repackaging =
  qinveq
   (λ (_∣_ , e) → λ {X} {Y} j i f → (f ∣ (j , i)) , e f (j , i))
   ((λ ainj →
       (λ {X} {Y} f 𝕛 → pr₁ (ainj ⌊ 𝕛 ⌋ ⌊ 𝕛 ⌋-is-embedding f)) ,
       (λ {X} {Y} f 𝕛 → pr₂ (ainj ⌊ 𝕛 ⌋ ⌊ 𝕛 ⌋-is-embedding f))) ,
    (λ _ → refl) ,
    (λ _ → refl))

 aflabby-repackaging : flabby-structure 𝓤 ≃ aflabby D 𝓤
 aflabby-repackaging
  = qinveq
     (λ (⨆ , e) P i f → ⨆ (P , i) f , e (P , i) f)
     ((λ aflab →
        (λ P f → pr₁ (aflab (P holds) (holds-is-prop P) f)) ,
        (λ P f → pr₂ (aflab (P holds) (holds-is-prop P) f))) ,
      (λ _ → refl) ,
      (λ _ → refl))

\end{code}

TODO. Write the commutative squares corresponding to the following two
proofs as a comment.

\begin{code}

 injective-structure-gives-flabby-structure-agreement
  : (s : injective-structure 𝓤 𝓥)
  → ⌜ aflabby-repackaging ⌝
      (injective-structure-gives-flabby-structure s)
  ＝ ainjective-types-are-aflabby D
      (⌜ ainjective-type-repackaging ⌝ s)
 injective-structure-gives-flabby-structure-agreement s = refl

 \end{code}

 For the second one we need to do a manual eta expasion to deal with
 the way Agda works with implicit arguments, which gives unsolved
 constraints otherwise (this is a well known design issue).

 \begin{code}

 flabby-structure-gives-injective-structure-agreement
  : (s : flabby-structure 𝓤)
  → (λ {X Y : 𝓤 ̇} (j : X → Y)
     → ⌜ ainjective-type-repackaging ⌝
         (flabby-structure-gives-injective-structure s) {X} {Y} j)
  ＝ aflabby-types-are-ainjective D
      (⌜ aflabby-repackaging ⌝ s)
 flabby-structure-gives-injective-structure-agreement s = refl

\end{code}

We can change variables in ⨆ in the following sense. Notice that there
is a similar fact proved with the stronger assumption of univalence in
the development of the lifting monad.

\begin{code}

open import UF.Subsingletons

⨆-change-of-variable : propext 𝓤
                     → funext 𝓤 𝓤
                     → (⨆ : (P : Ω 𝓤) → (P holds → D) → D)
                     → (P Q : Ω 𝓤)
                       (f : P holds → D)
                       ((g , h) : (P holds) ↔ Q holds)
                     → ⨆ P f ＝ ⨆ Q (f ∘ h)
⨆-change-of-variable pe fe ⨆ P Q f (g , h) = IV
 where
  h' : (e : P ＝ Q) → Q holds → P holds
  h' e = ⌜ idtoeq _ _ (ap _holds e) ⌝⁻¹

  I : (e : P ＝ Q) → h' e ＝ h
  I e = dfunext fe (λ p → holds-is-prop P (h' e p) (h p))

  II : (e : P ＝ Q) → ⨆ P f ＝ ⨆ Q (f ∘ h' e)
  II refl = refl

  e : P ＝ Q
  e = Ω-extensionality pe fe g h

  III : ⨆ P f ＝ ⨆ Q (f ∘ h' e)
  III = II e

  IV : ⨆ P f ＝ ⨆ Q (f ∘ h)
  IV = transport (λ - → ⨆ P f ＝ ⨆ Q (f ∘ -)) (I e) III

\end{code}
