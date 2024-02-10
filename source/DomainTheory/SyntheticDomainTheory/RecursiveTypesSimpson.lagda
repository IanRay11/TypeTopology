Ian Ray, 02/02/2024

We set out to formalize parts of 'Computational adequacy for recursive types
in models of intuitionistic set theory'. Our goal is internalize much of the
first 9 sections in HoTT (+ additional axioms as neccesary).

\begin{code}

{-# OPTIONS --safe --without-K --exact-split #-}

open import MLTT.Spartan
open import MLTT.Two-Properties
open import Slice.Family
open import UF.Embeddings
open import UF.Equiv
open import UF.FunExt
open import UF.Logic
open import UF.Retracts
open import UF.PropTrunc
open import UF.SIP
open import UF.SIP-Examples
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.SubtypeClassifier
open import UF.Size
open import UF.Subsingletons-FunExt
open import UF.Sets

module DomainTheory.SyntheticDomainTheory.RecursiveTypesSimpson
       (pt : propositional-truncations-exist)
       (fe : Fun-Ext)
        where

open import UF.ImageAndSurjection pt
open PropositionalTruncation pt

\end{code}

open AllCombinators pt fe

A dominance is ...

\begin{code}

module dominance-def (𝓣 𝓦 : Universe) where

 D₁ : (𝓣  ̇ → 𝓦  ̇) → (𝓣 ⁺) ⊔ 𝓦  ̇
 D₁ d = (X : 𝓣 ̇) → is-prop (d X)

 D₂ : (𝓣  ̇ → 𝓦  ̇) → (𝓣 ⁺) ⊔ 𝓦  ̇ 
 D₂ d = (X : 𝓣 ̇) → d X → is-prop X

 D₃ : (𝓣  ̇ → 𝓦  ̇) → 𝓦  ̇
 D₃ d = d 𝟙

 D₄ : (𝓣  ̇ → 𝓦  ̇) → (𝓣 ⁺) ⊔ 𝓦  ̇
 D₄ d = (P : 𝓣  ̇)
      → (Q : P → 𝓣  ̇)
      → d P
      → ((p : P) → d (Q p))
      → d (Σ p ꞉ P , Q(p))

 is-dominance : (𝓣  ̇ → 𝓦  ̇) → (𝓣 ⁺) ⊔ 𝓦  ̇
 is-dominance d = D₁ d × D₂ d × D₃ d × D₄ d

 Dominance : (𝓣 ⁺) ⊔ (𝓦 ⁺)  ̇
 Dominance = Σ d ꞉ (𝓣  ̇ → 𝓦  ̇) , is-dominance d

\end{code}

We will now name the projections for ease of use.

\begin{code}

 is-dominant : Dominance → (𝓣  ̇ → 𝓦  ̇)
 is-dominant (d , _) = d

 being-dominant-is-prop : (D : Dominance)
                        → (X : 𝓣  ̇) → is-prop (is-dominant D X)
 being-dominant-is-prop (_ , (dip , _)) = dip

 dominant-types-are-props : (D : Dominance)
                          → (X : 𝓣  ̇) → is-dominant D X → is-prop X
 dominant-types-are-props (_ , (_ , (dtp , _))) = dtp

 Dominant-Propositions : Dominance → (𝓣 ⁺) ⊔ 𝓦  ̇
 Dominant-Propositions D = Σ P ꞉ Ω 𝓣 , is-dominant D (P holds)

 _dom-holds : {D : Dominance} → Dominant-Propositions D → 𝓣  ̇
 P dom-holds = pr₁ (pr₁ P)

 𝟙-is-dominant : (D : Dominance) → is-dominant D 𝟙
 𝟙-is-dominant (_ , (_ , (_ , (oid , _)))) = oid

 dominant-closed-under-sigma : (D : Dominance) → (P : 𝓣 ̇ ) (Q : P → 𝓣 ̇ )
                             → is-dominant D P
                             → ((p : P)
                             → is-dominant D (Q p))
                             → is-dominant D (Σ p ꞉ P , Q p)
 dominant-closed-under-sigma (_ , (_ , (_ , (_ , cus)))) = cus

 being-dominance-is-prop : (d : 𝓣  ̇ → 𝓦  ̇ )
                         → is-prop (is-dominance d)
 being-dominance-is-prop d = prop-criterion lemma
  where
   lemma : is-dominance d → is-prop (is-dominance d)
   lemma i = Σ-is-prop
               (Π-is-prop fe (λ _ → being-prop-is-prop fe))
                (λ _ → ×₃-is-prop
                         (Π₂-is-prop fe (λ _ _ → being-prop-is-prop fe))
                         (being-dominant-is-prop (d , i) 𝟙)
                         (Π₄-is-prop fe λ _ Q _ _
                                        → being-dominant-is-prop (d , i)
                                                                 (Σ Q)))

\end{code}

We could equivalently define a dominance to be d : Ω 𝓣 → Ω 𝓦. Let's try.

\begin{code}

module _ {𝓣 𝓦 : Universe} where

 D₃' : (Ω 𝓣 → Ω 𝓦) → 𝓦  ̇ 
 D₃' d = (d ⊤) holds

 D₄' : (Ω 𝓣 → Ω 𝓦) → (𝓣 ⁺) ⊔ 𝓦  ̇
 D₄' d = (P : Ω 𝓣)
       → (Q : P holds → Ω 𝓣)
       → (d P) holds
       → ((p : P holds) → d (Q p) holds)
       → (d ((Σ p ꞉ P holds , (Q p) holds) , ΣQ-is-prop P Q)) holds
  where
   ΣQ-is-prop : (P : Ω 𝓣)
              → (Q : P holds → Ω 𝓣)
              → is-prop (Σ p ꞉ P holds , (Q p) holds)
   ΣQ-is-prop P Q =
     subsets-of-props-are-props (P holds)
                                (λ p → Q p holds)
                                (holds-is-prop P)
                                (λ {p} → holds-is-prop (Q p))

 is-dominance' : (Ω 𝓣 → Ω 𝓦) → (𝓣 ⁺) ⊔ 𝓦  ̇
 is-dominance' d = D₃' d × D₄' d

 Dominance' : (𝓣 ⁺) ⊔ (𝓦 ⁺)  ̇
 Dominance' = Σ d ꞉ (Ω 𝓣 → Ω 𝓦) , is-dominance' d

 is-dominant' : Dominance' → (Ω 𝓣 → Ω 𝓦)
 is-dominant' (d , _) = d

\end{code}

I'm not sure which definition is preferred so for now we will work with the
former.

We will define a lift operation on a Dominance. In Simpson the notion of
subterminality is used to define the lifting functor. We observe that this
notion is equivalent to being a proposition. So we can define our lifting
functor on types in a bit simpler of a way... 

\begin{code}

module _ {𝓣 𝓦 : Universe} where

 open dominance-def 𝓣 𝓦

 module _ (D : Dominance) where

  𝕃₀ : 𝓣  ̇ → (𝓣 ⁺) ⊔ 𝓦  ̇
  𝕃₀ X = Σ P ꞉ (Dominant-Propositions D) , (P dom-holds → X)

  𝕃₁ : {X Y : 𝓣  ̇} (f : X → Y) → 𝕃₀ X → 𝕃₀ Y
  𝕃₁ f ((P , is-dom) , h) = ((P , is-dom) , f ∘ h)

  𝕃-prop : {X : 𝓣  ̇} → 𝕃₀ X → Ω 𝓣
  𝕃-prop = pr₁ ∘ pr₁

  𝕃-dom : {X : 𝓣  ̇} → (u : 𝕃₀ X) → is-dominant D ((𝕃-prop u) holds)
  𝕃-dom = pr₂ ∘ pr₁

  𝕃-map : {X : 𝓣  ̇} → (u : 𝕃₀ X) → (𝕃-prop u) holds → X
  𝕃-map = pr₂

\end{code}

We will now characterize the identity on 𝕃 X under the assumption that
X has an identity system. The goal is to show

  (P , P-is-dom , h) ＝ (P' , P'-is-dom , h')
≃ Σ (f , g) ꞉ (P holds → P' holds) × (P' holds → P holds)
    , (x : P holds) (x' : P' holds) → h x ≃⟨ X ⟩ h' x'
     
where ≃⟨ X ⟩ is the charcterization of identity on X. This definition is
more symmetric but only works because P and P' are props. The equivalent,
but more robust, h ∼ h' ∘ f (or h ∘ g ∼ h') would be easier to generalize
but notice these homotopies still depend on ≃⟨ X ⟩.

As a warm up let's characterize the identity of dominant propositions
which should correspond to our first components above...

\begin{code}

  open sip

  sns-data-dom-prop : SNS {!!} {!!}
  sns-data-dom-prop = ({!!} , {!!} , {!!})
   where
    ι : {!!}
    ι = {!!}

\end{code}

Dominant-Propositions D

We now want to show that this 'Functor', 𝕃, has monad structure.
Notice 𝕃(𝕃(X)) doesn't make sense as defined so we will instead define a
Kleisli extension.

\begin{code}

  η : (X : 𝓣  ̇) → X → 𝕃₀ X
  η X x = ((⊤ , 𝟙-is-dominant D) , λ _ → x)

  ext : (X Y : 𝓣  ̇) → (X → 𝕃₀ Y) → 𝕃₀ X → 𝕃₀ Y
  ext X Y f ((P , P-is-dom) , h) = ((Q , Q-is-dom) , g)
   where
    Q : Ω 𝓣
    Q = ((Σ x ꞉ P holds , (𝕃-prop (f (h x)) holds))
        , Σ-is-prop (holds-is-prop P) (λ x → holds-is-prop (𝕃-prop (f (h x)))))
    Q-is-dom : is-dominant D (Q holds)
    Q-is-dom = dominant-closed-under-sigma D (P holds)
                                           (λ x → 𝕃-prop (f (h x)) holds)
                                           P-is-dom
                                           (λ x → 𝕃-dom (f (h x)))
    g : Q holds → Y
    g (x , l) = 𝕃-map (f (h x)) l

\end{code}

We need to show that ext has the desired properties.

\begin{code}

  ext-unit : {X : 𝓣  ̇} → ext X X (η X) ＝ id
  ext-unit {X} = dfunext fe {!!}
   where
    H : ext X X (η X) ∼ id
    H ((P , P-is-dom) , h) = {!!}

  ext-coh : {X Y : 𝓣  ̇} (f : X → 𝕃₀ Y) → ext X Y f ∘ η X ＝ f
  ext-coh {X} {Y} f = dfunext fe {!!}
   where
    H : ext X Y f ∘ η X ∼ f
    H x = {!!}

  ext-comp : {X Y Z : 𝓣  ̇} (f : X → 𝕃₀ Y) (g : Y → 𝕃₀ Z)
           → ext Y Z g ∘ ext X Y f ＝ ext X Z (ext Y Z g ∘ f)
  ext-comp {X} {Y} {Z} f g = dfunext fe {!!}
   where
    H : ext Y Z g ∘ ext X Y f ∼ ext X Z (ext Y Z g ∘ f)
    H ((P , P-is-dom) , h) = {!!}

\end{code}
