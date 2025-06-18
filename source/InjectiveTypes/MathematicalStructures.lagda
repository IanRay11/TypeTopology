Martin Escardo, 16th August 2023, with more improvements 18th June 2025.

This file improves InjectiveTypes.MathematicalStructuresOriginal at
the cost of being harder to understand, with the benefit of at the
same time being more general and allowing shorter proofs. It relies on
the file InjectiveTypes.Sigma, which also arises as a generalization
of the original file InjectiveTypes.MathematicalStructuresOriginal.

We give a sufficient condition for types of mathematical structures,
such as pointed types, ∞-magmas, monoids, groups, etc. to be
algebraically injective. We use algebraic flabbiness as our main tool.

There is already enough discussion in the files
InjectiveTypes.MathematicalStructuresOriginal and
InjectiveTypes.Sigma, which we will not repeat here. But we include
some further remarks.

\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import UF.Univalence

module InjectiveTypes.MathematicalStructures
        (ua : Univalence)
       where

open import UF.FunExt
open import UF.UA-FunExt

private
 fe : FunExt
 fe = Univalence-gives-FunExt ua

 fe' : Fun-Ext
 fe' {𝓤} {𝓥} = fe 𝓤 𝓥

open import InjectiveTypes.Blackboard fe
open import InjectiveTypes.Sigma fe
open import MLTT.Spartan
open import Taboos.Decomposability fe
open import UF.Base
open import UF.Equiv
open import UF.ClassicalLogic
open import UF.PropIndexedPiSigma
open import UF.Retracts
open import UF.Sets
open import UF.Sets-Properties
open import UF.SubtypeClassifier

\end{code}

It is convenient to work with the following definition of flabbiness
of a universe, which uses equivalence of types rather than equality.

\begin{code}

Flabby : (𝓤 : Universe) → 𝓤 ⁺ ̇
Flabby 𝓤 = Σ ⨆ ꞉ ((p : Ω 𝓤) → (p holds → 𝓤 ̇ ) → 𝓤 ̇ )
                , ((p : Ω 𝓤) (A : p holds → 𝓤 ̇) (h : p holds) → ⨆ p A ≃ A h)

\end{code}

Using univalence we can convert back and forth the usual definition,
but in this file we need the first one only.

\begin{code}

from-Flabby : Flabby 𝓤 → aflabby (𝓤 ̇ ) 𝓤
from-Flabby {𝓤} (⨆ , e) P i A =
 ⨆ (P , i) A , (λ h → eqtoid (ua 𝓤) _ _ (e (P , i) A h))

to-Flabby : aflabby (𝓤 ̇ ) 𝓤 → Flabby 𝓤
to-Flabby {𝓤} aflab =
 (λ p A → pr₁ (aflab (p holds) (holds-is-prop p) A)) ,
 (λ p A h → idtoeq _ _ (pr₂ (aflab (p holds) (holds-is-prop p) A) h))

\end{code}

We already know that universes are flabby in two ways, using ⨆ := Π
and ⨆ := Σ, but we give constructions that they are Flabby without
univalence, and hence have better computational behaviour, which will
simplify many proofs and constructions.

\begin{code}

Π-𝕡𝕣𝕠𝕛 : (p : Ω 𝓤) {A : p holds → 𝓤 ̇ } (h : p holds)
      → Π A ≃ A h
Π-𝕡𝕣𝕠𝕛 p h = prop-indexed-product h fe' (holds-is-prop p)

universes-are-Flabby-Π : Flabby 𝓤
universes-are-Flabby-Π {𝓤} = (λ p A → Π A) ,
                             (λ p A → Π-𝕡𝕣𝕠𝕛 p)

universes-are-flabby-Π : aflabby (𝓤  ̇) 𝓤
universes-are-flabby-Π {𝓤} = from-Flabby universes-are-Flabby-Π

universes-are-Flabby-Σ : Flabby 𝓤
universes-are-Flabby-Σ {𝓤} = (λ p A → Σ A) ,
                             (λ p A h → prop-indexed-sum h (holds-is-prop p))

universes-are-flabby-Σ : aflabby (𝓤  ̇) 𝓤
universes-are-flabby-Σ {𝓤} = from-Flabby universes-are-Flabby-Σ

\end{code}

In this file we apply only the the above constructions for Π, but we
include those for Σ for illustration (and perhaps for future use).

We now work with an arbitrary notion of structure on 𝓤.

\begin{code}

module _ (S : 𝓤 ̇ → 𝓥 ̇ ) where

\end{code}

By the results of InjectiveTypes.Sigma, we get that Σ S is aflabby in
two ways, assuming the compatibility condition for the flabbiness
data.

\begin{code}

 module _ (ϕ : aflabby (𝓤 ̇ ) 𝓤) where

  aflabbiness-of-type-of-structured-types : compatibility-data S ϕ
                                          → aflabby (Σ S) 𝓤
  aflabbiness-of-type-of-structured-types = Σ-is-aflabby S ϕ

  ainjectivity-of-type-of-structures : compatibility-data S ϕ
                                     → ainjective-type (Σ S) 𝓤 𝓤
  ainjectivity-of-type-of-structures = aflabby-types-are-ainjective (Σ S)
                                       ∘ aflabbiness-of-type-of-structured-types

\end{code}

We apply this with ϕ taken to be the above canonical Π-flabby
structure on the universe.

Next we want to simplify working with compatibility data, where we
avoid transports by working with the following function treq and
suitable choices of T and T-refl in the examples below.

\begin{code}

 treq : {X Y : 𝓤 ̇ } → X ≃ Y → S X → S Y
 treq {X} {Y} 𝕗 = transport S (eqtoid (ua 𝓤) X Y 𝕗)

\end{code}

We don't need the following fact explicitly, but it is worth keeping
it in mind:

\begin{code}

 _ : {X Y : 𝓤 ̇ } (𝕗 : X ≃ Y) → is-equiv (treq 𝕗)
 _ = λ 𝕗 → transports-are-equivs (eqtoid (ua 𝓤) _ _ 𝕗)

\end{code}

The main additional work in this file on top of InjectiveTypes.Sigma
is to make it easier to work with the compatibility condition for the
purpose of injectivity of types of mathematical structures.

We work with hypothetical T and T-refl with the following types.

\begin{code}

 module _ (T      : {X Y : 𝓤 ̇ } → X ≃ Y → S X → S Y)
          (T-refl : {X : 𝓤 ̇ } → T (≃-refl X) ∼ id)
        where

\end{code}

The point is that any such T can be equivalently expressed as a
transport and hence we may apply the theorems of the imported file
InjectiveTypes.Sigma, but it may be easier to check the compatibility
condition using T rather than transport (see examples below).

\begin{code}

  T-is-treq : {X Y : 𝓤 ̇ } (𝕗 : X ≃ Y)
            → T 𝕗 ∼ treq 𝕗
  T-is-treq {X} {Y} 𝕗 s = JEq (ua 𝓤) X A I Y 𝕗
   where
    A : (Y : 𝓤 ̇ ) (𝕗 : X ≃ Y) → 𝓥 ̇
    A Y 𝕗 = T 𝕗 s ＝ treq 𝕗 s

    I : A X (≃-refl X)
    I = T (≃-refl X) s                                ＝⟨ T-refl s ⟩
        s                                             ＝⟨ refl ⟩
        transport S refl s                            ＝⟨ II ⟩
        transport S (eqtoid (ua 𝓤) X X (≃-refl X)) s  ＝⟨ refl ⟩
        treq (≃-refl X) s                             ∎
      where
       II = (ap (λ - → transport S - s) (eqtoid-refl (ua 𝓤) X))⁻¹

\end{code}



\begin{code}

  module compatibility-data-construction (ϕ@(⨆ , ε) : Flabby 𝓤) where

   derived-ρ : (p : Ω 𝓤)
               (A : p holds → 𝓤 ̇ )
             → S (⨆ p A) → ((h : p holds) → S (A h))
   derived-ρ p A s h = T (ε p A h) s

   compatibility-data-for-derived-ρ : 𝓤 ⁺ ⊔ 𝓥 ̇
   compatibility-data-for-derived-ρ = (p : Ω 𝓤)
                                      (A : p holds → 𝓤 ̇ )
                                    → has-section (derived-ρ p A)

   κ : compatibility-data-for-derived-ρ → compatibility-data S (from-Flabby ϕ)
   κ t p A = III
    where

     II : derived-ρ p A ∼ ρ S (from-Flabby ϕ) p A
     II s =
      derived-ρ p A s                                     ＝⟨ refl ⟩
      (λ h → T (ε p A h) s)                               ＝⟨ I₀ ⟩
      (λ h → treq (ε p A h) s)                            ＝⟨ refl ⟩
      (λ h → transport S (eqtoid (ua 𝓤) _ _ (ε p A h)) s) ＝⟨ refl ⟩
      ρ S (from-Flabby ϕ) p A s                           ∎
      where
       I₀ = dfunext fe' (λ h → T-is-treq (ε p A h) s)

     III : has-section (ρ S (from-Flabby ϕ) p A)
     III = has-section-closed-under-∼ (derived-ρ p A) _ (t p A) (∼-sym II)

\end{code}

This completes the construction, but we record that the section map
of the conclusion is literally the same as that of the hypothesis.

\begin{code}

     _ = section-of (ρ S (from-Flabby ϕ) p A) III  ＝⟨ refl ⟩
         section-of (derived-ρ p A) (t p A)        ∎

\end{code}

But notice that the above remark is only saying that the section map
is literally the same. It is definitely not saying that the proof that
it is a section is also the same (literally or otherwise).

We can specialize this to the Π and Σ flabbiness structures discussed
above, to get

\begin{code}

  module _ where

   open compatibility-data-construction universes-are-Flabby-Π

   ρΠ : (p : Ω 𝓤)
        (A : p holds → 𝓤 ̇ )
      → S (Π A) → ((h : p holds) → S (A h))
   ρΠ = derived-ρ

   compatibility-data-Π : 𝓤 ⁺ ⊔ 𝓥 ̇
   compatibility-data-Π = (p : Ω 𝓤)
                          (A : p holds → 𝓤 ̇ )
                        → has-section (ρΠ p A)

   Π-construction : compatibility-data-Π
                  → compatibility-data S universes-are-flabby-Π
   Π-construction = κ

\end{code}

We use the following definitional equality a number of types.

\begin{code}

   _ : ρΠ ＝ λ p A s h → T (Π-𝕡𝕣𝕠𝕛 p h) s
   _ = refl

\end{code}

For our examples below, we only need the above functions ρΠ,
compatibility-data-Π and Π-construction, but we take the opportunity
to remark that we also have the following.

\begin{code}

  module _ where

   open compatibility-data-construction universes-are-Flabby-Σ

   ρΣ : (p : Ω 𝓤)
        (A : p holds → 𝓤 ̇ )
      → S (Σ A) → ((h : p holds) → S (A h))
   ρΣ = derived-ρ

   compatibility-data-Σ : 𝓤 ⁺ ⊔ 𝓥 ̇
   compatibility-data-Σ = (p : Ω 𝓤)
                          (A : p holds → 𝓤 ̇ )
                        → has-section (ρΣ p A)

   Σ-construction : compatibility-data-Σ
                  → compatibility-data S universes-are-flabby-Σ
   Σ-construction = κ

\end{code}

Example. The type of pointed types is algebraically injective. We use
the Π-flabbiness of the universe.

\begin{code}

Pointed-type : (𝓤 : Universe) → 𝓤 ⁺ ̇
Pointed-type 𝓤 = Σ X ꞉ 𝓤 ̇ , X

Pointed : 𝓤 ̇ → 𝓤 ̇
Pointed X = X

Pointed-Π-data : compatibility-data (Pointed {𝓤}) universes-are-flabby-Π
Pointed-Π-data {𝓤} = Π-construction Pointed T T-refl c
 where
  S : 𝓤 ̇ → 𝓤 ̇
  S X = X

  T : {X Y : 𝓤 ̇ } → (X ≃ Y) → X → Y
  T = ⌜_⌝

  T-refl : {X : 𝓤 ̇ } → T (≃-refl X) ∼ id
  T-refl x = refl

  c : compatibility-data-Π S T T-refl
  c p A = equivs-have-sections id (id-is-equiv (Π A))

\end{code}

This completes the construction, but we remark that the definition of
c works because we have the following definitional equality.

\begin{code}

  _ : (p : Ω 𝓤) (A : p holds → 𝓤 ̇) → ρΠ S T T-refl p A ＝ 𝑖𝑑 (S (Π A))
  _ = λ p A → refl

\end{code}

Hence we conclude that the type of pointed types is injective.

\begin{code}

ainjectivity-of-type-of-pointed-types : ainjective-type (Pointed-type 𝓤) 𝓤 𝓤
ainjectivity-of-type-of-pointed-types =
 ainjectivity-of-type-of-structures
  Pointed
  universes-are-flabby-Π
  Pointed-Π-data

\end{code}

Example. The type of ∞-magmas is algebraically injective. The proof is
an entirely routine application of the above general theorem after we
guess what T should be.

\begin{code}

∞-Magma : (𝓤 : Universe) → 𝓤 ⁺ ̇
∞-Magma 𝓤 = Σ X ꞉ 𝓤 ̇ , (X → X → X)

∞-Magma-structure : 𝓤 ̇ → 𝓤 ̇
∞-Magma-structure = λ X → X → X → X

∞-Magma-structure-Π-data : compatibility-data
                            (∞-Magma-structure {𝓤})
                            universes-are-flabby-Π
∞-Magma-structure-Π-data {𝓤} =
 Π-construction S T T-refl ρΠ-has-section
 where
  S = ∞-Magma-structure

  T : {X Y : 𝓤 ̇ } → (X ≃ Y) → S X → S Y
  T 𝕗 _·_ = λ y y' → ⌜ 𝕗 ⌝ (⌜ 𝕗 ⌝⁻¹ y · ⌜ 𝕗 ⌝⁻¹ y')

  T-refl : {X : 𝓤 ̇ } → T (≃-refl X) ∼ id
  T-refl _·_ = refl

  module _ (p : Ω 𝓤)
           (A : p holds → 𝓤 ̇ )
         where

   π : (h : p holds) → Π A ≃ A h
   π = Π-𝕡𝕣𝕠𝕛 p

   r : S (Π A) → ((h : p holds) → S (A h))
   r _·_ h a b = ⌜ π h ⌝ (⌜ π h ⌝⁻¹ a · ⌜ π h ⌝⁻¹ b)

   _ : r ＝ ρΠ S T T-refl p A
   _ = refl

   σ : ((h : p holds) → S (A h)) → S (Π A)
   σ g α β h = g h (⌜ π h ⌝ α) (⌜ π h ⌝ β)

   rσ : r ∘ σ ∼ id
   rσ g =
    r (σ g)                                                         ＝⟨ refl ⟩
    (λ h a b → g h (⌜ π h ⌝ (⌜ π h ⌝⁻¹ a)) (⌜ π h ⌝ (⌜ π h ⌝⁻¹ b))) ＝⟨ II ⟩
    (λ h a b → g h a b)                                             ＝⟨ refl ⟩
    g                                                               ∎
     where
      II = dfunext fe' (λ h →
           dfunext fe' (λ a →
           dfunext fe' (λ b →
            ap₂ (g h)
             (inverses-are-sections' (π h) a)
             (inverses-are-sections' (π h) b))))

   ρΠ-has-section : has-section (ρΠ S T T-refl p A)
   ρΠ-has-section = σ , rσ

ainjectivity-of-∞-Magma : ainjective-type (∞-Magma 𝓤) 𝓤 𝓤
ainjectivity-of-∞-Magma =
 ainjectivity-of-type-of-structures
  ∞-Magma-structure
  universes-are-flabby-Π
  ∞-Magma-structure-Π-data

\end{code}

A corollary is that the type ∞-Magma 𝓤 doesn't have any non-trivial
decidable property unless weak excluded middle holds.

\begin{code}

decomposition-of-∞-Magma-gives-WEM : decomposition (∞-Magma 𝓤) → typal-WEM 𝓤
decomposition-of-∞-Magma-gives-WEM {𝓤} =
 decomposition-of-ainjective-type-gives-WEM
  (univalence-gives-propext (ua 𝓤))
  (∞-Magma 𝓤)
  ainjectivity-of-∞-Magma

\end{code}

The same is true for the type of pointed types, of course, and for any
injective type.

Example. The type of pointed ∞-magmas is injective.

\begin{code}

open import UF.SIP-Examples
open monoid

∞-Magma∙ : (𝓤 : Universe) → 𝓤 ⁺ ̇
∞-Magma∙ 𝓤 = Σ X ꞉ 𝓤 ̇ , (X → X → X) × X

∞-Magma∙-structure : 𝓤 ̇ → 𝓤 ̇
∞-Magma∙-structure = monoid-structure

∞-Magma∙-structure-Π-data : compatibility-data
                                  (∞-Magma∙-structure {𝓤})
                                  universes-are-flabby-Π
∞-Magma∙-structure-Π-data =
 compatibility-data-×
  universes-are-flabby-Π
  ∞-Magma-structure-Π-data
  Pointed-Π-data

ainjectivity-of-∞-Magma∙ : ainjective-type (∞-Magma∙ 𝓤) 𝓤 𝓤
ainjectivity-of-∞-Magma∙ =
 ainjectivity-of-type-of-structures
  ∞-Magma∙-structure
  universes-are-flabby-Π
  ∞-Magma∙-structure-Π-data

\end{code}

Example. The type of monoids is injective. We just have to check that
the monoid axioms are closed under Π.

\begin{code}

Monoid-Π-data : compatibility-data {𝓤 ⁺}
                 (λ X → Σ s ꞉ monoid-structure X , monoid-axioms X s)
                 universes-are-flabby-Π
Monoid-Π-data {𝓤} =
 compatibility-data-with-axioms
  universes-are-flabby-Π
  monoid-structure
  ∞-Magma∙-structure-Π-data
  monoid-axioms
  (monoid-axioms-is-prop fe')
  axioms-Π-data
 where
  σ : (p : Ω 𝓤) (A : p holds → 𝓤 ̇ )
    → ((h : p holds) → monoid-structure (A h)) → monoid-structure (Π A)
  σ p A = section-of
           (ρ monoid-structure universes-are-flabby-Π p A)
           (∞-Magma∙-structure-Π-data p A)

  axioms-Π-data
    : (p : Ω 𝓤)
      (A : p holds → 𝓤 ̇ )
      (α : (h : p holds) → monoid-structure (A h))
      (F : (h : p holds) → monoid-axioms (A h) (α h))
    → monoid-axioms (Π A) (σ p A α)
  axioms-Π-data p A α F = I , II , III , IV
   where
    _·_ : Π A → Π A → Π A
    f · g = λ h → pr₁ (α h) (f h) (g h)

    e : Π A
    e h = pr₂ (α h)

    _ : σ p A α ＝ (_·_ , e)
    _ = refl

    I : is-set (Π A)
    I = Π-is-set fe' (λ h →
         case F h of
          λ (Ah-is-set , ln , rn , assoc) → Ah-is-set)

    II : left-neutral e _·_
    II f = dfunext fe' (λ h →
            case F h of
             λ (Ah-is-set , ln , rn , assoc) → ln (f h))

    III : right-neutral e _·_
    III g = dfunext fe' (λ h →
             case F h of
              λ (Ah-is-set , ln , rn , assoc) → rn (g h))

    IV : associative _·_
    IV f g k = dfunext fe' (λ h →
                case F h of
                 λ (Ah-is-set , ln , rn , assoc) → assoc (f h) (g h) (k h))

ainjectivity-of-Monoid : ainjective-type (Monoid {𝓤}) 𝓤 𝓤
ainjectivity-of-Monoid {𝓤} =
 ainjectivity-of-type-of-structures
  (λ X → Σ s ꞉ monoid-structure X , monoid-axioms X s)
  universes-are-flabby-Π
  Monoid-Π-data

\end{code}

TODO. It is easy to add further axioms to monoids to get groups, and
then show that the type of groups is injective using the above
technique. I expect this to be entirely routine as the example of
monoids.

TODO. More techniques are needed to show that the type of 1-categories
would be injective. This is more interesting.

NB. The type Ordinal 𝓤 of well-ordered sets in 𝓤 is also injective,
but for a different reason.

TODO. The type of posets should be injective, but with a different
proof. Maybe the proof for the type of ordinals can be adapted
(check). What about metric spaces? Notice that both posets and metric
spaces have structure of the form X → X → R where R is
respectively Ω 𝓤 and ℝ.
