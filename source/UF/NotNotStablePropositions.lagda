By Tom de Jong in January 2022 with later additions by Martin Escardo

\begin{code}

{-# OPTIONS --safe --without-K #-}

module UF.NotNotStablePropositions where

open import MLTT.Spartan

open import UF.Base
open import UF.DiscreteAndSeparated
open import UF.Embeddings
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.FunExt
open import UF.Hedberg
open import UF.Lower-FunExt
open import UF.Retracts
open import UF.Sets
open import UF.Size
open import UF.SubtypeClassifier
open import UF.SubtypeClassifier-Properties
open import UF.Subsingletons
open import UF.Subsingletons-FunExt

¬¬-stable-↔ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
            → X ↔ Y
            → ¬¬-stable X
            → ¬¬-stable Y
¬¬-stable-↔ (f , g) σ h = f (σ (¬¬-functor g h))

¬¬-stable-≃ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
            → X ≃ Y
            → ¬¬-stable X
            → ¬¬-stable Y
¬¬-stable-≃ e = ¬¬-stable-↔ (⌜ e ⌝ , ⌜ e ⌝⁻¹)

being-¬¬-stable-is-prop : {X : 𝓤 ̇ }
                        → funext 𝓤 𝓤
                        → is-prop X
                        → is-prop (¬¬-stable X)
being-¬¬-stable-is-prop fe i = Π-is-prop fe (λ _ → i)

Ω¬¬ : (𝓤 : Universe)  → 𝓤 ⁺ ̇
Ω¬¬ 𝓤 = Σ p ꞉ Ω 𝓤 , ¬¬-stable (p holds)

_holds¬¬ : Ω¬¬ 𝓤 → 𝓤 ̇
(P , i) holds¬¬ = P holds

Ω¬¬-is-¬¬-separated : funext 𝓤 𝓤
                    → propext 𝓤
                    → is-¬¬-separated (Ω¬¬ 𝓤)
Ω¬¬-is-¬¬-separated fe pe (p , s) (q , t) ν = γ
 where
  α : ¬¬ (p ＝ q)
  α = ¬¬-functor (ap pr₁) ν

  δ : p ＝ q
  δ = equality-of-¬¬stable-propositions fe pe p q s t α

  γ : (p , s) ＝ (q , t)
  γ = to-subtype-＝ (λ p → Π-is-prop fe (λ _ → holds-is-prop p)) δ

\end{code}

A weakening of the notion of Ω-Rezing.

\begin{code}

Ω¬¬-Resizing : (𝓤 𝓥 : Universe) → (𝓤 ⊔ 𝓥)⁺ ̇
Ω¬¬-Resizing 𝓤 𝓥 = (Ω¬¬ 𝓤) is 𝓥 small

\end{code}

Added 25 August 2023 by Martin Escardo from the former file UF.Miscelanea.

\begin{code}

decidable-types-are-¬¬-stable : {X : 𝓤 ̇ } → is-decidable X → ¬¬-stable X
decidable-types-are-¬¬-stable (inl x) φ = x
decidable-types-are-¬¬-stable (inr u) φ = unique-from-𝟘(φ u)

¬¬-stable-types-are-collapsible : funext 𝓤 𝓤₀
                                → {X : 𝓤 ̇ } → ¬¬-stable X → collapsible X
¬¬-stable-types-are-collapsible {𝓤} fe {X} s = (f , g)
 where
  f : X → X
  f x = s(λ u → u x)

  claim₀ : (x y : X) → (u : is-empty X) → u x ＝ u y
  claim₀ x y u = unique-from-𝟘 (u x)

  claim₁ : (x y : X) → (λ u → u x) ＝ (λ u → u y)
  claim₁ x y = dfunext fe (claim₀ x y)

  g : (x y : X) → f x ＝ f y
  g x y = ap s (claim₁ x y)

¬¬-separated-types-are-Id-collapsible : funext 𝓤 𝓤₀ → {X : 𝓤 ̇ }
                                      → is-¬¬-separated X
                                      → Id-collapsible X
¬¬-separated-types-are-Id-collapsible fe s = ¬¬-stable-types-are-collapsible
                                              fe (s _ _)

¬¬-separated-types-are-sets : funext 𝓤 𝓤₀ → {X : 𝓤 ̇ }
                            → is-¬¬-separated X
                            → is-set X
¬¬-separated-types-are-sets fe s = Id-collapsibles-are-sets
                                    (¬¬-separated-types-are-Id-collapsible fe s)

being-¬¬-separated-is-prop : funext 𝓤 𝓤
                           → {X : 𝓤 ̇ }
                           → is-prop (is-¬¬-separated X)
being-¬¬-separated-is-prop {𝓤} fe {X} = prop-criterion f
 where
  f : is-¬¬-separated X → is-prop (is-¬¬-separated X)
  f s = Π-is-prop fe (λ _ →
        Π-is-prop fe (λ _ →
        Π-is-prop fe (λ _ → ¬¬-separated-types-are-sets
                             (lower-funext 𝓤 𝓤 fe) s)))

to-Ω¬¬-＝ : funext 𝓤 𝓤
          → {p q : Ω 𝓤}
            {i : ¬¬-stable (p holds)} {j : ¬¬-stable (q holds)}
          → p ＝ q
          → (p , i) ＝[ Ω¬¬ 𝓤 ] (q , j)
to-Ω¬¬-＝ fe = to-subtype-＝ λ p → being-¬¬-stable-is-prop fe (holds-is-prop p)

Ω¬¬-to-Ω : Ω¬¬ 𝓤 → Ω 𝓤
Ω¬¬-to-Ω = pr₁

_holds' : Ω¬¬ 𝓤 → 𝓤 ̇
_holds' 𝕡 = (Ω¬¬-to-Ω 𝕡) holds

holds'-is-prop : (𝕡 : Ω¬¬ 𝓤) → is-prop (𝕡 holds')
holds'-is-prop 𝕡 = holds-is-prop (Ω¬¬-to-Ω 𝕡)

holds'-is-¬¬-stable : (𝕡 : Ω¬¬ 𝓤) → ¬¬-stable (𝕡 holds')
holds'-is-¬¬-stable = pr₂

from-Ω¬¬-＝ : {p q : Ω 𝓤}
              {i : ¬¬-stable (p holds)} {j : ¬¬-stable (q holds)}
           → (p , i) ＝[ Ω¬¬ 𝓤 ] (q , j)
           → p ＝ q
from-Ω¬¬-＝ = ap Ω¬¬-to-Ω

to-Ω¬¬-＝' : funext 𝓤 𝓤
           → {P Q : 𝓤 ̇ }
             {i : is-prop P} {j : is-prop Q}
             {s : ¬¬-stable P} {t : ¬¬-stable Q}
           → P ＝ Q
           → ((P , i) , s) ＝[ Ω¬¬ 𝓤 ] ((Q , j) , t)
to-Ω¬¬-＝' fe e = to-Ω¬¬-＝ fe (to-Ω-＝ fe e)

from-Ω¬¬-＝' : {P Q : 𝓤 ̇ }
               {i : is-prop P} {j : is-prop Q}
               {s : ¬¬-stable P} {t : ¬¬-stable Q}
             → ((P , i) , s) ＝[ Ω¬¬ 𝓤 ] ((Q , j) , t)
             → P ＝ Q
from-Ω¬¬-＝' e = from-Ω-＝ (from-Ω¬¬-＝ e)

Ω¬¬-is-set : FunExt
           → PropExt
           → is-set (Ω¬¬ 𝓤)
Ω¬¬-is-set {𝓤} fe pe = ¬¬-separated-types-are-sets
                        (fe (𝓤 ⁺) 𝓤₀)
                        (Ω¬¬-is-¬¬-separated (fe 𝓤 𝓤) (pe 𝓤))

Ω¬¬-to-Ω-is-embedding : funext 𝓤 𝓤 → is-embedding (Ω¬¬-to-Ω {𝓤})
Ω¬¬-to-Ω-is-embedding fe = pr₁-is-embedding
                            (λ p → being-¬¬-stable-is-prop fe (holds-is-prop p))

Ω-to-Ω¬¬ : funext 𝓤 𝓤₀ → Ω 𝓤 → Ω¬¬ 𝓤
Ω-to-Ω¬¬ fe p = ((¬¬ (p holds)) , negations-are-props fe) , ¬-is-¬¬-stable

Ω¬¬-retract-equation : (fe : funext 𝓤 𝓤)
                       (fe₀ : funext 𝓤 𝓤₀)
                       (pe : propext 𝓤)
                     → Ω-to-Ω¬¬ fe₀ ∘ Ω¬¬-to-Ω ∼ id
Ω¬¬-retract-equation fe fe₀ pe 𝕡 = to-Ω¬¬-＝' fe
                                    (pe (negations-are-props fe₀)
                                        (holds'-is-prop 𝕡)
                                        (holds'-is-¬¬-stable 𝕡)
                                        ¬¬-intro)

Ω¬¬-is-retract-of-Ω : funext 𝓤 𝓤
                    → propext 𝓤
                    → retract (Ω¬¬ 𝓤) of Ω 𝓤
Ω¬¬-is-retract-of-Ω {𝓤} fe pe = Ω-to-Ω¬¬ (lower-funext 𝓤 𝓤 fe) ,
                                Ω¬¬-to-Ω ,
                                Ω¬¬-retract-equation fe (lower-funext 𝓤 𝓤 fe) pe

𝟘-is-¬¬-stable : ¬¬ 𝟘 {𝓤} → 𝟘 {𝓥}
𝟘-is-¬¬-stable ϕ = 𝟘-elim (ϕ 𝟘-elim)

𝟙-is-¬¬-stable : ¬¬ 𝟙 {𝓤} → 𝟙 {𝓥}
𝟙-is-¬¬-stable _ = ⋆

⊥Ω¬¬ ⊤Ω¬¬ : Ω¬¬ 𝓤
⊥Ω¬¬ = ⊥ , 𝟘-is-¬¬-stable
⊤Ω¬¬ = ⊤ , 𝟙-is-¬¬-stable

⊥Ω¬¬-is-not-⊤Ω¬¬ : ⊥Ω¬¬ {𝓤} ≠ ⊤Ω¬¬ {𝓤}
⊥Ω¬¬-is-not-⊤Ω¬¬ e = ⊥-is-not-⊤ (ap Ω¬¬-to-Ω e)

𝟚-to-Ω¬¬ : 𝟚 → Ω¬¬ 𝓤
𝟚-to-Ω¬¬ ₀ = ⊥Ω¬¬
𝟚-to-Ω¬¬ ₁ = ⊤Ω¬¬

module _ (fe : FunExt) (pe : PropExt) where

 𝟚-to-Ω¬¬-is-embedding : is-embedding (𝟚-to-Ω¬¬ {𝓤})
 𝟚-to-Ω¬¬-is-embedding _ (₀ , p) (₀ , q) = to-Σ-＝ (refl , Ω¬¬-is-set fe pe p q)
 𝟚-to-Ω¬¬-is-embedding _ (₀ , p) (₁ , q) =
  𝟘-elim (⊥-is-not-⊤ (ap pr₁ p ∙ (ap pr₁ q)⁻¹))
 𝟚-to-Ω¬¬-is-embedding _ (₁ , p) (₀ , q) =
  𝟘-elim (⊥-is-not-⊤ (ap pr₁ q ∙ (ap pr₁ p ⁻¹)))
 𝟚-to-Ω¬¬-is-embedding _ (₁ , p) (₁ , q) = to-Σ-＝ (refl , Ω¬¬-is-set fe pe p q)

 𝟚-to-Ω¬¬-fiber : ((p , s) : Ω¬¬ 𝓤) → fiber 𝟚-to-Ω¬¬ (p , s) ≃ (¬ (p holds) + p holds)
 𝟚-to-Ω¬¬-fiber {𝓤} 𝕡@(p , s) =
  fiber (𝟚-to-Ω¬¬ {𝓤}) 𝕡                        ≃⟨by-definition⟩
  (Σ n ꞉ 𝟚 , 𝟚-to-Ω¬¬ {𝓤} n ＝ 𝕡)              ≃⟨ alternative-+ ⟩
  (𝟚-to-Ω¬¬ ₀ ＝ p , s) + (𝟚-to-Ω¬¬ ₁ ＝ p , s) ≃⟨ I ⟩
  (⊥ ＝ p) + (⊤ ＝ p)                           ≃⟨ II ⟩
  (¬ (p holds) + (p holds))                     ■
  where
   I = +-cong
        (embedding-criterion-converse' pr₁
          (pr₁-is-embedding
            (λ p → being-¬¬-stable-is-prop (fe _ _) (holds-is-prop p))) _ _)
        (embedding-criterion-converse' pr₁
          (pr₁-is-embedding
            (λ p → being-¬¬-stable-is-prop (fe _ _) (holds-is-prop p))) _ _)

   II = +-cong
           (＝-flip ● equal-⊥-≃ (pe _) (fe _ _) p)
           (＝-flip ● equal-⊤-≃ (pe _) (fe _ _) p)

 𝟚-to-Ω¬¬-is-small-map : (𝟚-to-Ω¬¬ {𝓤}) is 𝓤 small-map
 𝟚-to-Ω¬¬-is-small-map (p , s) = (¬ (p holds) + p holds) ,
                                  ≃-sym (𝟚-to-Ω¬¬-fiber (p , s))

\end{code}

Added 3rd September 2023 by Martin Escardo.

\begin{code}

two-Ω¬¬-props-distinct-from-a-third-are-equal
 : funext 𝓤 𝓤
 → propext 𝓤
 → (𝕡₀ 𝕡₁ 𝕢 : Ω¬¬ 𝓤) → 𝕡₀ ≠ 𝕢 → 𝕡₁ ≠ 𝕢 → 𝕡₀ ＝ 𝕡₁
two-Ω¬¬-props-distinct-from-a-third-are-equal fe pe 𝕡₀ 𝕡₁ 𝕢 ν₀ ν₁ = III
 where
  I : ¬ (Ω¬¬-to-Ω 𝕡₀ ≠ Ω¬¬-to-Ω 𝕡₁)
  I = no-three-distinct-propositions' fe pe
      (Ω¬¬-to-Ω 𝕡₀) (Ω¬¬-to-Ω 𝕡₁) (Ω¬¬-to-Ω 𝕢)
      (λ e → ν₀ (to-Ω¬¬-＝ fe e))
      λ e → ν₁ (to-Ω¬¬-＝ fe e)

  II : ¬ (𝕡₀ ≠ 𝕡₁)
  II = ¬¬-functor (embeddings-are-lc Ω¬¬-to-Ω (Ω¬¬-to-Ω-is-embedding fe)) I

  III : 𝕡₀ ＝ 𝕡₁
  III = Ω¬¬-is-¬¬-separated fe pe 𝕡₀ 𝕡₁ II

\end{code}

Added 3rd April 2025 by Fredrik Bakke

\begin{code}

¬¬-stable-weakly-decidable-types-are-decidable : {X : 𝓤 ̇ }
                                               → is-decidable (¬ X)
                                               → ¬¬-stable X
                                               → is-decidable X
¬¬-stable-weakly-decidable-types-are-decidable (inl nx) ¬¬-elim-X = inr nx
¬¬-stable-weakly-decidable-types-are-decidable (inr x) ¬¬-elim-X =
 inl (¬¬-elim-X x)

\end{code}

Added 24th July 2026 by Ian Ray.

\begin{code}

¬¬-props-satisfy-contrapositive : (P : Ω 𝓤) (Q : Ω¬¬ 𝓥)
                                → (¬ (Q holds¬¬) → ¬ (P holds))
                                → P holds → Q holds¬¬
¬¬-props-satisfy-contrapositive P (Q , Q¬¬stable) ¬Q→¬P Pholds
 = Q¬¬stable (λ ¬Qholds → ¬Q→¬P ¬Qholds Pholds)
