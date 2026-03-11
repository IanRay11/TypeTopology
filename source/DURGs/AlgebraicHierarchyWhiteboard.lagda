Ian Ray. 3rd March 2026.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module DURGs.AlgebraicHierarchyWhiteboard where

open import MLTT.Spartan 
open import DURGs.BivariantMidpointLenses
open import DURGs.ReflexiveGraphs
open import DURGs.ReflexiveGraphConstructions
open import DURGs.ReflexiveGraphExamples
open import DURGs.UnivalentReflexiveGraphClosureProperties
open import DURGs.DisplayedReflexiveGraphs
open import DURGs.DisplayedUnivalentReflexiveGraphs
open import DURGs.Lenses
open import DURGs.UnivalentFamilies
open import DURGs.UnivalentReflexiveGraphs
open import DURGs.UnivalenceProperty
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.FunExt
open import UF.PropTrunc
open import UF.Sets
open import UF.Sets-Properties
open import UF.Subsingletons
open import UF.SubtypeClassifier
open import UF.Univalence

\end{code}

We define some algerbaic structures characterize their equality with lenses and
consider the induced hierarchy and it's relationships.

\begin{code}

Magma : (𝓤 : Universe) → (𝓤 ⁺) ̇
Magma 𝓤 = Σ M@(X , _) ꞉ ∞-Magma 𝓤 , is-set X

Magma-refl-graph : (𝓤 : Universe)
                 → is-univalent 𝓤
                 → Fun-Ext
                 → refl-graph (𝓤 ⁺) 𝓤
Magma-refl-graph 𝓤 ua fe = ∞-Magma-unbiased-lens-total 𝓤 ﹐ (I Δ II)
 where
  I = (∞-Magma-unbiased-lens-total 𝓤
       , ∞-Magma-unbiased-lens-total-univalent 𝓤 ua fe)
  II : ∞-Magma 𝓤 → 𝓤 ̇
  II (X , _) = is-set X

Magma-univalent-refl-graph : (𝓤 : Universe)
                           → is-univalent 𝓤
                           → Fun-Ext
                           → univalent-refl-graph (𝓤 ⁺) 𝓤
Magma-univalent-refl-graph 𝓤 ua fe
 = (Magma-refl-graph 𝓤 ua fe , prop-display-total-univalent I II III)
 where
  I = (∞-Magma-unbiased-lens-total 𝓤
       , ∞-Magma-unbiased-lens-total-univalent 𝓤 ua fe)
  II : ∞-Magma 𝓤 → 𝓤 ̇
  II (X , _) = is-set X
  III : (x : ⊰ I ⊱ᵤ) → is-prop (II x)
  III x = being-set-is-prop fe

Magma-＝-char
 : {𝓤 : Universe} 
 → Fun-Ext
 → is-univalent 𝓤
 → (((X , _·X_) , _) ((Y , _·Y_) , _) : Magma 𝓤)
 → (((X , _·X_) , _) ＝[ Magma 𝓤 ] ((Y , _·Y_) , _))
  ≃ (Σ e ꞉ X ≃ Y , ((x y : X) → ⌜ e ⌝ (x ·X y) ＝ (⌜ e ⌝ x ·Y ⌜ e ⌝ y)))
Magma-＝-char {𝓤} fe ua 𝓧@((X , _·X_) , X-is-set) 𝓨@((Y , _·Y_) , Y-is-set)
 = (𝓧 ＝ 𝓨)                                                             ≃⟨ IV ⟩
   (𝓧 ≈⟨ Magma-refl-graph 𝓤 ua fe ⟩ 𝓨)                                  ≃⟨ V ⟩
   (Σ e ꞉ X ≃ Y , ((x y : X) → ⌜ e ⌝ (x ·X y) ＝ (⌜ e ⌝ x ·Y ⌜ e ⌝ y)))  ■
 where
  I = (∞-Magma-unbiased-lens-total 𝓤
       , ∞-Magma-unbiased-lens-total-univalent 𝓤 ua fe)
  II : ∞-Magma 𝓤 → 𝓤 ̇
  II (X , _) = is-set X
  III : (x : ⊰ I ⊱ᵤ) → is-prop (II x)
  III x = being-set-is-prop fe
  IV = id-equiv-edge (Magma-univalent-refl-graph 𝓤 ua fe) 𝓧 𝓨
  V = prop-display-total-edge-char
       I II III (X , _·X_) (Y , _·Y_) X-is-set Y-is-set

\end{code}

We give an alternative, yet reasonable, definition of the type of magmas. We
then characterize the identity type and consider questions of interoperability
between these two different presentations of the magma structure.

\begin{code}

Magma-hSet : (𝓤 : Universe) → (𝓤 ⁺) ̇
Magma-hSet 𝓤 = Σ M@(X , _) ꞉ hSet 𝓤 , (X → X → X)

Magma-hSet-unbiased-lens
 : (𝓤 : Universe)
 → (ua : is-univalent 𝓤)
 → (fe : funext 𝓤 𝓤)
 → (fe' : funext (𝓤 ⁺) 𝓤)
 → bivariant-midpoint-lens 𝓤 𝓤 (hSet-refl-graph ua fe')
Magma-hSet-unbiased-lens 𝓤 ua fe fe' = record
   { bi-lens-fam = λ {(X , _)} {(Y , _)} (e , _) → X ➙ (X ➙ (Δ Y))
   ; lext = λ (e , _) u x x' → ⌜ e ⌝ (u x x')
   ; rext = λ (e , _) u x x' → u (⌜ e ⌝ x) (⌜ e ⌝ x')
   ; ext-R = λ u x x' → refl
   ; rext-R = λ u x x' → refl
   }

Magma-hSet-unbiased-lens-univalent
 : (𝓤 : Universe)
 → (ua : is-univalent 𝓤)
 → (fe : Fun-Ext)
 → bivariant-midpoint-lens-is-univalent (hSet-refl-graph ua fe)
    (Magma-hSet-unbiased-lens 𝓤 ua fe fe)
Magma-hSet-unbiased-lens-univalent
 𝓤 ua fe {(X , _)} {(Y , _)} p
 = univalence-closed-under-cotensor fe X (X ➙ (Δ Y))
    (univalence-closed-under-cotensor fe X (Δ Y)
     (discrete-refl-graph-is-univalent Y))

Magma-hSet-unbiased-lens-display
 : (𝓤 : Universe)
 → (ua : is-univalent 𝓤)
 → (fe : Fun-Ext)
 → displayed-refl-graph 𝓤 𝓤 (hSet-refl-graph ua fe)
Magma-hSet-unbiased-lens-display 𝓤 ua fe
 = disp± (hSet-refl-graph ua fe) , (Magma-hSet-unbiased-lens 𝓤 ua fe fe)

Magma-hSet-unbiased-lens-display-univalent
 : (𝓤 : Universe)
 → (ua : is-univalent 𝓤)
 → (fe : Fun-Ext)
 → is-displayed-univalent-refl-graph (hSet-refl-graph ua fe)
    (Magma-hSet-unbiased-lens-display 𝓤 ua fe)
Magma-hSet-unbiased-lens-display-univalent 𝓤 ua fe
 = disp-bivariant-midpoint-lens-univalent (hSet-refl-graph ua fe)
    (Magma-hSet-unbiased-lens 𝓤 ua fe fe)
    (λ x → Magma-hSet-unbiased-lens-univalent 𝓤 ua fe
            (𝓻 (hSet-refl-graph ua fe) x))

Magma-hSet-unbiased-lens-total
 : (𝓤 : Universe)
 → (ua : is-univalent 𝓤)
 → (fe : Fun-Ext)
 → refl-graph (𝓤 ⁺) 𝓤
Magma-hSet-unbiased-lens-total 𝓤 ua fe
 = (hSet-refl-graph ua fe) ﹐ Magma-hSet-unbiased-lens-display 𝓤 ua fe

private
 obs1 : (𝓤 : Universe)
      → (ua : is-univalent 𝓤)
      → (fe : Fun-Ext)
      → ⊰ Magma-hSet-unbiased-lens-total 𝓤 ua fe ⊱ ＝ Magma-hSet 𝓤
 obs1 𝓤 ua fe = refl

Magma-hSet-unbiased-lens-total-is-univalent
 : (𝓤 : Universe)
 → (ua : is-univalent 𝓤)
 → (fe : Fun-Ext)
 → is-univalent-refl-graph (Magma-hSet-unbiased-lens-total 𝓤 ua fe)
Magma-hSet-unbiased-lens-total-is-univalent 𝓤 ua fe
 = univalence-closed-under-total
    (hSet-refl-graph ua fe)
    (Magma-hSet-unbiased-lens-display 𝓤 ua fe)
    (hSet-refl-graph-is-univalent ua fe fe)
    (Magma-hSet-unbiased-lens-display-univalent 𝓤 ua fe)

Magma-hSet-unbiased-lens-univalent-total
 : (𝓤 : Universe)
 → (ua : is-univalent 𝓤)
 → (fe : Fun-Ext)
 → univalent-refl-graph (𝓤 ⁺) 𝓤
Magma-hSet-unbiased-lens-univalent-total 𝓤 ua fe
 = (Magma-hSet-unbiased-lens-total 𝓤 ua fe
    , Magma-hSet-unbiased-lens-total-is-univalent 𝓤 ua fe)

\end{code}

Magma-hSet-＝-char
 : {𝓤 : Universe} 
 → Fun-Ext
 → is-univalent 𝓤
 → (((X , _) , _·X_) ((Y , _) , _·Y_) : Magma-hSet 𝓤)
 → (((X , _) , _·X_) ＝[ Magma-hSet 𝓤 ] ((Y , _) , _·Y_))
  ≃ (Σ e ꞉ X ≃ Y , ((x y : X) → ⌜ e ⌝ (x ·X y) ＝ (⌜ e ⌝ x ·Y ⌜ e ⌝ y)))
Magma-hSet-＝-char {𝓤} fe ua 𝓧@((X , X-is-set) , _·X_) 𝓨@((Y , Y-is-set) , _·Y_) 
 = (𝓧 ＝ 𝓨)                                                           ≃⟨ I ⟩
   (𝓧 ≈⟨ Magma-hSet-unbiased-lens-total 𝓤 ua fe ⟩ 𝓨)                  ≃⟨ II ⟩
   (Σ p ꞉ (X , X-is-set) ＝ (Y , Y-is-set) ,
    ((x y : X) → ⌜ ⌜ {!hSet-＝-char!} ⌝ p ⌝ (x ·X y)
               ＝ (⌜ ⌜ {!!} ⌝ p ⌝ x ·Y ⌜ ⌜ {!!} ⌝ p ⌝ y)))            ≃⟨ III ⟩
   (Σ e ꞉ X ≃ Y , ((x y : X) → ⌜ e ⌝ (x ·X y) ＝ (⌜ e ⌝ x ·Y ⌜ e ⌝ y)))  ■
 where
  I = id-equiv-edge (Magma-hSet-unbiased-lens-univalent-total 𝓤 ua fe) 𝓧 𝓨
  II = Σ-change-of-variable-≃ _
        (≃-sym (id-equiv-edge {!hSet-univalent-refl-graph ua fe fe !}
         (X , X-is-set) (Y , Y-is-set)))
  III = Σ-change-of-variable-≃ _ {!hSet-＝-char!}

\end{code}
