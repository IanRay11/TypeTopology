\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.FunExt
open import UF.HedbergApplications
open import UF.Logic
open import UF.NotNotStablePropositions
open import UF.PropTrunc
open import UF.Sets
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.SubtypeClassifier
open import UF.Size
open import UF.SmallnessProperties
open import UF.UniverseEmbedding

module OrderedTypes.TarskisLeastFixedPointResizing
        (fe : Fun-Ext)
        (pt : propositional-truncations-exist)
        (pe : Prop-Ext)
      where

open import Slice.Family hiding (_[_])
open import Locales.Frame pt fe hiding (⟨_⟩ ; join-of)
open import OrderedTypes.InfLattice fe pt pe

\end{code}

We start by defining a colift operator on the type of not not stable
propositions.

\begin{code}

module _ (𝓥 : Universe) where

 coLift : Ω¬¬ 𝓤 → (𝓥 ⁺) ⊔ 𝓤 ̇
 coLift P = Σ Q ꞉ Ω¬¬ 𝓥 , (P holds¬¬ → Q holds¬¬)

module coLift-properties {𝓥 : Universe} (P : Ω¬¬ 𝓤) where

 [_] : coLift 𝓥 P → Ω¬¬ 𝓥
 [ (Q , _) ] = Q

 colift-condition : ((Q , Q→P) : coLift 𝓥 P) → P holds¬¬ → Q holds¬¬
 colift-condition (Q , P→Q) = P→Q

\end{code}

We show that coLift P is a inf lattice.

\begin{code}

 coLift-inf-lattice : Inf-Lattice (𝓤 ⊔ (𝓥 ⁺)) 𝓥 𝓥
 coLift-inf-lattice = (coLift 𝓥 P , (I , II) , (III , IV))
  where
   I : coLift 𝓥 P → coLift 𝓥 P → Ω 𝓥
   I Q Q' = (([ Q ] holds¬¬ → [ Q' ] holds¬¬)
             , Π-is-prop fe (λ _ → holds'-is-prop [ Q' ]))
   II : Fam 𝓥 (coLift 𝓥 P) → coLift 𝓥 P
   II (D , f)
    = ((((d : D) → [ f d ] holds¬¬)
      , Π-is-prop fe (λ - → holds'-is-prop [ f - ]))
       , Π-is-¬¬-stable (λ - → holds'-is-¬¬-stable [ f - ]))
        , λ Pholds d → colift-condition (f d) Pholds
   III : is-partial-order (coLift 𝓥 P) (λ Q Q' → I Q Q')
   III = (((λ Q → id) , (λ Q Q' Q'' Q→Q' Q'→Q'' → Q'→Q'' ∘ Q→Q' ))
          , λ {Q} {Q'} Q→Q' Q'→Q → to-subtype-＝
            (λ - → Π-is-prop fe (λ x → holds'-is-prop -))
             (to-subtype-＝ (λ - → being-¬¬-stable-is-prop fe (holds-is-prop -))
              (to-subtype-＝ (λ - → being-prop-is-prop fe)
               (pe (holds'-is-prop [ Q ]) (holds'-is-prop [ Q' ]) Q→Q' Q'→Q))))
   open Infs I
   IV : (U : Fam 𝓥 (coLift 𝓥 P)) → ((II U) is-glb-of U) holds
   IV (D , f) = ((λ d F → F d) , (λ (l , lb) fd-holds d → lb d fd-holds))

\end{code}

TODO. Show that coLift 𝓥 𝟘 ≃ Ω 𝓥 and coLift 𝓥 𝟙 ≃ 𝟙 for intuition.

We show that if coLift P has a least element then it is equivalent to P.

TODO. Maybe it is worth proving the version with minimal rather than least
element.

\begin{code}

 is-least : coLift 𝓥 P → 𝓤 ⊔ (𝓥 ⁺) ̇
 is-least Q = (Q' : coLift 𝓥 P) → [ Q ] holds¬¬ → [ Q' ] holds¬¬

 least-element-is-≃P : (Q : coLift 𝓥 P)
                     → is-least Q
                     → [ Q ] holds¬¬ ≃ P holds¬¬ 
 least-element-is-≃P Q is-minQ
  = logically-equivalent-props-are-equivalent
     (holds'-is-prop [ Q ]) (holds'-is-prop P) II (colift-condition Q)
  where
   𝟘-in-coLift : ¬ (P holds¬¬) → coLift 𝓥 P
   𝟘-in-coLift ¬Pholds
    = ((𝟘 , 𝟘-is-prop) , 𝟘-is-¬¬-stable) , (λ Pholds → 𝟘-elim (¬Pholds Pholds))
   I : ¬ (P holds¬¬) → ¬ ([ Q ] holds¬¬)
   I ¬Pholds Qholds = 𝟘-elim (is-minQ (𝟘-in-coLift ¬Pholds) Qholds)
   II : [ Q ] holds¬¬ → P holds¬¬
   II = ¬¬-props-satisfy-contrapositive (Ω¬¬-to-Ω [ Q ]) P I

\end{code}

We define the relevant version of Tarski's least fixed point theorem here.

\begin{code}

module _ (L : Inf-Lattice 𝓤 𝓣 𝓥) where

 has-least-fixed-point : (f : ⟨ L ⟩ → ⟨ L ⟩) → 𝓤 ⊔ 𝓣 ̇
 has-least-fixed-point f =
  Σ p ꞉ ⟨ L ⟩ , (f p ＝ p) × ((a : ⟨ L ⟩) → (f a ＝ a) → (p ≤⟨ L ⟩ a) holds)

 has-least-fixed-point-is-prop : (f : ⟨ L ⟩ → ⟨ L ⟩)
                               → is-prop (has-least-fixed-point f)
 has-least-fixed-point-is-prop f (p₁ , fp₁ , l₁) (p₂ , fp₂ , l₂) =
  to-subtype-＝ (λ x → ×-is-prop
                       (sethood-of L)
                       (Π-is-prop fe (λ y → Π-is-prop fe
                        (λ _ → holds-is-prop (x ≤⟨ L ⟩ y)))))
                (antisymmetry-of L (l₁ p₂ fp₂) (l₂ p₁ fp₁))

Tarski-Least-Fixed-Point-Inf : (𝓤 𝓦 𝓥 : Universe) → (𝓤 ⊔ 𝓦 ⊔ 𝓥)⁺ ̇
Tarski-Least-Fixed-Point-Inf 𝓤 𝓦 𝓥 = (L : Inf-Lattice 𝓤 𝓦 𝓥)
                                   → (f : ⟨ L ⟩ → ⟨ L ⟩)
                                   → is-monotone-endomap L f
                                   → has-least-fixed-point L f

\end{code}

Now we show that tarski's least fixed point theorem implies a form of
propositional resizing.

\begin{code}

Propositional-Resizing¬¬ : (𝓤 𝓥 : Universe) → (𝓤 ⊔ 𝓥)⁺ ̇
Propositional-Resizing¬¬ 𝓤 𝓥 = (P : Ω¬¬ 𝓤) → (P holds¬¬) is 𝓥 small

Tarski-LFP-implies-Resizing¬¬
 : (𝓤 𝓥 : Universe)
 → Tarski-Least-Fixed-Point-Inf (𝓤 ⊔ (𝓥 ⁺)) 𝓥 𝓥
 → Propositional-Resizing¬¬ 𝓤 𝓥
Tarski-LFP-implies-Resizing¬¬ 𝓤 𝓥 TLFP P = (([ Q ] holds¬¬) , e)
 where
  open coLift-properties P
  LFP : has-least-fixed-point coLift-inf-lattice id
  LFP = TLFP coLift-inf-lattice id (λ x y → id)
  Q : coLift 𝓥 P
  Q = pr₁ LFP
  Qleast = pr₂ (pr₂ LFP)
  e : [ Q ] holds¬¬ ≃ P holds¬¬
  e = least-element-is-≃P Q (λ Q' → Qleast Q' refl)
  
