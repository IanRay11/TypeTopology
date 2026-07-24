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
open AllCombinators pt fe

\end{code}

We need the following lemma which should be found or added to the library.

\begin{code}

¬¬-props-satisfy-contrapositive : (P : Ω 𝓤) (Q : Ω¬¬ 𝓥)
                                → (¬ (Q holds¬¬) → ¬ (P holds))
                                → P holds → Q holds¬¬
¬¬-props-satisfy-contrapositive P (Q , Q¬¬stable) ¬Q→¬P Pholds
 = Q¬¬stable (λ ¬Qholds → ¬Q→¬P ¬Qholds Pholds)

\end{code}

We inline the definition of inf lattice but should add to the library.

\begin{code}

module Infs {A : 𝓤 ̇ } (_≤_ : A → A → Ω 𝓥) where

 _is-a-lower-bound-of_ : A → Fam 𝓦 A → Ω (𝓥 ⊔ 𝓦)
 l is-a-lower-bound-of (U , u) = Ɐ i ꞉ U , l ≤ u i

 lower-bound : Fam 𝓦 A → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇
 lower-bound U = Σ u ꞉ A , (u is-a-lower-bound-of U) holds

 _is-glb-of_ : A → Fam 𝓦 A → Ω (𝓤 ⊔ 𝓥 ⊔ 𝓦)
 u is-glb-of U = (u is-a-lower-bound-of U)
               ∧ (Ɐ (u′ , _) ꞉ lower-bound U , (u′ ≤ u))

module _ (𝓤 𝓣 𝓥 : Universe) where

 inf-lattice-data : 𝓤 ̇ → 𝓤 ⊔ 𝓣 ⁺ ⊔ 𝓥 ⁺ ̇
 inf-lattice-data A = (A → A → Ω 𝓣) × (Fam 𝓥 A → A)

 is-inf-lattice : {A : 𝓤 ̇ } → inf-lattice-data A → 𝓤 ⊔ 𝓣 ⊔ 𝓥 ⁺ ̇
 is-inf-lattice {A} (_≤_ , ⋀_) = is-partial-order A _≤_ × infima
  where
   open Infs _≤_
   infima : 𝓤 ⊔ 𝓣 ⊔ (𝓥 ⁺) ̇
   infima = (U : Fam 𝓥 A) → ((⋀ U) is-glb-of U) holds

 inf-lattice-structure : 𝓤 ̇ → 𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓣 ⁺ ̇
 inf-lattice-structure A = Σ d ꞉ (inf-lattice-data A) , is-inf-lattice d

 Inf-Lattice : (𝓤 ⊔ 𝓣 ⊔ 𝓥)⁺ ̇
 Inf-Lattice = Σ A ꞉ 𝓤 ̇ , inf-lattice-structure A

⟨_⟩ : Inf-Lattice 𝓤 𝓣 𝓥 → 𝓤 ̇
⟨ (L , _) ⟩ = L

order-of : (L : Inf-Lattice 𝓤 𝓣 𝓥) → (⟨ L ⟩ → ⟨ L ⟩ → Ω 𝓣)
order-of (A , (_≤_ , ⋀_) , rest) = _≤_

syntax order-of L x y = x ≤⟨ L ⟩ y

inf-of : (L : Inf-Lattice 𝓤 𝓣 𝓥) → Fam 𝓥 ⟨ L ⟩ → ⟨ L ⟩
inf-of (A , (_≤_ , ⋀_) , rest) = ⋀_

syntax inf-of L U = ⋀⟨ L ⟩ U

partial-orderedness-of : (L : Inf-Lattice 𝓤 𝓣 𝓥)
                       → is-partial-order ⟨ L ⟩ (order-of L)
partial-orderedness-of (A , (_≤_ , ⋁_) , order , is-glb-of) = order

reflexivity-of : (L : Inf-Lattice 𝓤 𝓣 𝓥) → is-reflexive (order-of L) holds
reflexivity-of L = pr₁ (pr₁ (partial-orderedness-of L))

antisymmetry-of : (L : Inf-Lattice 𝓤 𝓣 𝓥) → is-antisymmetric (order-of L)
antisymmetry-of L = pr₂ (partial-orderedness-of L)

transitivity-of : (L : Inf-Lattice 𝓤 𝓣 𝓥) → is-transitive (order-of L) holds
transitivity-of L = pr₂ (pr₁ (partial-orderedness-of L))

inf-is-glb-of : (L : Inf-Lattice 𝓤 𝓣 𝓥)
               → (U : Fam 𝓥 ⟨ L ⟩)
               → ((order-of L) Infs.is-glb-of inf-of L U) U holds
inf-is-glb-of (A , (_≤_ , ⋁_) , order , infima) = infima

inf-is-lower-bound-of : (L : Inf-Lattice 𝓤 𝓣 𝓥)
                      → (U : Fam 𝓥 ⟨ L ⟩)
                      → ((order-of L) Infs.is-a-lower-bound-of
                          inf-of L U) U holds
inf-is-lower-bound-of L U = pr₁ (inf-is-glb-of L U)

inf-is-greatest-lower-bound-of : (L : Inf-Lattice 𝓤 𝓣 𝓥)
                               → (U : Fam 𝓥 ⟨ L ⟩)
                               → ((u' , _) : Infs.lower-bound (order-of L) U)
                               → (order-of L u' (inf-of L U)) holds
inf-is-greatest-lower-bound-of L U = pr₂ (inf-is-glb-of L U)

sethood-of : (L : Inf-Lattice 𝓤 𝓣 𝓥) → is-set ⟨ L ⟩
sethood-of L =
 type-with-prop-valued-refl-antisym-rel-is-set
  (λ x → λ y → order-of L x y holds)
  (λ x → λ y → holds-is-prop (order-of L x y))
  (λ x → reflexivity-of L x)
  (λ x → λ y → antisymmetry-of L)

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

We show that if coLift P has a minimal element then it is equivalent to P.

\begin{code}

 is-least : coLift 𝓥 P → 𝓤 ⊔ (𝓥 ⁺) ̇
 is-least Q = (Q' : coLift 𝓥 P) → [ Q ] holds¬¬ → [ Q' ] holds¬¬

 least-element-is-≃P : (Q : coLift 𝓥 P)
                     → is-least Q
                     → P holds¬¬ ≃ [ Q ] holds¬¬
 least-element-is-≃P Q is-minQ
  = logically-equivalent-props-are-equivalent
     (holds'-is-prop P) (holds'-is-prop [ Q ])
     (colift-condition Q)
     II
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

module _ where

 is-monotone : (L : Inf-Lattice 𝓤 𝓣 𝓥) (M : Inf-Lattice 𝓤' 𝓣' 𝓥')
             → (f : ⟨ L ⟩ → ⟨ M ⟩)
             → 𝓤 ⊔ 𝓣 ⊔ 𝓣' ̇
 is-monotone L M f = (x y : ⟨ L ⟩)
                   → (x ≤⟨ L ⟩ y) holds
                   → (f x ≤⟨ M ⟩ f y) holds

 is-monotone-endomap : {𝓤 𝓣 𝓥 : Universe}
                     → (L : Inf-Lattice 𝓤 𝓣 𝓥)
                     → (f : ⟨ L ⟩ → ⟨ L ⟩)
                     → 𝓤 ⊔ 𝓣 ̇
 is-monotone-endomap L f = is-monotone L L f

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
  e = ≃-sym (least-element-is-≃P Q (λ Q' → Qleast Q' refl)) 
  
