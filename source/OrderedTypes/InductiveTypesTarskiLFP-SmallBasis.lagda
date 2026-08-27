Ian Ray. August 20 2026.

TODO. Remove unused imports.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons
open import UF.Size

module OrderedTypes.InductiveTypesTarskiLFP-SmallBasis
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : Prop-Ext)
        (pr : Propositional-resizing)
       where

private
 fe' : FunExt
 fe' 𝓤 𝓥 = fe {𝓤} {𝓥}

open import MLTT.Spartan
open import UF.Base
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.Logic
open import UF.Powerset-MultiUniverse
open import UF.Sets
open import UF.Sets-Properties
open import UF.Subsingletons-FunExt
open import UF.Subsingletons-Properties
open import UF.SubtypeClassifier
open import OrderedTypes.InfLattice fe pt
 hiding (⟨_⟩ ; is-monotone-endomap ; order-of ; antisymmetry-of ;
         transitivity-of)
open import OrderedTypes.SupLattice pt fe
open import OrderedTypes.SupLattice-SmallBasis pt fe
open import OrderedTypes.InfLattice fe pt
 hiding (⟨_⟩ ; order-of ; is-monotone-endomap)

open AllCombinators pt fe
open PropositionalTruncation pt hiding (_∨_)
open import Locales.Frame pt fe hiding (⟨_⟩ ; join-of)

open import Slice.Family
open import OrderedTypes.PredicativeLFP pt fe pe

\end{code}

We postulate the following infinite set.

\begin{code}

record weak-infinity (𝓤 : Universe) : 𝓤 ⁺ ̇
 where
 field
  Infty : 𝓤 ̇
  Infty-is-set : is-set Infty
  el-Infty : Infty
  map-Infty : Infty → Infty
  map-inj : (x y : Infty) → map-Infty x ＝ map-Infty y → x ＝ y
  el-not-img : (x : Infty) → ¬ (map-Infty x ＝ el-Infty)
  
\end{code}

We want to be able to have TarskiLFP-SmallBasis as a general assumption.

\begin{code}

module _ (L : Sup-Lattice 𝓤 𝓦 𝓥) {B : 𝓥 ̇}
         (β : B → ⟨ L ⟩) (h : is-basis L β)
         (f : ⟨ L ⟩ → ⟨ L ⟩)
         (f-mono : is-monotone-endomap L f)
       where

 has-least-pre-fixed-point : 𝓤 ⊔ 𝓦 ̇
 has-least-pre-fixed-point =
  Σ p ꞉ ⟨ L ⟩ , ((f p ≤⟨ L ⟩ p) holds)
              × ((a : ⟨ L ⟩) → (f a ≤⟨ L ⟩ a) holds → (p ≤⟨ L ⟩ a) holds)

TarskiLFP-SmallBasis : (𝓤 𝓦 𝓥 : Universe)
                     → (𝓤 ⁺) ⊔ (𝓦 ⁺) ⊔ (𝓥 ⁺) ̇
TarskiLFP-SmallBasis 𝓤 𝓦 𝓥
 = (L : Sup-Lattice 𝓤 𝓦 𝓥) {B : 𝓥 ̇}
   (β : B → ⟨ L ⟩) (h : is-basis L β)
   (f : ⟨ L ⟩ → ⟨ L ⟩)
   (f-mono : is-monotone-endomap L f)
 → has-least-pre-fixed-point L β h f f-mono

\end{code}

First we need to show that the powerset of some given set A is itself a
sup-lattice with small basis.

\begin{code}

module _ (A : 𝓤 ̇) (A-set : is-set A) where

 open unions-of-small-families pt 𝓤 𝓤 A
 open PropositionalSubsetInclusionNotation fe
 open Joins {𝓤 ⁺} {𝓤} {𝓟 {𝓤} A} _⊆ₚ_

 𝓟-sup-lattice : Sup-Lattice (𝓤 ⁺) 𝓤 𝓤
 𝓟-sup-lattice
  = (𝓟 {𝓤} A , (_⊆ₚ_ , sup) , (par-ord , suprema))
  where
   sup : Fam 𝓤 (𝓟 A) → 𝓟 {𝓤} A
   sup (S , s) a = ⋃ s a
   par-ord : is-partial-order (𝓟 A) _⊆ₚ_
   par-ord = ((⊆-refl , ⊆-trans) , subset-extensionality pe fe)
   suprema : (S : Fam 𝓤 (𝓟 {𝓤} A)) → ((sup S) is-lub-of S) holds
   suprema (S , s)
    = (⋃-is-upperbound s , λ (U , O) → ⋃-is-lowerbound-of-upperbounds s U O)

 open singleton-subsets A-set

 basis-char : (S : 𝓟 {𝓤} A)
            → ⋃ (↓ᴮ-inclusion 𝓟-sup-lattice ❴_❵ S) ＝ S
 basis-char S = subset-extensionality pe fe I II
  where
   I : ⋃ (↓ᴮ-inclusion 𝓟-sup-lattice ❴_❵ S) ⊆ S
   I x = ∥∥-rec (holds-is-prop (S x))
          (λ ((a , a∈S) , o) → transport (λ - → - ∈ S) o (a∈S a refl))
   II : S ⊆ ⋃ (↓ᴮ-inclusion 𝓟-sup-lattice ❴_❵ S)
   II x x∈S
    = ∣ ((x , (pr₁ (❴❵-subset-characterization {_} {x} S)) x∈S) , refl) ∣

 ❴❵-is-basis : is-basis 𝓟-sup-lattice ❴_❵
 ❴❵-is-basis
  = record{≤-is-small = λ S a → ((❴ a ❵ ⊆ S) , ≃-refl (❴ a ❵ ⊆ S)) ;
           ↓-is-sup
            = λ S → transport
                     (λ - → (- is-lub-of (↓ᴮ 𝓟-sup-lattice ❴_❵ S
                                   , ↓ᴮ-inclusion 𝓟-sup-lattice ❴_❵ S)) holds)
                     (basis-char S)
                     (⋃-is-upperbound (↓ᴮ-inclusion 𝓟-sup-lattice ❴_❵ S)
                      , λ (U , O) → ⋃-is-lowerbound-of-upperbounds
                                    (↓ᴮ-inclusion 𝓟-sup-lattice ❴_❵ S) U O) }

\end{code}

We now define a monotone map that is going to encode the constructors of the
natural numbers.

\begin{code}

module _ (wi : weak-infinity 𝓤) (lfp : TarskiLFP-SmallBasis (𝓤 ⁺) 𝓤 𝓤) where

 open weak-infinity wi

 nat-constr : 𝓟 {𝓤} Infty → 𝓟 {𝓤} Infty
 nat-constr S x
  = ((x ＝ el-Infty) , Infty-is-set) ∨
    ((∃ a ꞉ Infty , a ∈ S × (x ＝ map-Infty a)) , ∃-is-prop)

 nat-constr-monotone : (S T : 𝓟 {𝓤} Infty)
                      → S ⊆ T
                      → nat-constr S ⊆ nat-constr T
 nat-constr-monotone S T S⊆T x
  = ∥∥-rec (holds-is-prop (nat-constr T x)) I
  where
   I : (x ＝ el-Infty) + (∃ a ꞉ Infty , a ∈ S × (x ＝ map-Infty a))
     → nat-constr T x holds
   I (inl x＝el-Infty) = ∣ inl x＝el-Infty ∣
   I (inr x∈S) = ∣ inr (II x∈S) ∣
    where 
     II : ∃ a ꞉ Infty , a ∈ S × (x ＝ map-Infty a)
        → ∃ a ꞉ Infty , a ∈ T × (x ＝ map-Infty a)
     II = ∥∥-rec ∥∥-is-prop
           (λ (a , a∈S , x＝mapa) → ∣ (a , S⊆T a a∈S , x＝mapa) ∣)

\end{code}

Now we consider the least fixed point of nat-constr.

\begin{code}

 nat-has-lfp : has-least-pre-fixed-point (𝓟-sup-lattice Infty Infty-is-set)
                                         singleton-subsets.❴ Infty-is-set ❵
                                         (❴❵-is-basis Infty Infty-is-set)
                                         nat-constr nat-constr-monotone
 nat-has-lfp = lfp (𝓟-sup-lattice Infty Infty-is-set)
                   singleton-subsets.❴ Infty-is-set ❵
                   (❴❵-is-basis Infty Infty-is-set)
                   nat-constr nat-constr-monotone

 nat-constr-lfp : 𝓟 {𝓤} Infty
 nat-constr-lfp = pr₁ (nat-has-lfp)

 nat-constr-pre-fixed : nat-constr nat-constr-lfp ⊆ nat-constr-lfp
 nat-constr-pre-fixed = pr₁ (pr₂ nat-has-lfp)

 el-Infty∈nat-constr-lfp : el-Infty ∈ nat-constr-lfp
 el-Infty∈nat-constr-lfp = nat-constr-pre-fixed el-Infty ∣ inl refl ∣

 map-Infty-closed-constr-lfp : (x : Infty)
                             → x ∈ nat-constr-lfp
                             → map-Infty x ∈ nat-constr-lfp
 map-Infty-closed-constr-lfp x x∈
  = nat-constr-pre-fixed (map-Infty x) ∣ inr ∣ x , x∈ , refl ∣ ∣

 nat-constr-least : (S : 𝓟 {𝓤} Infty)
                  → nat-constr S ⊆ S
                  → nat-constr-lfp ⊆ S
 nat-constr-least = pr₂ (pr₂ nat-has-lfp)

 nat-constr-nat-lfp-pre-fixed
  : nat-constr (nat-constr nat-constr-lfp) ⊆ nat-constr nat-constr-lfp
 nat-constr-nat-lfp-pre-fixed
  = nat-constr-monotone (nat-constr nat-constr-lfp) nat-constr-lfp
     nat-constr-pre-fixed

 nat-constr-post-fixed : nat-constr-lfp ⊆ nat-constr nat-constr-lfp
 nat-constr-post-fixed = nat-constr-least (nat-constr nat-constr-lfp)
                              nat-constr-nat-lfp-pre-fixed

 nat-constr-lfp-fixed : nat-constr nat-constr-lfp ＝ nat-constr-lfp
 nat-constr-lfp-fixed
  = subset-extensionality pe fe nat-constr-pre-fixed nat-constr-post-fixed

\end{code}

TODO: See if anything below can be refactored using the post-fixed and fixed
from above.

We can now define the type of natural numbers and some properties.

\begin{code}

 ℕ-lfp : 𝓤 ̇
 ℕ-lfp = 𝕋 nat-constr-lfp

 ℕ-is-set-lfp : is-set ℕ-lfp
 ℕ-is-set-lfp = Σ-is-set Infty-is-set
                 (λ - → props-are-sets (holds-is-prop (nat-constr-lfp -)))

 zero-lfp : ℕ-lfp
 zero-lfp = (el-Infty , el-Infty∈nat-constr-lfp)

 suc-lfp : ℕ-lfp → ℕ-lfp
 suc-lfp (x , x∈lfp) = (map-Infty x , map-Infty-closed-constr-lfp x x∈lfp)

 suc-inj-lfp : (x y : ℕ-lfp)
             → suc-lfp x ＝ suc-lfp y
             → x ＝ y
 suc-inj-lfp (x , _) (y , _) sucx＝sucy
  = to-subtype-＝ (holds-is-prop ∘ nat-constr-lfp)
                  (map-inj x y (ap pr₁ sucx＝sucy))

 zero-not-img-lfp : (x : ℕ-lfp) → ¬ (suc-lfp x ＝ zero-lfp)
 zero-not-img-lfp (x , _) sucx＝zero = el-not-img x (ap pr₁ sucx＝zero)

\end{code}

We now work towards an induction principle for ℕ-lfp. First we define a
canonical subset of Infty from a subset of ℕ-lfp and prove some properties
about it.

\begin{code}

 canonical-subset-Infty : 𝓟 {𝓤} ℕ-lfp → 𝓟 {𝓤} Infty
 canonical-subset-Infty S i
  = ((∃ p ꞉ i ∈ nat-constr-lfp , (S (i , p) holds)) , ∃-is-prop)

 canonical-subset-contains-subset : (P : ℕ-lfp → Ω 𝓤)
                                  → ((x , p) : ℕ-lfp)
                                  → (x , p) ∈ P
                                  → x ∈ canonical-subset-Infty P
 canonical-subset-contains-subset P (x , p) n∈ = ∣ p , n∈ ∣

 subset-contains-canonical-subset : (P : ℕ-lfp → Ω 𝓤)
                                  → ((x , p) : ℕ-lfp)
                                  → x ∈ canonical-subset-Infty P 
                                  → (x , p) ∈ P
 subset-contains-canonical-subset P (x , p)
  = ∥∥-rec (holds-is-prop (P (x , p)))
           (λ (p' , Pxp') → transport (_∈ P)
           (to-subtype-＝ (holds-is-prop ∘ nat-constr-lfp) refl) Pxp')

 canonical-subset-zero : (S : 𝓟 {𝓤} ℕ-lfp)
                       → zero-lfp ∈ S
                       → el-Infty ∈ canonical-subset-Infty S
 canonical-subset-zero S S-zero = ∣ el-Infty∈nat-constr-lfp , S-zero ∣

 canonical-subset-suc : (S : 𝓟 {𝓤} ℕ-lfp)
                      → ((x : ℕ-lfp) → x ∈ S → (suc-lfp x) ∈ S)
                      → (x : Infty)
                      → x ∈ canonical-subset-Infty S
                      → (map-Infty x) ∈ canonical-subset-Infty S
 canonical-subset-suc S S-suc x 
  = ∥∥-rec ∥∥-is-prop
     (λ (p , Sp-holds)
       → ∣ map-Infty-closed-constr-lfp x p , S-suc (x , p) Sp-holds ∣)

 canonical-subset-Infty-pre-fixed
  : (S : 𝓟 {𝓤} ℕ-lfp)
  → zero-lfp ∈ S
  → ((x : ℕ-lfp) → x ∈ S → (suc-lfp x) ∈ S)
  → nat-constr (canonical-subset-Infty S) ⊆ canonical-subset-Infty S
 canonical-subset-Infty-pre-fixed S S-z S-s x
  = ∥∥-rec ∥∥-is-prop I
  where
   I : (x ＝ el-Infty)
     + (∃ a ꞉ Infty , a ∈ canonical-subset-Infty S × (x ＝ map-Infty a))
     → x ∈ canonical-subset-Infty S
   I (inl x＝el-Infty) = transport (_∈ canonical-subset-Infty S)
                          (x＝el-Infty ⁻¹)
                          (canonical-subset-zero S S-z)
   I (inr ∃a∈canS) = II ∃a∈canS
    where
     II : ∃ a ꞉ Infty , a ∈ canonical-subset-Infty S × (x ＝ map-Infty a)
        → x ∈ canonical-subset-Infty S
     II = ∥∥-rec ∥∥-is-prop
           (λ (a , a∈ , x＝mapa) → transport (_∈ canonical-subset-Infty S)
                                    (x＝mapa ⁻¹)
                                    (canonical-subset-suc S S-s a a∈))

 canonical-subset-Infty-contains-nat-constr-lfp
  : (S : 𝓟 {𝓤} ℕ-lfp)
  → zero-lfp ∈ S
  → ((x : ℕ-lfp) → x ∈ S → (suc-lfp x) ∈ S)
  → nat-constr-lfp ⊆ canonical-subset-Infty S
 canonical-subset-Infty-contains-nat-constr-lfp S S-z S-s
  = nat-constr-least (canonical-subset-Infty S)
     (canonical-subset-Infty-pre-fixed S S-z S-s)
            
\end{code}

Now we use the previous results to define prop-valued induction for ℕ-lfp.
We then prove canonical froms for ℕ-lfp.

\begin{code}

 ℕ-prop-induction-lfp : (P : ℕ-lfp → Ω 𝓤)
                      → (zero-lfp) ∈ P
                      → ((n : ℕ-lfp) → n ∈ P → (suc-lfp n) ∈ P)
                      → (n : ℕ-lfp) → n ∈ P
 ℕ-prop-induction-lfp P P-zero P-suc (x , x∈)
  = subset-contains-canonical-subset P (x , x∈)
     (canonical-subset-Infty-contains-nat-constr-lfp P P-zero P-suc x x∈)

 is-canonical : (n : ℕ-lfp) → 𝓤 ̇
 is-canonical n
  = (((n ＝ zero-lfp) , ℕ-is-set-lfp) ∨
     ((∃ m ꞉ ℕ-lfp , n ＝ suc-lfp m) , ∃-is-prop)) holds

 is-canonical-prop : (n : ℕ-lfp) → is-prop (is-canonical n)
 is-canonical-prop n = ∥∥-is-prop

 ℕ-canonical-forms-lfp
  : (n : ℕ-lfp)
  → is-canonical n
 ℕ-canonical-forms-lfp n@(x , x∈)
  = ℕ-prop-induction-lfp (λ - → is-canonical - , is-canonical-prop -)
     ∣ inl refl ∣ (λ x x∈can → ∣ inr ∣ x , refl ∣ ∣) n

\end{code}

TODO: Canonical forms should also follow from the fact that nat-constr-lfp is
post-fixed.

We now give a recursion principle for ℕ-lfp. The idea is to define the graph of
the to be defined recursive function as a least pre-fixed point.

\begin{code}

 module _ (X : 𝓤 ̇) (X-set : is-set X) (x₀ : X) (s : X → X) where

  ℕ-lfp×A-is-set : is-set (ℕ-lfp × X)
  ℕ-lfp×A-is-set = ×-is-set ℕ-is-set-lfp X-set

  graph-constr : 𝓟 {𝓤} (ℕ-lfp × X) → 𝓟 {𝓤} (ℕ-lfp × X)
  graph-constr S (n , x)
   = (((n ＝ zero-lfp) , ℕ-is-set-lfp) ∧ ((x ＝ x₀) , X-set)) ∨
     ((∃ m ꞉ ℕ-lfp , Σ x' ꞉ X , (m , x') ∈ S
      × (n ＝ suc-lfp m) × (x ＝ s x')) , ∃-is-prop)

  graph-constr-monotone : (S R : 𝓟 {𝓤} (ℕ-lfp × X))
                        → S ⊆ R
                        → graph-constr S ⊆ graph-constr R
  graph-constr-monotone S R S⊆R (n , x)
   = ∥∥-rec ∥∥-is-prop I
   where
    I : ((n ＝ zero-lfp) × (x ＝ x₀)) +
        (∃ m ꞉ ℕ-lfp , Σ x' ꞉ X , (m , x') ∈ S
          × (n ＝ suc-lfp m) × (x ＝ s x'))
      → graph-constr R (n , x) holds
    I (inl nx＝zerox₀) = ∣ inl nx＝zerox₀ ∣
    I (inr ∃mx'∈S)
     = ∥∥-rec ∥∥-is-prop
        (λ (m , x' , ∈S , n＝sucm , x＝sx')
           → ∣ inr ∣ m , x' , S⊆R (m , x') ∈S , n＝sucm , x＝sx' ∣ ∣)
        ∃mx'∈S

  graph-has-lfp : has-least-pre-fixed-point
                   (𝓟-sup-lattice (ℕ-lfp × X) ℕ-lfp×A-is-set)
                   singleton-subsets.❴ ℕ-lfp×A-is-set ❵
                   (❴❵-is-basis (ℕ-lfp × X) ℕ-lfp×A-is-set)
                   graph-constr graph-constr-monotone 
  graph-has-lfp = lfp (𝓟-sup-lattice (ℕ-lfp × X) ℕ-lfp×A-is-set)
                      singleton-subsets.❴ ℕ-lfp×A-is-set ❵
                      (❴❵-is-basis (ℕ-lfp × X) ℕ-lfp×A-is-set)
                      graph-constr graph-constr-monotone

  graph-lfp : 𝓟 {𝓤} (ℕ-lfp × X)
  graph-lfp = pr₁ graph-has-lfp

  graph-pre-fixed : graph-constr graph-lfp ⊆ graph-lfp
  graph-pre-fixed = pr₁ (pr₂ graph-has-lfp)

  x₀∈graph-lfp : (zero-lfp , x₀) ∈ graph-lfp
  x₀∈graph-lfp = graph-pre-fixed (zero-lfp , x₀) ∣ inl (refl , refl) ∣

  suc∈graph-lfp : (n : ℕ-lfp) (x : X)
                → (n , x) ∈ graph-lfp
                → (suc-lfp n , s x) ∈ graph-lfp
  suc∈graph-lfp n x nx∈
   = graph-pre-fixed (suc-lfp n , s x) ∣ inr ∣ n , x , nx∈ , refl , refl ∣ ∣

  graph-least : (S : 𝓟 {𝓤} (ℕ-lfp × X))
              → graph-constr S ⊆ S
              → graph-lfp ⊆ S
  graph-least = pr₂ (pr₂ graph-has-lfp)

\end{code}

We now start proving some lemmas about graph-lfp which will prove useful.

\begin{code}

  canonical-graph-subset : 𝓟 {𝓤} (ℕ-lfp × X)
  canonical-graph-subset = graph-constr graph-lfp

  x₀∈canonical-graph-subset : (zero-lfp , x₀) ∈ canonical-graph-subset
  x₀∈canonical-graph-subset = ∣ inl (refl , refl) ∣

  suc∈canonical-graph-subset : ((n , x) : ℕ-lfp × X)
                             → (n , x) ∈ canonical-graph-subset
                             → (suc-lfp n , s x) ∈ canonical-graph-subset
  suc∈canonical-graph-subset (n , x)
   = ∥∥-rec ∥∥-is-prop I
   where
    I : ((n ＝ zero-lfp) × (x ＝ x₀)) +
        ((∃ m ꞉ ℕ-lfp , Σ x' ꞉ X , (m , x') ∈ graph-lfp
                     × (n ＝ suc-lfp m) × (x ＝ s (x'))))
      → (suc-lfp n , s x) ∈ canonical-graph-subset
    I (inl (n＝z , x＝x₀))
     = ∣ inr ∣ (zero-lfp , x₀ , x₀∈graph-lfp , ap suc-lfp n＝z , ap s x＝x₀) ∣ ∣
    I (inr ∃mx')
     = ∥∥-rec ∥∥-is-prop
        (λ (m , x' , mx'∈graphlfp , n＝sucm , x＝sx')
         → ∣ inr ∣ (suc-lfp m , s x' , suc∈graph-lfp m x' mx'∈graphlfp
                    , ap suc-lfp n＝sucm , ap s x＝sx') ∣ ∣)
        ∃mx'
        
  graph-constr-can⊆canonical-graph-subset
   : graph-constr canonical-graph-subset ⊆ canonical-graph-subset
  graph-constr-can⊆canonical-graph-subset 
   = graph-constr-monotone canonical-graph-subset graph-lfp graph-pre-fixed 

  graph-canonical-forms
   : graph-lfp ⊆ canonical-graph-subset
  graph-canonical-forms 
   = graph-least canonical-graph-subset graph-constr-can⊆canonical-graph-subset 

  graph-lfp＝canonical-graph-subset : graph-lfp ＝ canonical-graph-subset
  graph-lfp＝canonical-graph-subset
   = subset-extensionality pe fe graph-canonical-forms
      graph-pre-fixed

  x₀-unique : (x : X)
            → (zero-lfp , x) ∈ graph-lfp
            → x₀ ＝ x
  x₀-unique x zx∈graph-lfp
   = I (graph-canonical-forms (zero-lfp , x) zx∈graph-lfp)
   where
    I : (zero-lfp , x) ∈ canonical-graph-subset
      → x₀ ＝ x
    I = ∥∥-rec X-set II
     where
      II : ((zero-lfp ＝ zero-lfp) × (x ＝ x₀)) +
           (∃ m ꞉ ℕ-lfp , Σ x' ꞉ X , (m , x') ∈ graph-lfp 
                          × (zero-lfp ＝ suc-lfp m) × (x ＝ s (x')))
         → x₀ ＝ x
      II (inl (_ , x＝x₀)) = x＝x₀ ⁻¹
      II (inr ∃mx')
       = ∥∥-rec X-set
          (λ (m , _ , _ , zero＝sucm , _)
           → 𝟘-elim (zero-not-img-lfp m (zero＝sucm ⁻¹)))
          ∃mx'

  X-unique : (n : ℕ-lfp) (x y : X)
           → (n , x) ∈ graph-lfp
           → (n , y) ∈ graph-lfp
           → x ＝ y
  X-unique 
   = ℕ-prop-induction-lfp (λ - → ((x y : X)
                               → (- , x) ∈ graph-lfp
                               → (- , y) ∈ graph-lfp
                               → x ＝ y) , Π₄-is-prop fe (λ _ _ _ _ → X-set))
                          (λ x y x∈ y∈ → x₀-unique x x∈ ⁻¹ ∙ x₀-unique y y∈)
                          I
   where
    I : (n : ℕ-lfp) 
      → ((x y : X)
       → (n , x) ∈ graph-lfp → (n , y) ∈ graph-lfp → x ＝ y)
      → (x y : X)
      → (suc-lfp n , x) ∈ graph-lfp
      → (suc-lfp n , y) ∈ graph-lfp
      → x ＝ y
    I n IH x y sucnx∈ sucny∈
     = II (graph-canonical-forms (suc-lfp n , x) sucnx∈)
          (graph-canonical-forms (suc-lfp n , y) sucny∈)
     where
      II : (suc-lfp n , x) ∈ canonical-graph-subset
         → (suc-lfp n , y) ∈ canonical-graph-subset
         → x ＝ y
      II = ∥∥-rec₂ X-set III
       where
        III : ((suc-lfp n ＝ zero-lfp) × (x ＝ x₀)) +
              (∃ m ꞉ ℕ-lfp , Σ x' ꞉ X , (m , x') ∈ graph-lfp
                           × (suc-lfp n ＝ suc-lfp m) × (x ＝ s x'))
            → ((suc-lfp n ＝ zero-lfp) × (y ＝ x₀)) +
              (∃ m' ꞉ ℕ-lfp , Σ x'' ꞉ X , (m' , x'') ∈ graph-lfp
                           × (suc-lfp n ＝ suc-lfp m') × (y ＝ s x''))
            → x ＝ y
        III (inl (sucn＝zero , _)) _ = 𝟘-elim (zero-not-img-lfp n sucn＝zero)
        III (inr _) (inl (sucn＝zero , _))
         = 𝟘-elim (zero-not-img-lfp n sucn＝zero)
        III (inr ∃mx'∈) (inr ∃m'x''∈) = ∥∥-rec₂ X-set IV ∃mx'∈ ∃m'x''∈
         where
          IV : Σ m ꞉ ℕ-lfp , Σ x' ꞉ X , (m , x') ∈ graph-lfp
                           × (suc-lfp n ＝ suc-lfp m) × (x ＝ s x')
             → Σ m' ꞉ ℕ-lfp , Σ x'' ꞉ X , (m' , x'') ∈ graph-lfp
                           × (suc-lfp n ＝ suc-lfp m') × (y ＝ s x'')
             → x ＝ y
          IV (m , x' , mx'∈ , sucn＝sucm , x＝sx')
             (m' , x'' , m'x''∈ , sucn＝sucm' , y＝sx'')
           = x       ＝⟨ x＝sx' ⟩
             s x'    ＝⟨ ap s (IH x' x'' nx'∈ nx''∈) ⟩
             s x''   ＝⟨ y＝sx'' ⁻¹ ⟩
             y       ∎
           where
            m＝n : m ＝ n
            m＝n = suc-inj-lfp m n (sucn＝sucm ⁻¹)
            m'＝n : m' ＝ n
            m'＝n = suc-inj-lfp m' n (sucn＝sucm' ⁻¹)
            nx'∈ : (n , x') ∈ graph-lfp
            nx'∈ = transport (λ - → (- , x') ∈ graph-lfp) m＝n mx'∈
            nx''∈ : (n , x'') ∈ graph-lfp
            nx''∈ = transport (λ - → (- , x'') ∈ graph-lfp) m'＝n m'x''∈
                                     
\end{code}

We now define a subset on ℕ-lfp that says the above relation is functional
and prove it by prop induction on ℕ-lfp.

\begin{code}

  functional-rel : 𝓟 {𝓤} (ℕ-lfp)
  functional-rel n
   = ((∃! x ꞉ X , (n , x) ∈ graph-lfp) , being-singleton-is-prop fe)

  rec-functional-rel : (n : ℕ-lfp)
                     → n ∈ functional-rel
  rec-functional-rel
   = ℕ-prop-induction-lfp functional-rel
      ((x₀ , x₀∈graph-lfp) , (λ (x' , zx'∈)
        → to-subtype-＝ (λ - → holds-is-prop (graph-lfp (zero-lfp , -)))
           (x₀-unique x' zx'∈)))
      (λ n ((x , nx∈) , nx-sing) → ((s x , suc∈graph-lfp n x nx∈) ,
        (λ (y , sucny∈)
         → to-subtype-＝ (λ - → holds-is-prop (graph-lfp (suc-lfp n , -)))
            (X-unique (suc-lfp n) (s x) y (suc∈graph-lfp n x nx∈) sucny∈))))

  recursive-graph : (n : ℕ-lfp)
                  → Σ x ꞉ X , (n , x) ∈ graph-lfp
  recursive-graph n = pr₁ (rec-functional-rel n)

  recursive-function : ℕ-lfp → X
  recursive-function n = pr₁ (recursive-graph n)

  recursive-function∈graph-lfp : (n : ℕ-lfp)
                               → (n , recursive-function n) ∈ graph-lfp
  recursive-function∈graph-lfp n = pr₂ (recursive-graph n)

  recursive-function-functional : (n : ℕ-lfp)
                                → (p : (Σ x ꞉ X , (n , x) ∈ graph-lfp))
                                → recursive-graph n ＝ p
  recursive-function-functional n = pr₂ (rec-functional-rel n)

  rec-comp-zero : recursive-function zero-lfp ＝ x₀
  rec-comp-zero
   = x₀-unique (recursive-function zero-lfp)
      (recursive-function∈graph-lfp zero-lfp) ⁻¹

  rec-comp-suc : (n : ℕ-lfp)
               → recursive-function (suc-lfp n) ＝ s (recursive-function n)
  rec-comp-suc n
   = X-unique (suc-lfp n) (recursive-function (suc-lfp n))
       (s (recursive-function n))
       (recursive-function∈graph-lfp (suc-lfp n))
       (suc∈graph-lfp n (recursive-function n)
         (recursive-function∈graph-lfp n))

\end{code}

We now state the recursion principle outside of the previous module.

\begin{code}

 ℕ-recursion-lfp : (X : 𝓤 ̇) 
                 → is-set X
                 → X
                 → (X → X)
                 → ℕ-lfp → X
 ℕ-recursion-lfp = recursive-function

 ℕ-recursion-comp-zero-lfp
  : (X : 𝓤 ̇) (X-set : is-set X) (x₀ : X) (s : X → X)
  → ℕ-recursion-lfp X X-set x₀ s zero-lfp ＝ x₀
 ℕ-recursion-comp-zero-lfp = rec-comp-zero

 ℕ-recursion-comp-suc-lfp
  : (X : 𝓤 ̇) (X-set : is-set X) (x₀ : X) (s : X → X)
  → (n : ℕ-lfp)
  → ℕ-recursion-lfp X X-set x₀ s (suc-lfp n)
  ＝ s (ℕ-recursion-lfp X X-set x₀ s n)
 ℕ-recursion-comp-suc-lfp = rec-comp-suc

\end{code}

TODO. Usual construction of induction from recursion.

\begin{code}

 module _ (X : ℕ-lfp → 𝓤 ̇) (X-set : (n : ℕ-lfp) → is-set (X n))
          (X-zero : X zero-lfp) (X-suc : (n : ℕ-lfp) → X n → X (suc-lfp n))
        where

  recursion-total-space : ℕ-lfp → Σ n ꞉ ℕ-lfp , X n
  recursion-total-space 
   = ℕ-recursion-lfp (Σ n ꞉ ℕ-lfp , X n) (Σ-is-set ℕ-is-set-lfp X-set)
      (zero-lfp , X-zero) (λ (n , Xn) → (suc-lfp n , X-suc n Xn))

  recursion-total-space-zero
   : recursion-total-space zero-lfp ＝ (zero-lfp , X-zero)
  recursion-total-space-zero
   = ℕ-recursion-comp-zero-lfp (Σ n ꞉ ℕ-lfp , X n) (Σ-is-set ℕ-is-set-lfp X-set)
      (zero-lfp , X-zero) (λ (n , Xn) → (suc-lfp n , X-suc n Xn))

 ℕ-induction-lfp : (X : ℕ-lfp → 𝓤 ̇)
                 → ((n : ℕ-lfp) → is-set (X n))
                 → X zero-lfp
                 → ((n : ℕ-lfp) → X n → X (suc-lfp n))
                 → (n : ℕ-lfp) → X n
 ℕ-induction-lfp X X-set X-zero X-suc
  = {!!}

