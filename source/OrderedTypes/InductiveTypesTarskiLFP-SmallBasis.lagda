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
open import UF.Subsingletons-FunExt
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

We start by postulating the following infinite set...

this record is subject to change...

We may need some injectivity stuff...

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

We want to construct the natural numbers from weak-infinity and
TarskiLFP-SmallBasis.

\begin{code}

module _ (L : Sup-Lattice 𝓤 𝓦 𝓥) {B : 𝓥 ̇}
         (β : B → ⟨ L ⟩) (h : is-basis L β)
         (f : ⟨ L ⟩ → ⟨ L ⟩)
         (f-mono : is-monotone-endomap L f)
       where

 TarskiLFP-SmallBasis : 𝓤 ⊔ 𝓦 ̇
 TarskiLFP-SmallBasis = has-least-fixed-point L f

\end{code}

First we need to show that the powerset of some given set A is itself a
sup-lattice with small basis.

\begin{code}

module _ (A : 𝓤 ̇) (A-set : is-set A) where

 open unions-of-small-families pt 𝓤 𝓤 A
 open PropositionalSubsetInclusionNotation fe
 open Joins {𝓤 ⁺} {𝓤} {𝓟 {𝓤} A} _⊆ₚ_

 𝓟A-sup-lattice : Sup-Lattice (𝓤 ⁺) 𝓤 𝓤
 𝓟A-sup-lattice
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
            → ⋃ (↓ᴮ-inclusion 𝓟A-sup-lattice ❴_❵ S) ＝ S
 basis-char S = subset-extensionality pe fe I II
  where
   I : ⋃ (↓ᴮ-inclusion 𝓟A-sup-lattice ❴_❵ S) ⊆ S
   I x = ∥∥-rec (holds-is-prop (S x))
          (λ ((a , a∈S) , o) → transport (λ - → - ∈ S) o (a∈S a refl))
   II : S ⊆ ⋃ (↓ᴮ-inclusion 𝓟A-sup-lattice ❴_❵ S)
   II x x∈S
    = ∣ ((x , (pr₁ (❴❵-subset-characterization {_} {x} S)) x∈S) , refl) ∣

 ❴❵-is-basis : is-basis 𝓟A-sup-lattice ❴_❵
 ❴❵-is-basis
  = record{≤-is-small = λ S a → ((❴ a ❵ ⊆ S) , ≃-refl (❴ a ❵ ⊆ S)) ;
           ↓-is-sup
            = λ S → transport
                     (λ - → (- is-lub-of (↓ᴮ 𝓟A-sup-lattice ❴_❵ S
                                   , ↓ᴮ-inclusion 𝓟A-sup-lattice ❴_❵ S)) holds)
                     (basis-char S)
                     (⋃-is-upperbound (↓ᴮ-inclusion 𝓟A-sup-lattice ❴_❵ S)
                      , λ (U , O) → ⋃-is-lowerbound-of-upperbounds
                                    (↓ᴮ-inclusion 𝓟A-sup-lattice ❴_❵ S) U O) }

\end{code}

We now define a monotone map that is going to encode the constructors of the
natural numbers.

\begin{code}

module _ (wi : weak-infinity 𝓤) where

 open weak-infinity wi
 open singleton-subsets Infty-is-set
 open binary-unions-of-subsets pt

 nat-constr : 𝓟 {𝓤} Infty → 𝓟 {𝓤} Infty
 nat-constr S x
  = ((x ＝ el-Infty) , Infty-is-set)
  ∨ ((∃ a ꞉ Infty , a ∈ S × (x ＝ map-Infty a)) , ∃-is-prop)

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
     II = ∥∥-rec
           (holds-is-prop
            ((∃ a ꞉ Infty , a ∈ T × (x ＝ map-Infty a)) , ∃-is-prop))
           (λ (a , a∈S , x＝mapa) → ∣ (a , S⊆T a a∈S , x＝mapa) ∣)

\end{code}

Now we consider the least fixed point of nat-constr.

\begin{code}

 module _ (lfp : TarskiLFP-SmallBasis (𝓟A-sup-lattice Infty Infty-is-set)
                                      ❴_❵ (❴❵-is-basis Infty Infty-is-set)
                                      nat-constr nat-constr-monotone)
        where

  nat-constr-lfp : 𝓟 {𝓤} Infty
  nat-constr-lfp = pr₁ lfp

  nat-constr-fixed : nat-constr nat-constr-lfp ＝ nat-constr-lfp
  nat-constr-fixed = pr₁ (pr₂ lfp)

  nat-constr-lfp→lfp : nat-constr nat-constr-lfp ⊆ nat-constr-lfp
  nat-constr-lfp→lfp x x∈ = transport (λ - → x ∈ -) nat-constr-fixed x∈

  lfp→nat-constr-lfp : nat-constr-lfp ⊆ nat-constr nat-constr-lfp
  lfp→nat-constr-lfp x x∈ = transport⁻¹ (λ - → x ∈ -) nat-constr-fixed x∈

  el-Infty∈nat-constr-lfp : el-Infty ∈ nat-constr-lfp
  el-Infty∈nat-constr-lfp = nat-constr-lfp→lfp el-Infty ∣ inl refl ∣

  map-Infty-closed-constr-lfp : (x : Infty)
                              → x ∈ nat-constr-lfp
                              → map-Infty x ∈ nat-constr-lfp
  map-Infty-closed-constr-lfp x x∈
   = nat-constr-lfp→lfp (map-Infty x) ∣ inr ∣ x , x∈ , refl ∣ ∣

  nat-constr-least : (S : 𝓟 {𝓤} Infty)
                   → nat-constr S ＝ S
                   → nat-constr-lfp ⊆ S
  nat-constr-least = pr₂ (pr₂ lfp)

\end{code}

We can now define the type of natural numbers and some properties.

\begin{code}

  ℕ-lfp : 𝓤 ̇
  ℕ-lfp = 𝕋 nat-constr-lfp

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

We now work towards an induction principle for ℕ-lfp.

\begin{code}

  canonical-subset-Infty : 𝓟 {𝓤} ℕ-lfp → 𝓟 {𝓤} Infty
  canonical-subset-Infty S i
   = ((∃ p ꞉ i ∈ nat-constr-lfp , (S (i , p) holds)) , ∃-is-prop)

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
   = ∥∥-rec (holds-is-prop (canonical-subset-Infty S (map-Infty x)))
            (λ (p , Sp-holds)
              → ∣ map-Infty-closed-constr-lfp x p , S-suc (x , p) Sp-holds ∣)

  canonical-subset-Infty-pre-fixed
   : (S : 𝓟 {𝓤} ℕ-lfp)
   → zero-lfp ∈ S
   → ((x : ℕ-lfp) → x ∈ S → (suc-lfp x) ∈ S)
   → nat-constr (canonical-subset-Infty S) ⊆ canonical-subset-Infty S
  canonical-subset-Infty-pre-fixed S S-z S-s x
   = ∥∥-rec (holds-is-prop (canonical-subset-Infty S x)) III
   where
    III : (x ＝ el-Infty)
        + (∃ a ꞉ Infty , a ∈ canonical-subset-Infty S × (x ＝ map-Infty a))
        → x ∈ canonical-subset-Infty S
    III (inl x＝el-Infty) = transport (_∈ canonical-subset-Infty S)
                             (x＝el-Infty ⁻¹)
                             (canonical-subset-zero S S-z)
    III (inr ∃a∈canS) = IV ∃a∈canS
     where
      IV : ∃ a ꞉ Infty , a ∈ canonical-subset-Infty S × (x ＝ map-Infty a)
         → x ∈ canonical-subset-Infty S
      IV = ∥∥-rec (holds-is-prop (canonical-subset-Infty S x))
            (λ (a , a∈ , x＝mapa) → transport (_∈ canonical-subset-Infty S)
                                     (x＝mapa ⁻¹)
                                     (canonical-subset-suc S S-s a a∈))

  canonical-subset-Infty-post-fixed
   : (S : 𝓟 {𝓤} ℕ-lfp)
   → zero-lfp ∈ S
   → ((x : ℕ-lfp) → x ∈ S → (suc-lfp x) ∈ S)
   → canonical-subset-Infty S ⊆ nat-constr (canonical-subset-Infty S) 
  canonical-subset-Infty-post-fixed S S-z S-s x
   = ∥∥-rec (holds-is-prop (nat-constr (canonical-subset-Infty S) x)) III
   where
    III : Σ p ꞉ x ∈ nat-constr-lfp , S (x , p) holds
        → x ∈ nat-constr (canonical-subset-Infty S)
    III (p , Sxp) = IV (lfp→nat-constr-lfp x p)
     where
      IV : x ∈ nat-constr nat-constr-lfp
         → x ∈ nat-constr (canonical-subset-Infty S)
      IV = ∥∥-rec (holds-is-prop (nat-constr (canonical-subset-Infty S) x)) V
       where
        V : (x ＝ el-Infty)
          + (∃ a ꞉ Infty , a ∈ nat-constr-lfp × (x ＝ map-Infty a))
          → x ∈ nat-constr (canonical-subset-Infty S)
        V (inl x＝el-Infty) = ∣ (inl x＝el-Infty) ∣
        V (inr ∃a∈lfp)
         = ∥∥-rec (holds-is-prop (nat-constr (canonical-subset-Infty S) x))
            VI ∃a∈lfp
         where
          VI : Σ a ꞉ Infty , a ∈ nat-constr-lfp × (x ＝ map-Infty a)
             → x ∈ nat-constr (canonical-subset-Infty S)
          VI (a , a∈ , x＝mapa)
           = ∣ inr ∣ a , ∣ a∈ , {!VII!} ∣ , x＝mapa ∣ ∣
           where
            VII : (suc-lfp (a , a∈)) ∈ S
            VII = transport (_∈ S) (to-subtype-＝
                   (holds-is-prop ∘ nat-constr-lfp) x＝mapa) Sxp

  canonical-subset-Infty-contains-nat-constr-lfp
   : (S : 𝓟 {𝓤} ℕ-lfp)
   → zero-lfp ∈ S
   → ((x : ℕ-lfp) → x ∈ S → (suc-lfp x) ∈ S)
   → nat-constr-lfp ⊆ canonical-subset-Infty S
  canonical-subset-Infty-contains-nat-constr-lfp S S-z S-s
   = nat-constr-least (canonical-subset-Infty S)
      (subset-extensionality pe fe
       (canonical-subset-Infty-pre-fixed S S-z S-s)
       (canonical-subset-Infty-post-fixed S S-z S-s))

  ℕ-prop-induction-lfp : (P : ℕ-lfp → Ω 𝓤)
                       → P (zero-lfp) holds
                       → ((x : ℕ-lfp) → P x holds → P (suc-lfp x) holds)
                       → (x : ℕ-lfp) → P x holds
  ℕ-prop-induction-lfp P P-zero P-suc (x , x∈)
   = {!!}
