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

 has-least-pre-fixed-point : (f : ⟨ L ⟩ → ⟨ L ⟩) → 𝓤 ⊔ 𝓦 ̇
 has-least-pre-fixed-point f =
  Σ p ꞉ ⟨ L ⟩ , ((f p ≤⟨ L ⟩ p) holds)
              × ((a : ⟨ L ⟩) → (f a ≤⟨ L ⟩ a) holds → (p ≤⟨ L ⟩ a) holds)

 TarskiLFP-SmallBasis : 𝓤 ⊔ 𝓦 ̇
 TarskiLFP-SmallBasis = has-least-pre-fixed-point f

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

  nat-constr-pre-fixed : nat-constr nat-constr-lfp ⊆ nat-constr-lfp
  nat-constr-pre-fixed = pr₁ (pr₂ lfp)
  
{- artifact of fix-point assumption 
  lfp→nat-constr-lfp : nat-constr-lfp ⊆ nat-constr nat-constr-lfp
  lfp→nat-constr-lfp x x∈ = transport⁻¹ (λ - → x ∈ -) nat-constr-fixed x∈ -}

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
  nat-constr-least = pr₂ (pr₂ lfp)

\end{code}

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
   = ∥∥-rec (holds-is-prop (canonical-subset-Infty S (map-Infty x)))
            (λ (p , Sp-holds)
              → ∣ map-Infty-closed-constr-lfp x p , S-suc (x , p) Sp-holds ∣)

  canonical-subset-Infty-pre-fixed
   : (S : 𝓟 {𝓤} ℕ-lfp)
   → zero-lfp ∈ S
   → ((x : ℕ-lfp) → x ∈ S → (suc-lfp x) ∈ S)
   → nat-constr (canonical-subset-Infty S) ⊆ canonical-subset-Infty S
  canonical-subset-Infty-pre-fixed S S-z S-s x
   = ∥∥-rec (holds-is-prop (canonical-subset-Infty S x)) I
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
      II = ∥∥-rec (holds-is-prop (canonical-subset-Infty S x))
            (λ (a , a∈ , x＝mapa) → transport (_∈ canonical-subset-Infty S)
                                     (x＝mapa ⁻¹)
                                     (canonical-subset-suc S S-s a a∈))

{- artifact of fix-point assumption
  canonical-subset-inversion
   : (S : 𝓟 {𝓤} ℕ-lfp) (x : Infty) 
   → map-Infty x ∈ nat-constr (canonical-subset-Infty S)
   → x ∈ nat-constr (canonical-subset-Infty S)
  canonical-subset-inversion S x
   = ∥∥-rec (holds-is-prop (nat-constr (canonical-subset-Infty S) x)) I
   where
    I : (map-Infty x ＝ el-Infty) +
        (∃ a ꞉ Infty , a ∈ canonical-subset-Infty S
                     × (map-Infty x ＝ map-Infty a))
      → x ∈ nat-constr (canonical-subset-Infty S)
    I (inl mapx＝el-Infty) = 𝟘-elim (el-not-img x mapx＝el-Infty)
    I (inr ∃a∈)
     = ∥∥-rec (holds-is-prop (nat-constr (canonical-subset-Infty S) x))
              (λ (a , a∈ , mapx＝mapa) → {!!}) ∃a∈

  canonical-subset-Infty-post-fixed
   : (S : 𝓟 {𝓤} ℕ-lfp)
   → zero-lfp ∈ S
   → ((x : ℕ-lfp) → x ∈ S → (suc-lfp x) ∈ S)
   → canonical-subset-Infty S ⊆ nat-constr (canonical-subset-Infty S) 
  canonical-subset-Infty-post-fixed S S-z S-s x
   = ∥∥-rec (holds-is-prop (nat-constr (canonical-subset-Infty S) x)) I 
   where
    I : Σ p ꞉ x ∈ nat-constr-lfp , S (x , p) holds
      → x ∈ nat-constr (canonical-subset-Infty S)
    I (p , Sxp)
     = canonical-subset-inversion S x ∣ inr ∣ (x , ∣ (p , Sxp) ∣ , refl) ∣ ∣
    I' = II (lfp→nat-constr-lfp x p) 
     where
      II : x ∈ nat-constr nat-constr-lfp
         → x ∈ nat-constr (canonical-subset-Infty S)
      II = ∥∥-rec (holds-is-prop (nat-constr (canonical-subset-Infty S) x)) III
       where
        III : (x ＝ el-Infty)
            + (∃ a ꞉ Infty , a ∈ nat-constr-lfp × (x ＝ map-Infty a))
            → x ∈ nat-constr (canonical-subset-Infty S)
        III (inl x＝el-Infty) = ∣ inl x＝el-Infty ∣
        III (inr ∃a∈lfp)
         = ∥∥-rec (holds-is-prop (nat-constr (canonical-subset-Infty S) x))
            IV ∃a∈lfp
         where
          IV : Σ a ꞉ Infty , a ∈ nat-constr-lfp × (x ＝ map-Infty a)
             → x ∈ nat-constr (canonical-subset-Infty S)
          IV (a , a∈ , x＝mapa)
           = ∣ inr ∣ a , ∣ a∈ , {!!} ∣ , x＝mapa ∣ ∣
           where
            V : (suc-lfp (a , a∈)) ∈ S
            V = transport (_∈ S) (to-subtype-＝
                 (holds-is-prop ∘ nat-constr-lfp) x＝mapa) Sxp -}

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

We now give a recursion principle for ℕ-lfp.
(Is this possible???)

\begin{code}



\end{code}
