Ian Ray. August 27 2026.

Using the least pre-fixed point principle from NatfromTarskiLFP-SmallBasis we
construct a relation which encodes the graph of a recursively defined function
from ℕ-lfp to some pointed set with endomap. Using prop-induction we can show
this graph is functional and from there we can produce a geniune recursion
principle for ℕ-lfp.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons

module OrderedTypes.NatRecfromTarskiLFP-SmallBasis
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : Prop-Ext)
       where

private
 fe' : FunExt
 fe' 𝓤 𝓥 = fe {𝓤} {𝓥}

open import MLTT.Spartan
open import UF.Equiv
open import UF.Logic
open import UF.Powerset-MultiUniverse
open import UF.Sets
open import UF.Subsingletons-FunExt
open import UF.SubtypeClassifier
open import OrderedTypes.SupLattice pt fe
open import OrderedTypes.SupLattice-SmallBasis pt fe
open import OrderedTypes.NatfromTarskiLFP-SmallBasis pt fe pe 

open AllCombinators pt fe
open PropositionalTruncation pt hiding (_∨_)

module nat-rec-weak-inf-tarsk
         (wi : weak-infinity 𝓤) (lfp : TarskiLFP-SmallBasis (𝓤 ⁺) 𝓤 𝓤)
         (X : 𝓤 ̇) (X-set : is-set X) (x₀ : X) (s : X → X)
       where

 open weak-infinity wi
 open nat-weak-inf-tarski wi lfp

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
     II (inl (z＝z , x＝x₀)) = x＝x₀ ⁻¹
     II (inr ∃mx')
      = ∥∥-rec X-set
         (λ (m , x' , mx'∈ , zero＝sucm , x＝sx')
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

 opaque
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

module _ (wi : weak-infinity 𝓤) (lfp : TarskiLFP-SmallBasis (𝓤 ⁺) 𝓤 𝓤) where

 open nat-weak-inf-tarski wi lfp
 open nat-rec-weak-inf-tarsk wi lfp

 ℕ-recursion-lfp : (X : 𝓤 ̇) 
                 → is-set X
                 → X
                 → (X → X)
                 → ℕ-lfp → X
 ℕ-recursion-lfp X X-set x₀ s = recursive-function X X-set x₀ s

 ℕ-recursion-comp-zero-lfp
  : (X : 𝓤 ̇) (X-set : is-set X) (x₀ : X) (s : X → X)
  → ℕ-recursion-lfp X X-set x₀ s zero-lfp ＝ x₀
 ℕ-recursion-comp-zero-lfp X X-set x₀ s = rec-comp-zero X X-set x₀ s

 ℕ-recursion-comp-suc-lfp
  : (X : 𝓤 ̇) (X-set : is-set X) (x₀ : X) (s : X → X)
  → (n : ℕ-lfp)
  → ℕ-recursion-lfp X X-set x₀ s (suc-lfp n)
  ＝ s (ℕ-recursion-lfp X X-set x₀ s n)
 ℕ-recursion-comp-suc-lfp X X-set x₀ s = rec-comp-suc X X-set x₀ s

\end{code}


