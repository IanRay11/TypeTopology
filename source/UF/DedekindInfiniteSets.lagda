Ian Ray. 29th October 2026.

...

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons
open import UF.Univalence

module UF.DedekindInfiniteSets
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : Prop-Ext)
        (ua : Univalence)
       where

private
 fe' : FunExt
 fe' 𝓤 𝓥 = fe {𝓤} {𝓥}

open import MLTT.Spartan
open import MLTT.Plus-Properties
open import UF.Base
open import UF.DiscreteAndSeparated
open import UF.Embeddings
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.Equiv-FunExt
open import UF.Sets
open import ReflexiveGraphs.Constructions using
             (refl-graph-×; cotensor-refl-graph; Δ; total-refl-graph)
open import ReflexiveGraphs.Displayed
open import ReflexiveGraphs.DisplayedUnivalent
open import ReflexiveGraphs.Lenses
open import ReflexiveGraphs.Type
open import ReflexiveGraphs.UnbiasedLenses
open import ReflexiveGraphs.Univalent
open import ReflexiveGraphs.UnivalentClosureProperties
open import ReflexiveGraphs.UnivalentFamilies

\end{code}

TODO: Check imports.

TODO: Spellcheck.

We define the type of dedekind infinite sets.

\begin{code}

record is-dedekind-infinite-set (I : 𝓤 ̇) : 𝓤 ⁺ ̇
 where
 field
  is-set-Inf : is-set I
  el-Inf : I
  map-Inf : I → I
  map-inj : (x y : I) → map-Inf x ＝ map-Inf y → x ＝ y
  el-not-img : (x : I) → ¬ (map-Inf x ＝ el-Inf)

Dedekind-Infinite : (𝓤 : Universe) → 𝓤 ⁺ ̇
Dedekind-Infinite 𝓤 = Σ I ꞉ 𝓤 ̇ , is-dedekind-infinite-set I

\end{code}

We will now give some examples of large* dedekind infinite sets.

*By large we mean the underlying type itself lives in a successor universe.*

Example 1:

Rigid N+1-algebras.

Recall, an N+1-algebra consists of a type X together with a point x₀ : X and a
map s : X → X (this data can also be assembled as a map X + 1 → X). Then a
morphism of N+1-algebras (X , x₀ , s) and (Y , y₀ , s') is a map f : X → Y such
that f(x₀) ＝ y₀ and s' ∘ f ∼ f ∘ s. Finally, and isomorphism of N+1-algebras is
a morphism for which f : X → Y is an equivalence. We say thatan N+1-algebra is
rigid if the type of automorphisms is contractible (another way to say this is
there are no non-trivial automorphisms).

Using univalence we can show that the type of rigid N+1-algebras is a dedekind
infinite set.

\begin{code}

N+1-Algebra : (𝓤 : Universe) → 𝓤 ⁺ ̇
N+1-Algebra 𝓤 = Σ X ꞉ 𝓤 ̇ , X × (X → X)

_→N+1_ : (N+1-Algebra 𝓤) → (N+1-Algebra 𝓣) → 𝓤 ⊔ 𝓣 ̇
(X , x₀ , s) →N+1 (Y , y₀ , s')
 = Σ f ꞉ (X → Y) , (f x₀ ＝ y₀) × (f ∘ s ∼ s' ∘ f)

_≅N+1_ : (N+1-Algebra 𝓤) → (N+1-Algebra 𝓣) → 𝓤 ⊔ 𝓣 ̇
𝓧 ≅N+1 𝓨 = Σ (f , _) ꞉ 𝓧 →N+1 𝓨 , is-equiv f

_≅'N+1_ : (N+1-Algebra 𝓤) → (N+1-Algebra 𝓣) → 𝓤 ⊔ 𝓣 ̇
𝓧@(X , x₀ , s) ≅'N+1 𝓨@(Y , y₀ , s')
 = Σ e ꞉ X ≃ Y , ((⌜ e ⌝ x₀) ＝ y₀) × (⌜ e ⌝ ∘ s ∼ s' ∘ ⌜ e ⌝)

≅N+1≃≅'N+1 : (𝓧 : N+1-Algebra 𝓤) (𝓨 : N+1-Algebra 𝓣)
           → (𝓧 ≅N+1 𝓨) ≃ (𝓧 ≅'N+1 𝓨)
≅N+1≃≅'N+1 𝓧@(X , x₀ , s) 𝓨@(Y , y₀ , s')
 = (Σ (f , _) ꞉ 𝓧 →N+1 𝓨 , is-equiv f)                                 ≃⟨ I ⟩
   (Σ f ꞉ (X → Y) , ((f x₀ ＝ y₀) × (f ∘ s ∼ s' ∘ f)) × (is-equiv f))  ≃⟨ II ⟩
   (Σ f ꞉ (X → Y) , (is-equiv f) × ((f x₀ ＝ y₀) × (f ∘ s ∼ s' ∘ f)))  ≃⟨ ≃-sym I ⟩
   (Σ e ꞉ X ≃ Y , ((⌜ e ⌝ x₀) ＝ y₀) × (⌜ e ⌝ ∘ s ∼ s' ∘ ⌜ e ⌝))       ■
    where
     I = Σ-assoc
     II = Σ-cong (λ _ → ×-comm)

\end{code}

We use SIP in the form of unbiased univalent reflexive graph lenses to
characterize the identity type of N+1-Algebra.

\begin{code}

module _ (𝓤 : Universe) where

 N+1-unbiased-lens : Unbiased-Lens 𝓤 𝓤 (universe-refl-graph 𝓤)
 N+1-unbiased-lens
  = (I , record
          {lext = λ {X Y : 𝓤 ̇} (e : X ≃ Y) ((r₁ , r₂) : X × (X → X))
                → (⌜ e ⌝ r₁ , ⌜ e ⌝ ∘ r₂);
           rext = λ {X Y : 𝓤 ̇} (e : X ≃ Y) ((r₁ , r₂) : Y × (Y → Y))
                → (r₁ , r₂ ∘ ⌜ e ⌝);
           ext-refl = λ {X : 𝓤 ̇} ((r₁ , r₂) : X × (X → X)) → (refl , ∼-refl);
           rext-refl = λ {X : 𝓤 ̇} ((r₁ , r₂) : X × (X → X)) → (refl , ∼-refl)})
  where
   I : {X Y : 𝓤 ̇} → X ≃ Y → Refl-Graph 𝓤 𝓤
   I {X} {Y} e = Δ Y ⊗ (X ➙ Δ Y)

 N+1-unbiased-lens-is-univalent
  : unbiased-lens-is-univalent (universe-refl-graph 𝓤) N+1-unbiased-lens
 N+1-unbiased-lens-is-univalent {X} {Y} e
  = univalence-closed-under-× (Δ Y) (X ➙ Δ Y)
     (discrete-refl-graph-is-univalent Y)
     (univalence-closed-under-cotensor fe X (Δ Y)
      (discrete-refl-graph-is-univalent Y))

 N+1-unbiased-lens-display
  : Displayed-Refl-Graph 𝓤 𝓤 (universe-refl-graph 𝓤)
 N+1-unbiased-lens-display
  = disp± (universe-refl-graph 𝓤) N+1-unbiased-lens

 N+1-unbiased-lens-display-univalent
  : is-displayed-univalent-refl-graph (universe-refl-graph 𝓤)
     N+1-unbiased-lens-display 
 N+1-unbiased-lens-display-univalent
  = disp-unbiased-lens-univalent (universe-refl-graph 𝓤) N+1-unbiased-lens
      (λ - → N+1-unbiased-lens-is-univalent (≃-refl -))

 N+1-unbiased-lens-total
  : Refl-Graph (𝓤 ⁺) 𝓤
 N+1-unbiased-lens-total
  = total-refl-graph (universe-refl-graph 𝓤) N+1-unbiased-lens-display

 private
  observation : ⟨ N+1-unbiased-lens-total ⟩ ＝ N+1-Algebra 𝓤
  observation = refl

 N+1-unbiased-lens-total-univalent
  : is-univalent-refl-graph N+1-unbiased-lens-total 
 N+1-unbiased-lens-total-univalent
  = univalence-closed-under-total (universe-refl-graph 𝓤) N+1-unbiased-lens-display
     (univalent-universe-is-univalent-family 𝓤 (ua 𝓤))
     N+1-unbiased-lens-display-univalent

\end{code}

We now give the characterization.

\begin{code}

 N+1-Algebra-＝-characterization : (𝓧 : N+1-Algebra 𝓤) (𝓨 : N+1-Algebra 𝓤)
                                 → (𝓧 ＝ 𝓨) ≃ (𝓧 ≅N+1 𝓨)
 N+1-Algebra-＝-characterization 𝓧@(X , x₀ , s) 𝓨@(Y , y₀ , s')
  = ≃-comp I (≃-sym (≅N+1≃≅'N+1 𝓧 𝓨))
  where
   I : (𝓧 ＝ 𝓨) ≃ (𝓧 ≅'N+1 𝓨)
   I = id-equiv-edge (N+1-unbiased-lens-total , N+1-unbiased-lens-total-univalent)
        𝓧 𝓨

\end{code}

We now give a characterization of the identity type of N+1 morphisms.

\begin{code}

 →N+1-lens
  : (𝓧@(X , x₀ , s) : N+1-Algebra 𝓤) (𝓨@(Y , y₀ , s') : N+1-Algebra 𝓤)
  → Oplax-Covariant-Lens 𝓤 𝓤 (X ➙ Δ Y)
 →N+1-lens 𝓧@(X , x₀ , s) 𝓨@(Y , y₀ , s')
  = (I , record{push = λ {f g : X → Y} (H : f ∼ g)
                         ((f-point , f-comm) : (f x₀ ＝ y₀) × (f ∘ s ∼ s' ∘ f))
                       → ((H x₀ ⁻¹ ∙ f-point)
                          , λ (x : X) → H (s x) ⁻¹ ∙ f-comm x ∙ ap s' (H x));
                push-refl
                 = λ {f : X → Y}
                      ((f-point , f-comm) : (f x₀ ＝ y₀) × (f ∘ s ∼ s' ∘ f))
                    → (refl-left-neutral
                       , dfunext fe (λ (x : X) → refl-left-neutral))})
  where
   I : (X → Y) → Refl-Graph 𝓤 𝓤
   I f = Δ (f x₀ ＝ y₀) ⊗ Δ (f ∘ s ∼ s' ∘ f)

 →N+1-unbiased-lens
  : (𝓧@(X , x₀ , s) : N+1-Algebra 𝓤) (𝓨@(Y , y₀ , s') : N+1-Algebra 𝓤)
  → Unbiased-Lens 𝓤 𝓤 (X ➙ Δ Y)
 →N+1-unbiased-lens = {!!}

 →N+1-＝-characterization
  : {𝓧@(X , x₀ , s) : N+1-Algebra 𝓤} {𝓨@(Y , y₀ , s') : N+1-Algebra 𝓤}
  → (𝓯@(f , f-point , f-comm) 𝓰@(g , g-point , g-comm) : 𝓧 →N+1 𝓨)
  → (𝓯 ＝ 𝓰)
  ≃ (Σ H ꞉ (f ∼ g) , (H x₀ ∙ g-point ＝ f-point)
                   × (∼-trans f-comm (∼-ap-∘ s' H) ＝ ∼-trans (H ∘ s) g-comm))
 →N+1-＝-characterization = {!!}

\end{code}

We will now construct a point of N+1-Algebra and endomap on N+1-Algebra which
is injective by not surjective with respect to ≅N+1.

\begin{code}

 point-N+1 : N+1-Algebra 𝓤
 point-N+1 = (𝟙 , ⋆ , id)

 succ-N+1 : N+1-Algebra 𝓤 → N+1-Algebra 𝓤
 succ-N+1 (X , x₀ , s) = ((X + 𝟙{𝓤}) , inr ⋆ , s+)
  module succ-data where
   s+ : X + 𝟙 → X + 𝟙
   s+ (inl x) = inl (s x)
   s+ (inr ⋆) = inl x₀

 point-is-not-succ-N+1 : (𝓧 : N+1-Algebra 𝓤)
                       → ¬ (point-N+1 ＝ succ-N+1 𝓧)
 point-is-not-succ-N+1 (X , x₀ , s) point＝map𝓧 = ⌜ X≃𝟘 ⌝ x₀
  where
   𝟙＝X+𝟙 : 𝟙 ＝ X + 𝟙
   𝟙＝X+𝟙 = ap pr₁ point＝map𝓧
   X+𝟙≃𝟙 : X + 𝟙 ≃ 𝟙
   X+𝟙≃𝟙 = idtoeq (X + 𝟙) 𝟙 (𝟙＝X+𝟙 ⁻¹)
   X≃𝟘 : X ≃ 𝟘
   X≃𝟘 = adjoined-point-contractible-implies-empty X X+𝟙≃𝟙

 succ-lc-map : {𝓧@(X , _) 𝓨@(Y , _) : N+1-Algebra 𝓤}
             → ((f , _) : succ-N+1 𝓧 →N+1 succ-N+1 𝓨)
             → left-cancellable f
             → X → Y
 succ-lc-map (f , f-point , _) f-lc x = pr₁ (inl-preservation f f-point f-lc x)

 succ-lc-map∼ : {𝓧@(X , _) 𝓨@(Y , _) : N+1-Algebra 𝓤}
              → (𝓯@(f , _) : succ-N+1 𝓧 →N+1 succ-N+1 𝓨)
              → (f-lc : left-cancellable f)
              → (x : X) → f (inl x) ＝ inl (succ-lc-map 𝓯 f-lc x)
 succ-lc-map∼ (f , f-point , _) f-lc x = pr₂ (inl-preservation f f-point f-lc x)

 succ-lc-map-point : {𝓧@(X , x₀ , _) 𝓨@(Y , y₀ , _) : N+1-Algebra 𝓤}
                   → (𝓯@(f , _) : succ-N+1 𝓧 →N+1 succ-N+1 𝓨)
                   → (f-lc : left-cancellable f)
                   → succ-lc-map 𝓯 f-lc x₀ ＝ y₀
 succ-lc-map-point {(X , x₀ , s)} {(Y , y₀ , s')} 𝓯@(f , f-point , f-comm) f-lc
  = inl-lc (inl (f' x₀)                ＝⟨ f∼f' x₀ ⁻¹ ⟩
            f (inl x₀)                 ＝⟨by-definition⟩
            f (s+ X x₀ s (inr ⋆))      ＝⟨ f-comm (inr ⋆) ⟩
            s+ Y y₀ s' (f (inr ⋆))     ＝⟨ ap (s+ Y y₀ s') f-point ⟩
            s+ Y y₀ s' (inr ⋆)         ＝⟨by-definition⟩
            inl y₀                     ∎)
  where
   open succ-data
   f' = succ-lc-map 𝓯 f-lc
   f∼f' = succ-lc-map∼ 𝓯 f-lc

 succ-lc-map-comm : {𝓧@(X , x₀ , s) 𝓨@(Y , y₀ , s') : N+1-Algebra 𝓤}
                  → (𝓯@(f , _) : succ-N+1 𝓧 →N+1 succ-N+1 𝓨)
                  → (f-lc : left-cancellable f)
                  → succ-lc-map 𝓯 f-lc ∘ s ∼ s' ∘ succ-lc-map 𝓯 f-lc
 succ-lc-map-comm {(X , x₀ , s)} {(Y , y₀ , s')} 𝓯@(f , f-point , f-comm) f-lc x
  = inl-lc (inl (f' (s x))           ＝⟨ f∼f' (s x) ⁻¹ ⟩
            f (inl (s x))            ＝⟨by-definition⟩
            f (s+ X x₀ s (inl x))    ＝⟨ f-comm (inl x) ⟩
            s+ Y y₀ s' (f (inl x))   ＝⟨ ap (s+ Y y₀ s') (f∼f' x) ⟩
            s+ Y y₀ s' (inl (f' x))  ＝⟨by-definition⟩
            inl (s' (f' x))          ∎)
  where
   open succ-data
   f' = succ-lc-map (f , f-point , f-comm) f-lc
   f∼f' = succ-lc-map∼ (f , f-point , f-comm) f-lc

 succ-lc-→N+1 : (𝓧 𝓨 : N+1-Algebra 𝓤)
              → ((f , _) : succ-N+1 𝓧 →N+1 succ-N+1 𝓨)
              → left-cancellable f
              → 𝓧 →N+1 𝓨
 succ-lc-→N+1 𝓧@(X , x₀ , s) 𝓨@(Y , y₀ , s') 𝓯@(f , f-point , f-comm) f-lc
  = (succ-lc-map 𝓯 f-lc , succ-lc-map-point 𝓯 f-lc , succ-lc-map-comm 𝓯 f-lc) 

 succ-injective-N+1 : (𝓧 𝓨 : N+1-Algebra 𝓤)
                    → succ-N+1 𝓧 ≅N+1 succ-N+1 𝓨
                    → 𝓧 ≅N+1 𝓨
 succ-injective-N+1
  𝓧@(X , x₀ , s) 𝓨@(Y , y₀ , s') (𝓯@(f , f-point , f-comm) , f-equiv)
  = (succ-lc-→N+1 𝓧 𝓨 𝓯 (equivs-are-lc f f-equiv) , f'-is-equiv)
  module succ-inj where
   f' = succ-lc-map 𝓯 (equivs-are-lc f f-equiv)
   f∼f' = succ-lc-map∼ 𝓯 (equivs-are-lc f f-equiv)
   f'-is-equiv : is-equiv f'
   f'-is-equiv = vv-equivs-are-equivs f'
                  (λ (y : Y) → equiv-to-singleton (I y)
                                (equivs-are-vv-equivs f f-equiv (inl y)))
    where
     I : (y : Y) → fiber f' y ≃ fiber f (inl y)
     I y = (Σ x ꞉ X , f' x ＝ y)                     ≃⟨ III ⟩
           (Σ x ꞉ X , inl {𝓤} {𝓤} (f' x) ＝ inl y)   ≃⟨ IV ⟩
           (Σ x ꞉ X , f (inl x) ＝ inl y)            ≃⟨ V ⟩
           (Σ x ꞉ X + 𝟙 , f x ＝ inl y)              ■
      where
       II = inl-is-embedding Y 𝟙 
       III = Σ-cong (λ - → (ap inl , embedding-gives-embedding' inl II (f' -) y))
       IV = Σ-cong (λ - → ＝-cong-l (inl (f' -)) (inl y) (f∼f' - ⁻¹))
       m : (Σ x ꞉ X , f (inl x) ＝ inl y) → (Σ x ꞉ X + 𝟙 , f x ＝ inl y)
       m (x , p) = (inl x , p)
       m' : (Σ x ꞉ X + 𝟙 , f x ＝ inl y) → (Σ x ꞉ X , f (inl x) ＝ inl y)
       m' (inl x , p) = (x , p)
       m' (inr ⋆ , p) = 𝟘-elim (+disjoint (p ⁻¹ ∙ f-point))
       mm'∼id : m ∘ m' ∼ id
       mm'∼id (inl x , p) = refl
       mm'∼id (inr ⋆ , p) = 𝟘-elim (+disjoint (p ⁻¹ ∙ f-point))
       V = (m , qinvs-are-equivs m (m' , ∼-refl , mm'∼id))

\end{code}

We define the type of rigid N+1-algebras, characterize the identity type and
use univalence to show that this type is a set.

\begin{code}

Rigid-N+1-Algebra : (𝓤 : Universe) → (𝓤 ⁺) ̇
Rigid-N+1-Algebra 𝓤 = Σ 𝓧 ꞉ N+1-Algebra 𝓤 , is-contr (𝓧 ≅N+1 𝓧)

Rigid-N+1-Algebra-＝-characterization
 : ((𝓧 , contr₁) : Rigid-N+1-Algebra 𝓤) ((𝓨 , contr₂) : Rigid-N+1-Algebra 𝓤)
 → ((𝓧 , contr₁) ＝ (𝓨 , contr₂)) ≃ (𝓧 ≅N+1 𝓨)
Rigid-N+1-Algebra-＝-characterization = {!!}

\end{code}

We show that the point point-N+1 is rigid and that rigidity is closed under the
endomap succ-N+1.

\begin{code}

module _ {𝓤 : Universe} where

 point-N+1-map : point-N+1 𝓤 →N+1 point-N+1 𝓤
 point-N+1-map = (id , 𝟙-is-prop ⋆ ⋆ , (λ - → 𝟙-is-prop ⋆ ⋆))

 point-N+1-automorphism : point-N+1 𝓤 ≅N+1 point-N+1 𝓤
 point-N+1-automorphism = (point-N+1-map , id-is-equiv 𝟙)

 point-N+1-is-rigid : is-contr (point-N+1 𝓤 ≅N+1 point-N+1 𝓤)
 point-N+1-is-rigid
  = (point-N+1-automorphism , I)
  where
   I : is-central (point-N+1 𝓤 ≅N+1 point-N+1 𝓤) point-N+1-automorphism
   I ((f , f-point , f-comm) , f-equiv)
    = to-subtype-＝ (λ (- , _) → being-equiv-is-prop fe' -)
       (⌜ (→N+1-＝-characterization 𝓤 point-N+1-map ((f , f-point , f-comm))) ⌝⁻¹
        ((λ _ → 𝟙-is-prop ⋆ ⋆)
         , 𝟙-is-set (𝟙-is-prop ⋆ ⋆ ∙ f-point) (𝟙-is-prop ⋆ ⋆)
         , dfunext fe (λ - → 𝟙-is-set (𝟙-is-prop ⋆ ⋆)
                      (𝟙-is-prop ⋆ ⋆ ∙ f-comm -))))

 rigid-point-N+1 : Rigid-N+1-Algebra 𝓤
 rigid-point-N+1 = (point-N+1 𝓤 , point-N+1-is-rigid)

 succ-N+1-is-rigid : (𝓧 : N+1-Algebra 𝓤)
                   → is-contr (𝓧 ≅N+1 𝓧)
                   → is-contr (succ-N+1 𝓤 𝓧 ≅N+1 succ-N+1 𝓤 𝓧)
 succ-N+1-is-rigid
  𝓧@(X , x₀ , s) (𝓰@((g , g-point , g-comm) , g-equiv) , 𝓰-central)
  = (((g+ , refl , g+-comm) , ⌜⌝-is-equiv (Ap+ 𝟙 (g , g-equiv))) , 𝓰+-central)
  where
   open succ-data
   g+ : X + 𝟙{𝓤} → X + 𝟙{𝓤}
   g+ = ⌜ (Ap+ 𝟙 (g , g-equiv)) ⌝
   g+-comm : g+ ∘ s+ 𝓤 X x₀ s ∼ s+ 𝓤 X x₀ s ∘ g+
   g+-comm (inl x) = ap inl (g-comm x) 
   g+-comm (inr ⋆) = ap inl g-point
   𝓰+-central : is-central
                 (succ-N+1 𝓤 (X , x₀ , s) ≅N+1 succ-N+1 𝓤 (X , x₀ , s))
                 ((g+ , refl , g+-comm) , ⌜⌝-is-equiv (Ap+ 𝟙 (g , g-equiv)))
   𝓰+-central (𝓯@(f , f-point , f-comm) , f-equiv)
    = to-subtype-＝ (λ (- , _) → being-equiv-is-prop fe' -)
       (⌜ →N+1-＝-characterization 𝓤 (g+ , refl , g+-comm) 𝓯 ⌝⁻¹
         (III , trans-sym f-point , V))
    where
     III : g+ ∼ f
     III (inl x) = inl (g x)    ＝⟨ ap inl (happly IV x) ⟩
                   inl (f' x)   ＝⟨ f∼f' x ⁻¹ ⟩
                   f (inl x)    ∎
      where
       open succ-inj 𝓤 X x₀ s X x₀ s f f-point f-comm f-equiv
       g-cent
        = 𝓰-central
           ((f' , succ-lc-map-point 𝓤 𝓯 (equivs-are-lc f f-equiv)
             , succ-lc-map-comm 𝓤 𝓯 (equivs-are-lc f f-equiv)) , f'-is-equiv)
       IV : g ＝ f'
       IV = ap pr₁ (ap pr₁ g-cent)
     III (inr ⋆) = f-point ⁻¹
     V : ∼-trans g+-comm (∼-ap-∘ (s+ 𝓤 X x₀ s) III)
       ＝ ∼-trans (III ∘ s+ 𝓤 X x₀ s) f-comm
     V = dfunext fe VI
      where
       VI : ∼-trans g+-comm (∼-ap-∘ (s+ 𝓤 X x₀ s) III)
          ∼ ∼-trans (III ∘ s+ 𝓤 X x₀ s) f-comm
       VI (inl x) = g+-comm (inl x) ∙ ap (s+ 𝓤 X x₀ s) (III (inl x)) ＝⟨ {!!} ⟩
                    {!!}                                             ＝⟨ {!!} ⟩
                    {!!}                                             ＝⟨ {!!} ⟩
                    (III ∘ s+ 𝓤 X x₀ s) (inl x) ∙ f-comm (inl x)     ∎
       VI (inr ⋆) = {!!}

 rigid-succ-N+1 : Rigid-N+1-Algebra 𝓤 → Rigid-N+1-Algebra 𝓤
 rigid-succ-N+1 (𝓧 , 𝓧-rigid) = (succ-N+1 𝓤 𝓧 , succ-N+1-is-rigid 𝓧 𝓧-rigid)

\end{code}

Finally, we show that injectivity and non-surjectivity with respect to ≅N+1
can be upgraded, via univalence, to identifications.

\begin{code}



\end{code}

Thus, Rigid-N+1-Algebra is an example of a dedekind infinite set.

\begin{code}



\end{code}

----------------------------------------------------------------------------

Example 2:

Rigid "encodings" of Nat.
