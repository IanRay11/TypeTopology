Ian Ray, 15th January 2025

Pushouts are defined as higher inductive type (in the form of a record type).
We postulate point and path constructors, an induction principle and
propositional computation rules for each constructor.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module UF.Pushouts (fe : Fun-Ext) where

open import MLTT.Spartan
open import UF.Base
open import UF.CoconesofSpans fe
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.PropIndexedPiSigma
open import UF.Retracts
open import UF.Subsingletons
open import UF.Yoneda

\end{code}

Now we will define the universal property, induction principle and propositional
computation rules for pushouts and show they are inter-derivable.

In fact we will only show:
(1) The induction principle and propositional computation rules implies the
  the recursion principle with corresponding computation rules and the uniqueness
  principle.

(2) The recursion principle with corresponding computation rules and the
  uniqueness principle implies the non-dependent universal property.

(3) The universal property implies the induction principle.

\begin{code}

canonical-map-to-cocone
 : {A : 𝓤  ̇} {B : 𝓥  ̇} {C : 𝓦  ̇} (S : 𝓤'  ̇) 
   (f : C → A) (g : C → B) (s : cocone f g S) (X : 𝓣  ̇)
 → (S → X) → cocone f g X
canonical-map-to-cocone S f g (i , j , G) X u =
 (u ∘ i , u ∘ j , ∼-ap-∘ u G)

Pushout-Universal-Property
 : {A : 𝓤  ̇} {B : 𝓥  ̇} {C : 𝓦  ̇} (S : 𝓤'  ̇) 
   (f : C → A) (g : C → B) (s : cocone f g S) (X : 𝓣  ̇)
 → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓤' ⊔ 𝓣  ̇
Pushout-Universal-Property S f g s X
 = is-equiv (canonical-map-to-cocone S f g s X)

canonical-map-to-dependent-cocone
 : {A : 𝓤  ̇} {B : 𝓥  ̇} {C : 𝓦  ̇} (S : 𝓤'  ̇)
   (f : C → A) (g : C → B) (s : cocone f g S) (P : S →  𝓣  ̇)
 → ((x : S) → P x) → dependent-cocone f g S s P
canonical-map-to-dependent-cocone S f g (i , j , G) P d =
 (d ∘ i , d ∘ j , λ c → apd d (G c))

Pushout-Dependent-Universal-Property
 : {A : 𝓤  ̇} {B : 𝓥  ̇} {C : 𝓦  ̇} (S : 𝓤'  ̇) 
   (f : C → A) (g : C → B) (s : cocone f g S) (P : S →  𝓣  ̇)
 → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓤' ⊔ 𝓣  ̇
Pushout-Dependent-Universal-Property S f g s P =
 is-equiv (canonical-map-to-dependent-cocone S f g s P)

Pushout-Induction-Principle
 : {A : 𝓤  ̇} {B : 𝓥  ̇} {C : 𝓦  ̇} (S : 𝓤'  ̇)
   (f : C → A) (g : C → B) (s : cocone f g S) (P : S → 𝓣  ̇)
 → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓤' ⊔ 𝓣  ̇
Pushout-Induction-Principle {_} {_} {_} {_} {_} {A} {B} {C} S f g (i , j , G) P 
 = (l : (a : A) → P (i a))
 → (r : (b : B) → P (j b))
 → ((c : C) → transport P (G c) (l (f c)) ＝ r (g c))
 → (x : S) → P x

Pushout-Computation-Rule₁
 : {A : 𝓤  ̇} {B : 𝓥  ̇} {C : 𝓦  ̇} (S : 𝓤'  ̇) 
   (f : C → A) (g : C → B) (s : cocone f g S) (P : S → 𝓣  ̇)
 → Pushout-Induction-Principle S f g s P
 → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓣  ̇
Pushout-Computation-Rule₁
 {_} {_} {_} {_} {_} {A} {B} {C} S f g (i , j , G) P S-ind
 = (l : (a : A) → P (i a))
 → (r : (b : B) → P (j b))
 → (H : (c : C) → transport P (G c) (l (f c)) ＝ r (g c))
 → (a : A)
 → S-ind l r H (i a) ＝ l a

Pushout-Computation-Rule₂
 : {A : 𝓤  ̇} {B : 𝓥  ̇} {C : 𝓦  ̇} (S : 𝓤'  ̇)
   (f : C → A) (g : C → B) (s : cocone f g S) (P : S → 𝓣  ̇)
 → Pushout-Induction-Principle S f g s P
 → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓣  ̇
Pushout-Computation-Rule₂
 {_} {_} {_} {_} {_} {A} {B} {C} S f g (i , j , G) P S-ind
 = (l : (a : A) → P (i a))
 → (r : (b : B) → P (j b))
 → (H : (c : C) → transport P (G c) (l (f c)) ＝ r (g c))
 → (b : B)
 → S-ind l r H (j b) ＝ r b

Pushout-Computation-Rule₃
 : {A : 𝓤  ̇} {B : 𝓥  ̇} {C : 𝓦  ̇} (S : 𝓤'  ̇) 
   (f : C → A) (g : C → B) (s : cocone f g S) (P : S → 𝓣  ̇)
   (S-ind : Pushout-Induction-Principle S f g s P)
 → Pushout-Computation-Rule₁ S f g s P S-ind
 → Pushout-Computation-Rule₂ S f g s P S-ind
 → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓣  ̇
Pushout-Computation-Rule₃
 {_} {_} {_} {_} {_}{A} {B} {C} S f g (i , j , G) P S-ind S-comp₁ S-comp₂
 = (l : (a : A) → P (i a))
 → (r : (b : B) → P (j b))
 → (H : (c : C) → transport P (G c) (l (f c)) ＝ r (g c))
 → (c : C)
 → apd (S-ind l r H) (G c) ∙ S-comp₂ l r H (g c)
 ＝ ap (transport P (G c)) (S-comp₁ l r H (f c)) ∙ H c

\end{code}

Now we will use a record type to give the pushout, point and path constructors,
and the dependent universal property.

\begin{code}

record pushouts-exist {A : 𝓤  ̇} {B : 𝓥  ̇} {C : 𝓦  ̇} (f : C → A) (g : C → B) : 𝓤ω
 where
 field
  pushout : 𝓤 ⊔ 𝓥 ⊔ 𝓦  ̇
  inll : A → pushout 
  inrr : B → pushout 
  glue : (c : C) → inll (f c) ＝ inrr (g c)
  pushout-induction
   : {P : pushout → 𝓣  ̇}
   → Pushout-Induction-Principle pushout f g (inll , inrr , glue) P
  pushout-ind-comp-inll
   : {P : pushout → 𝓣  ̇}
   → Pushout-Computation-Rule₁ pushout f g (inll , inrr , glue) P
      pushout-induction
  pushout-ind-comp-inrr
   : {P : pushout → 𝓣  ̇}
   → Pushout-Computation-Rule₂ pushout f g (inll , inrr , glue) P
      pushout-induction
  pushout-ind-comp-glue
   : {P : pushout → 𝓣  ̇}
   → Pushout-Computation-Rule₃ pushout f g (inll , inrr , glue) P
      pushout-induction pushout-ind-comp-inll pushout-ind-comp-inrr

\end{code}

We will observe that the pushout is a cocone and begin deriving some key
results from the induction principles:
recursion principle (along with corresponding computation rules), the uniqueness
principle and the universal property.

The following are logically equivalent

1) The induction principle with propositional computation rules
2) The recursion principle with propositional computation rules and the
   uniqueness principle
3) The universal property.

\begin{code}

 pushout-cocone : cocone f g pushout
 pushout-cocone = (inll , inrr , glue)
   
 pushout-recursion : {D : 𝓣  ̇}
                   → (l : A → D)
                   → (r : B → D)
                   → ((c : C) → l (f c) ＝ r (g c))
                   → pushout → D
 pushout-recursion l r G =
  pushout-induction l r (λ c → (transport-const (glue c) ∙ G c))

 pushout-rec-comp-inll : {D : 𝓣  ̇}
                       → (l : A → D)
                       → (r : B → D)
                       → (G : (c : C) → l (f c) ＝ r (g c))
                       → (a : A)
                       → pushout-recursion l r G (inll a) ＝ l a
 pushout-rec-comp-inll l r G =
  pushout-ind-comp-inll l r (λ c → (transport-const (glue c) ∙ G c))

 pushout-rec-comp-inrr : {D : 𝓣  ̇}
                       → (l : A → D)
                       → (r : B → D)
                       → (G : (c : C) → l (f c) ＝ r (g c))
                       → (b : B)
                       → pushout-recursion l r G (inrr b) ＝ r b
 pushout-rec-comp-inrr l r G =
  pushout-ind-comp-inrr l r (λ c → (transport-const (glue c) ∙ G c))

 pushout-rec-comp-glue
  : {D : 𝓣  ̇}
  → (l : A → D)
  → (r : B → D)
  → (G : (c : C) → l (f c) ＝ r (g c))
  → (c : C)
  → ap (pushout-recursion l r G) (glue c) ∙ pushout-rec-comp-inrr l r G (g c) 
  ＝ pushout-rec-comp-inll l r G (f c) ∙ G c
 pushout-rec-comp-glue {𝓣} {D} l r G c =
  ap (pushout-recursion l r G) (glue c) ∙ pushout-rec-comp-inrr l r G (g c)                                                                 ＝⟨ III ⟩
  transport-const (glue c) ⁻¹ ∙ apd (pushout-recursion l r G) (glue c)
   ∙ pushout-rec-comp-inrr l r G (g c)                      ＝⟨ V ⟩
  transport-const (glue c) ⁻¹
    ∙ ap (transport (λ - → D) (glue c)) (pushout-rec-comp-inll l r G (f c))
    ∙ (transport-const (glue c) ∙ G c)                      ＝⟨ VI ⟩
  transport-const (glue c) ⁻¹
    ∙ ap (transport (λ - → D) (glue c)) (pushout-rec-comp-inll l r G (f c))
    ∙ transport-const (glue c) ∙ G c                        ＝⟨ IX ⟩
  pushout-rec-comp-inll l r G (f c) ∙ G c                      ∎
  where
   II : ap (pushout-recursion l r G) (glue c)
      ＝ transport-const (glue c) ⁻¹
         ∙ apd (pushout-induction l r (λ - → (transport-const (glue -) ∙ G -)))
               (glue c)
   II = apd-from-ap (pushout-recursion l r G) (glue c)
   III = ap (_∙ pushout-rec-comp-inrr l r G (g c)) II 
   IV : apd (pushout-recursion l r G) (glue c)
       ∙ pushout-rec-comp-inrr l r G (g c)
      ＝ ap (transport (λ - → D) (glue c)) (pushout-rec-comp-inll l r G (f c))
       ∙ (transport-const (glue c) ∙ G c)
   IV = pushout-ind-comp-glue l r (λ - → (transport-const (glue -) ∙ G -)) c
   V : transport-const (glue c) ⁻¹ ∙ apd (pushout-recursion l r G) (glue c)
        ∙ pushout-rec-comp-inrr l r G (g c)
     ＝ transport-const (glue c) ⁻¹
        ∙ ap (transport (λ - → D) (glue c)) (pushout-rec-comp-inll l r G (f c))
        ∙ (transport-const (glue c) ∙ G c)
   V = ap-on-left-is-assoc (transport-const (glue c) ⁻¹) IV
   VI = ∙assoc (transport-const (glue c) ⁻¹ ∙ ap (transport (λ - → D) (glue c))
               (pushout-rec-comp-inll l r G (f c))) (transport-const (glue c))
               (G c) ⁻¹
   VII : ap (transport (λ - → D) (glue c)) (pushout-rec-comp-inll l r G (f c))
         ∙ transport-const (glue c)
       ＝ transport-const (glue c) ∙ pushout-rec-comp-inll l r G (f c)
   VII = homotopies-are-natural (transport (λ - → D) (glue c)) id
          (λ - → transport-const (glue c)) ⁻¹
   VIII : transport-const (glue c) ⁻¹
        ∙ ap (transport (λ - → D) (glue c)) (pushout-rec-comp-inll l r G (f c))
        ∙ transport-const (glue c)
     ＝ pushout-rec-comp-inll l r G (f c)
   VIII = ∙assoc (transport-const (glue c) ⁻¹)
                 (ap (transport (λ - → D) (glue c))
                 (pushout-rec-comp-inll l r G (f c))) (transport-const (glue c))
          ∙ ap-left-inverse (transport-const (glue c)) VII 
   IX = ap (_∙ G c) VIII

 pushout-uniqueness : (X : 𝓣 ̇)
                    → (s s' : pushout → X)
                    → (H : (a : A) → s (inll a) ＝ s' (inll a))
                    → (H' : (b : B) → s (inrr b) ＝ s' (inrr b))
                    → (G : (c : C)
                      → ap s (glue c) ∙ H' (g c) ＝ H (f c) ∙ ap s' (glue c))
                    → (x : pushout) → s x ＝ s' x
 pushout-uniqueness X s s' H H' G =
  pushout-induction H H' I
  where
   I : (c : C)
     → transport (λ - → s - ＝ s' -) (glue c) (H (f c)) ＝ H' (g c)
   I c = transport (λ - → s - ＝ s' -) (glue c) (H (f c)) ＝⟨ II ⟩
         ap s (glue c) ⁻¹ ∙ H (f c) ∙ ap s' (glue c)      ＝⟨ III ⟩
         H' (g c)                                         ∎
    where
     II = transport-after-ap' (glue c) s s' (H (f c))
     III = ap s (glue c) ⁻¹ ∙ H (f c) ∙ ap s' (glue c)   ＝⟨ IV ⟩
           ap s (glue c) ⁻¹ ∙ (H (f c) ∙ ap s' (glue c)) ＝⟨ V ⟩
           H' (g c)                                       ∎
      where
       IV = ∙assoc (ap s (glue c) ⁻¹) (H (f c)) (ap s' (glue c))
       V = ap-left-inverse (ap s (glue c)) (G c ⁻¹)
   
 pushout-universal-property
  : (X : 𝓣 ̇)
  → Pushout-Universal-Property pushout f g (inll , inrr , glue) X
 pushout-universal-property X = ((ψ , ϕ-ψ) , (ψ , ψ-ϕ))
  where
   ϕ : (pushout → X) → cocone f g X
   ϕ u = canonical-map-to-cocone pushout f g (inll , inrr , glue) X u
   ψ : cocone f g X → (pushout → X)
   ψ (l , r , G) = pushout-recursion l r G
   ψ-ϕ : ψ ∘ ϕ ∼ id
   ψ-ϕ u = dfunext fe (pushout-uniqueness X ((ψ ∘ ϕ) u) u
                   (pushout-rec-comp-inll (u ∘ inll) (u ∘ inrr) (∼-ap-∘ u glue))
                   (pushout-rec-comp-inrr (u ∘ inll) (u ∘ inrr) (∼-ap-∘ u glue))
                   (pushout-rec-comp-glue (u ∘ inll) (u ∘ inrr) (∼-ap-∘ u glue)))
   ϕ-ψ : ϕ ∘ ψ ∼ id
   ϕ-ψ (l , r , G) =
    inverse-cocone-map f g X ((ϕ ∘ ψ) (l , r , G)) (l , r , G)
     (pushout-rec-comp-inll l r G , pushout-rec-comp-inrr l r G ,
      ∼-sym (pushout-rec-comp-glue l r G))
   
\end{code}

We investigate only postulating the (non-dependent) universal property.

\begin{code}

record pushouts-exist' {A : 𝓤  ̇} {B : 𝓥  ̇} {C : 𝓦  ̇} (f : C → A) (g : C → B) : 𝓤ω
 where
 field
  pushout : 𝓤 ⊔ 𝓥 ⊔ 𝓦  ̇
  inll : A → pushout 
  inrr : B → pushout 
  glue : (c : C) → inll (f c) ＝ inrr (g c)
  pushout-universal-property
   : {X : 𝓣  ̇}
   → Pushout-Universal-Property pushout f g (inll , inrr , glue) X

 pushout-cocone : cocone f g pushout
 pushout-cocone = (inll , inrr , glue)

\end{code}

We will unpack the equivalence established by the universal property.

\begin{code}

 opaque
  pushout-fiber-is-singleton
   : {X : 𝓣  ̇}
   → (s : cocone f g X)
   → is-contr (fiber (canonical-map-to-cocone pushout f g pushout-cocone X) s)
  pushout-fiber-is-singleton {_} {X} s
   = equivs-are-vv-equivs (canonical-map-to-cocone pushout f g pushout-cocone X)
    pushout-universal-property s

  pushout-fiber-is-singleton'
   : {X : 𝓣  ̇}
   → (s : cocone f g X)
   → is-contr (Σ u ꞉ (pushout → X) ,
                 cocone-family f g X (u ∘ inll , u ∘ inrr , ∼-ap-∘ u glue) s)
  pushout-fiber-is-singleton' {_} {X} s 
   = equiv-to-singleton' (Σ-cong (λ - → cocone-identity-characterization f g X
                          (- ∘ inll , - ∘ inrr , ∼-ap-∘ - glue) s))
                         (pushout-fiber-is-singleton s)

  pushout-fiber-center
   : {X : 𝓣  ̇}
   → (s : cocone f g X)
   → Σ u ꞉ (pushout → X) ,
      cocone-family f g X (u ∘ inll , u ∘ inrr , ∼-ap-∘ u glue) s
  pushout-fiber-center s = center (pushout-fiber-is-singleton' s)

  pushout-fiber-centrality
   : {X : 𝓣  ̇}
   → (s : cocone f g X)
   → is-central (Σ u ꞉ (pushout → X) ,
                   cocone-family f g X (u ∘ inll , u ∘ inrr , ∼-ap-∘ u glue) s)
                (pushout-fiber-center s)
  pushout-fiber-centrality s = centrality (pushout-fiber-is-singleton' s)

  pushout-unique-map : {X : 𝓣  ̇}
                     → (s : cocone f g X)
                     → Σ u ꞉ (pushout → X) ,
                        cocone-family f g X (u ∘ inll , u ∘ inrr , ∼-ap-∘ u glue) s
                     → pushout → X
  pushout-unique-map s (u , _) = u

  pushout-inll-homotopy
   : {X : 𝓣  ̇}
   → (s : cocone f g X)
   → (z : Σ u ꞉ (pushout → X) ,
            cocone-family f g X (u ∘ inll , u ∘ inrr , ∼-ap-∘ u glue) s)
   → (pushout-unique-map s z) ∘ inll ∼ cocone-vertical-map f g X s
  pushout-inll-homotopy s (u , K , L , M) = K

  pushout-inrr-homotopy
   : {X : 𝓣  ̇}
   → (s : cocone f g X)
   → (z : Σ u ꞉ (pushout → X) ,
            cocone-family f g X (u ∘ inll , u ∘ inrr , ∼-ap-∘ u glue) s)
   → (pushout-unique-map s z) ∘ inrr ∼ cocone-horizontal-map f g X s
  pushout-inrr-homotopy s (u , K , L , M) = L

  pushout-glue-homotopy
   : {X : 𝓣  ̇}
   → (s : cocone f g X)
   → (z : Σ u ꞉ (pushout → X) ,
            cocone-family f g X (u ∘ inll , u ∘ inrr , ∼-ap-∘ u glue) s)
   → ∼-trans ((pushout-inll-homotopy s z) ∘ f) (cocone-commuting-square f g X s)
   ∼ ∼-trans (∼-ap-∘ (pushout-unique-map s z) glue)
             ((pushout-inrr-homotopy s z) ∘ g)
  pushout-glue-homotopy s (u , K , L , M) = M

\end{code}

Now we can derive the recursion principle, the corresponding propositional
computation rules and the uniqueness principles.

\begin{code}

 pushout-recursion : {D : 𝓣  ̇}
                   → (l : A → D)
                   → (r : B → D)
                   → ((c : C) → l (f c) ＝ r (g c))
                   → pushout → D
 pushout-recursion l r G
  = pushout-unique-map (l , r , G) (pushout-fiber-center (l , r , G))

 pushout-rec-comp-inll : {D : 𝓣  ̇}
                       → (l : A → D)
                       → (r : B → D)
                       → (G : (c : C) → l (f c) ＝ r (g c))
                       → (a : A)
                       → pushout-recursion l r G (inll a) ＝ l a
 pushout-rec-comp-inll l r G 
  = pushout-inll-homotopy (l , r , G) (pushout-fiber-center (l , r , G)) 

 pushout-rec-comp-inrr : {D : 𝓣  ̇}
                       → (l : A → D)
                       → (r : B → D)
                       → (G : (c : C) → l (f c) ＝ r (g c))
                       → (b : B)
                       → pushout-recursion l r G (inrr b) ＝ r b
 pushout-rec-comp-inrr l r G
  = pushout-inrr-homotopy (l , r , G) (pushout-fiber-center (l , r , G))
 
 pushout-rec-comp-glue
  : {D : 𝓣  ̇}
  → (l : A → D)
  → (r : B → D)
  → (G : (c : C) → l (f c) ＝ r (g c))
  → (c : C)
  → ap (pushout-recursion l r G) (glue c) ∙ pushout-rec-comp-inrr l r G (g c) 
  ＝ pushout-rec-comp-inll l r G (f c) ∙ G c
 pushout-rec-comp-glue l r G c
  = pushout-glue-homotopy (l , r , G) (pushout-fiber-center (l , r , G)) c ⁻¹

 pushout-uniqueness : {X : 𝓣 ̇}
                    → (u u' : pushout → X)
                    → (H : (a : A) → u (inll a) ＝ u' (inll a))
                    → (H' : (b : B) → u (inrr b) ＝ u' (inrr b))
                    → (M : (c : C)
                     → ap u (glue c) ∙ H' (g c) ＝ H (f c) ∙ ap u' (glue c))
                    → (x : pushout) → u x ＝ u' x
 pushout-uniqueness {_} {X} u u' H H' M
  = happly (pr₁ (from-Σ-＝ (singletons-are-props
    (pushout-fiber-is-singleton' (u' ∘ inll , u' ∘ inrr , ∼-ap-∘ u' glue))
     (u , H , H' , λ c → M c ⁻¹)
      (u' , ∼-refl , ∼-refl , λ c → refl-left-neutral))))

 pushout-uniqueness-inll : {X : 𝓣 ̇}
                         → (u u' : pushout → X)
                         → (H : (a : A) → u (inll a) ＝ u' (inll a))
                         → (H' : (b : B) → u (inrr b) ＝ u' (inrr b))
                         → (M : (c : C)
                           → ap u (glue c) ∙ H' (g c) ＝ H (f c) ∙ ap u' (glue c))
                         → (l : A → X)
                         → (L : (a : A) → u (inll a) ＝ l a)
                         → (L' : (a : A) → u' (inll a) ＝ l a)
                         → (a : A)
                         → pushout-uniqueness u u' H H' M (inll a) ∙ L' a ＝ L a
 pushout-uniqueness-inll u u' H H' M l L L' a = {!!}
                    
\end{code}

^^^^^^^^^^^Regarding above hole^^^^^^^^^^^^^^^^^^^^
!!!!!!!!!!!!I realized I needed computation rules for uniqueness to define the
computation rules below. So at this point I seperated the file into Pushouts and
CoconesofSpans (see new file). The goal is to define a notion of cocone morphism
and give the trivial direction of identity characterization, which I can use to
give the uniqueness computation rules.
(This resulted from discussion with Kristina Sojakova!) !!!!!!!!!!!!!!!!!!

Finally, we can derive the induction principle and the corresponding propositional
computation rules(?). First we will introduce an auxillary type which we will
call pre-induction. 

\begin{code}

 opaque
  pre-induction
   : {P : pushout → 𝓣  ̇}
   → (l : (a : A) → P (inll a))
   → (r : (b : B) → P (inrr b))
   → ((c : C) → transport P (glue c) (l (f c)) ＝ r (g c))
   → pushout → Σ x ꞉ pushout , P x
  pre-induction {_} {P} l r G = pushout-recursion l' r' G'
   where
    l' : A → Σ x ꞉ pushout , P x
    l' a = (inll a , l a)
    r' : B → Σ x ꞉ pushout , P x
    r' b = (inrr b , r b)
    G' : (c : C) → l' (f c) ＝ r' (g c)
    G' c = to-Σ-＝ (glue c , G c)

  pre-induction-comp-inll
   : {P : pushout → 𝓣  ̇}
   → (l : (a : A) → P (inll a))
   → (r : (b : B) → P (inrr b))
   → (G : (c : C) → transport P (glue c) (l (f c)) ＝ r (g c))
   → (a : A)
   → pre-induction l r G (inll a) ＝ (inll a , l a)
  pre-induction-comp-inll {_} {P} l r G = pushout-rec-comp-inll l' r' G'
   where
    l' : A → Σ x ꞉ pushout , P x
    l' a = (inll a , l a)
    r' : B → Σ x ꞉ pushout , P x
    r' b = (inrr b , r b)
    G' : (c : C) → l' (f c) ＝ r' (g c)
    G' c = to-Σ-＝ (glue c , G c)

  pre-induction-comp-inrr
   : {P : pushout → 𝓣  ̇}
   → (l : (a : A) → P (inll a))
   → (r : (b : B) → P (inrr b))
   → (G : (c : C) → transport P (glue c) (l (f c)) ＝ r (g c))
   → (b : B)
   → pre-induction l r G (inrr b) ＝ (inrr b , r b)
  pre-induction-comp-inrr {_} {P} l r G = pushout-rec-comp-inrr l' r' G'
   where
    l' : A → Σ x ꞉ pushout , P x
    l' a = (inll a , l a)
    r' : B → Σ x ꞉ pushout , P x
    r' b = (inrr b , r b)
    G' : (c : C) → l' (f c) ＝ r' (g c)
    G' c = to-Σ-＝ (glue c , G c)

  pre-induction-comp-glue
   : {P : pushout → 𝓣  ̇}
   → (l : (a : A) → P (inll a))
   → (r : (b : B) → P (inrr b))
   → (G : (c : C) → transport P (glue c) (l (f c)) ＝ r (g c))
   → (c : C)
   → ap (pre-induction l r G) (glue c) ∙ pre-induction-comp-inrr l r G (g c) 
   ＝ pre-induction-comp-inll l r G (f c) ∙ to-Σ-＝ (glue c , G c)
  pre-induction-comp-glue {_} {P} l r G = pushout-rec-comp-glue l' r' G'
   where
    l' : A → Σ x ꞉ pushout , P x
    l' a = (inll a , l a)
    r' : B → Σ x ꞉ pushout , P x
    r' b = (inrr b , r b)
    G' : (c : C) → l' (f c) ＝ r' (g c)
    G' c = to-Σ-＝ (glue c , G c)

  pre-induction-id
   : {P : pushout → 𝓣  ̇}
   → (l : (a : A) → P (inll a))
   → (r : (b : B) → P (inrr b))
   → ((c : C) → transport P (glue c) (l (f c)) ＝ r (g c))
   → pushout → pushout
  pre-induction-id l r G = pr₁ ∘ pre-induction l r G

  pre-induction-id-is-id
   : {P : pushout → 𝓣  ̇}
   → (l : (a : A) → P (inll a))
   → (r : (b : B) → P (inrr b))
   → (G : (c : C) → transport P (glue c) (l (f c)) ＝ r (g c))
   → (x : pushout) → pre-induction-id l r G x ＝ x
  pre-induction-id-is-id {_} {P} l r G
   = pushout-uniqueness (pre-induction-id l r G) id
      (λ a → ap pr₁ (pre-induction-comp-inll l r G a))
       (λ b → ap pr₁ (pre-induction-comp-inrr l r G b))
        I
   where
    I : (c : C)
      → ap (pre-induction-id l r G) (glue c)
        ∙ ap pr₁ (pre-induction-comp-inrr l r G (g c))
      ＝ ap pr₁ (pre-induction-comp-inll l r G (f c)) ∙ ap id (glue c)
    I c = ap (pre-induction-id l r G) (glue c)
          ∙ ap pr₁ (pre-induction-comp-inrr l r G (g c))            ＝⟨ II ⟩
          ap pr₁ (ap (pre-induction l r G) (glue c))
          ∙ ap pr₁ (pre-induction-comp-inrr l r G (g c))            ＝⟨ III ⟩
          ap pr₁ (ap (pre-induction l r G) (glue c)
          ∙ pre-induction-comp-inrr l r G (g c))                    ＝⟨ IV ⟩
          ap pr₁ (pre-induction-comp-inll l r G (f c)
          ∙ to-Σ-＝ (glue c , G c))                                 ＝⟨ V ⟩
          ap pr₁ (pre-induction-comp-inll l r G (f c))
          ∙ ap pr₁ (to-Σ-＝ (glue c , G c))                         ＝⟨ VII ⟩
          ap pr₁ (pre-induction-comp-inll l r G (f c))
          ∙ ap id (glue c)                                          ∎
     where
      II : ap (pre-induction-id l r G) (glue c)
          ∙ ap pr₁ (pre-induction-comp-inrr l r G (g c))
        ＝ ap pr₁ (ap (pre-induction l r G) (glue c))
          ∙ ap pr₁ (pre-induction-comp-inrr l r G (g c)) 
      II = ap (_∙ ap pr₁ (pre-induction-comp-inrr l r G (g c)))
              (ap-ap (pre-induction l r G) pr₁ (glue c) ⁻¹)
      III : ap pr₁ (ap (pre-induction l r G) (glue c))
           ∙ ap pr₁ (pre-induction-comp-inrr l r G (g c))
          ＝ ap pr₁ (ap (pre-induction l r G) (glue c)
           ∙ pre-induction-comp-inrr l r G (g c))
      III = ap-∙ pr₁ (ap (pre-induction l r G) (glue c))
                 (pre-induction-comp-inrr l r G (g c)) ⁻¹
      IV : ap pr₁ (ap (pre-induction l r G) (glue c)
          ∙ pre-induction-comp-inrr l r G (g c))
         ＝ ap pr₁ (pre-induction-comp-inll l r G (f c)
          ∙ to-Σ-＝ (glue c , G c))  
      IV = ap (ap pr₁) (pre-induction-comp-glue l r G c)
      V : ap pr₁ (pre-induction-comp-inll l r G (f c)
          ∙ to-Σ-＝ (glue c , G c))
        ＝ ap pr₁ (pre-induction-comp-inll l r G (f c))
          ∙ ap pr₁ (to-Σ-＝ (glue c , G c)) 
      V = ap-∙ pr₁ (pre-induction-comp-inll l r G (f c)) (to-Σ-＝ (glue c , G c))
      VI : ap pr₁ (to-Σ-＝ (glue c , G c)) ＝ ap id (glue c) 
      VI = ap pr₁ (to-Σ-＝ (glue c , G c)) ＝⟨ ap-pr₁-to-Σ-＝ (glue c , G c) ⟩
           glue c                          ＝⟨ ap-id-is-id' (glue c) ⟩
           ap id (glue c)                  ∎
      VII : ap pr₁ (pre-induction-comp-inll l r G (f c))
           ∙ ap pr₁ (to-Σ-＝ (glue c , G c))
          ＝ ap pr₁ (pre-induction-comp-inll l r G (f c))
           ∙ ap id (glue c)   
      VII = ap (ap pr₁ (pre-induction-comp-inll l r G (f c)) ∙_) VI 

  pre-induction-family
   : {P : pushout → 𝓣  ̇}
   → (l : (a : A) → P (inll a))
   → (r : (b : B) → P (inrr b))
   → (G : (c : C) → transport P (glue c) (l (f c)) ＝ r (g c))
   → (x : pushout) → P (pre-induction-id l r G x)
  pre-induction-family l r G = pr₂ ∘ pre-induction l r G

  pre-induction-family-comp-inll
   : {P : pushout → 𝓣  ̇}
   → (l : (a : A) → P (inll a))
   → (r : (b : B) → P (inrr b))
   → (G : (c : C) → transport P (glue c) (l (f c)) ＝ r (g c))
   → (a : A)
   → transport P (pre-induction-id-is-id l r G (inll a))
                 (pre-induction-family l r G (inll a))
   ＝ l a
  pre-induction-family-comp-inll {_} {P} l r G a
   = transport (λ - → transport P - (pre-induction-family l r G (inll a)) ＝ l a)
               (I a ⁻¹) (from-Σ-＝' (pre-induction-comp-inll l r G a))
   where
    I : (a : A)
      → pre-induction-id-is-id l r G (inll a)
      ＝ ap pr₁ (pre-induction-comp-inll l r G a)
    I = pushout-uniqueness-inll (pre-induction-id l r G) id
         (λ a → ap pr₁ (pre-induction-comp-inll l r G a))
          (λ b → ap pr₁ (pre-induction-comp-inrr l r G b))
           II inll (λ a → ap pr₁ (pre-induction-comp-inll l r G a)) ∼-refl
     where
      II : (c : C)
         → ap (pre-induction-id l r G) (glue c)
          ∙ ap pr₁ (pre-induction-comp-inrr l r G (g c))
         ＝ ap pr₁ (pre-induction-comp-inll l r G (f c)) ∙ ap id (glue c)
      II c = ap (pre-induction-id l r G) (glue c)
            ∙ ap pr₁ (pre-induction-comp-inrr l r G (g c))            ＝⟨ III ⟩
             ap pr₁ (ap (pre-induction l r G) (glue c))
            ∙ ap pr₁ (pre-induction-comp-inrr l r G (g c))            ＝⟨ IV ⟩
             ap pr₁ (ap (pre-induction l r G) (glue c)
            ∙ pre-induction-comp-inrr l r G (g c))                    ＝⟨ V ⟩
             ap pr₁ (pre-induction-comp-inll l r G (f c)
            ∙ to-Σ-＝ (glue c , G c))                                 ＝⟨ VI ⟩
             ap pr₁ (pre-induction-comp-inll l r G (f c))
            ∙ ap pr₁ (to-Σ-＝ (glue c , G c))                         ＝⟨ VIII ⟩
             ap pr₁ (pre-induction-comp-inll l r G (f c))
            ∙ ap id (glue c)                                          ∎
       where
        III : ap (pre-induction-id l r G) (glue c)
             ∙ ap pr₁ (pre-induction-comp-inrr l r G (g c))
            ＝ ap pr₁ (ap (pre-induction l r G) (glue c))
             ∙ ap pr₁ (pre-induction-comp-inrr l r G (g c)) 
        III = ap (_∙ ap pr₁ (pre-induction-comp-inrr l r G (g c)))
                 (ap-ap (pre-induction l r G) pr₁ (glue c) ⁻¹)
        IV : ap pr₁ (ap (pre-induction l r G) (glue c))
             ∙ ap pr₁ (pre-induction-comp-inrr l r G (g c))
            ＝ ap pr₁ (ap (pre-induction l r G) (glue c)
             ∙ pre-induction-comp-inrr l r G (g c))
        IV = ap-∙ pr₁ (ap (pre-induction l r G) (glue c))
                      (pre-induction-comp-inrr l r G (g c)) ⁻¹
        V : ap pr₁ (ap (pre-induction l r G) (glue c)
           ∙ pre-induction-comp-inrr l r G (g c))
          ＝ ap pr₁ (pre-induction-comp-inll l r G (f c)
           ∙ to-Σ-＝ (glue c , G c))  
        V = ap (ap pr₁) (pre-induction-comp-glue l r G c)
        VI : ap pr₁ (pre-induction-comp-inll l r G (f c)
            ∙ to-Σ-＝ (glue c , G c))
           ＝ ap pr₁ (pre-induction-comp-inll l r G (f c))
            ∙ ap pr₁ (to-Σ-＝ (glue c , G c)) 
        VI = ap-∙ pr₁ (pre-induction-comp-inll l r G (f c))
                      (to-Σ-＝ (glue c , G c))
        VII : ap pr₁ (to-Σ-＝ (glue c , G c)) ＝ ap id (glue c) 
        VII = ap pr₁ (to-Σ-＝ (glue c , G c)) ＝⟨ ap-pr₁-to-Σ-＝ (glue c , G c) ⟩
              glue c                          ＝⟨ ap-id-is-id' (glue c) ⟩
              ap id (glue c)                  ∎
        VIII : ap pr₁ (pre-induction-comp-inll l r G (f c))
              ∙ ap pr₁ (to-Σ-＝ (glue c , G c))
             ＝ ap pr₁ (pre-induction-comp-inll l r G (f c))
              ∙ ap id (glue c)   
        VIII = ap (ap pr₁ (pre-induction-comp-inll l r G (f c)) ∙_) VII 

\end{code}

Now we can define the induction principle and computation rules.

!!!!!!!!!!!!! Induction computation rules depend on preinduction computation rules,
which in turn depend on uniqueness computation rules (see above) !!!!!!!!!!!!!

\begin{code}

 pushout-induction
  : {P : pushout → 𝓣  ̇}
  → Pushout-Induction-Principle pushout f g (inll , inrr , glue) P
 pushout-induction {_} {P} l r G x
  = transport P (pre-induction-id-is-id l r G x) (pre-induction-family l r G x)

 pushout-induction-comp-inll
  : {P : pushout → 𝓣  ̇}
  → Pushout-Computation-Rule₁ pushout f g (inll , inrr , glue) P pushout-induction 
 pushout-induction-comp-inll l r H a
  = pre-induction-family-comp-inll l r H a

 pushout-induction-comp-inrr
  : {P : pushout → 𝓣  ̇}
  → Pushout-Computation-Rule₂ pushout f g (inll , inrr , glue) P pushout-induction 
 pushout-induction-comp-inrr l r H b = {!!}

 pushout-induction-comp-glue
  : {P : pushout → 𝓣  ̇}
  → Pushout-Computation-Rule₃ pushout f g (inll , inrr , glue) P pushout-induction
     pushout-induction-comp-inll pushout-induction-comp-inrr
 pushout-induction-comp-glue = {!!}

\end{code}

