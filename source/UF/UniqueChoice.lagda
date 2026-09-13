Ian Ray, 24 October 2025.

We prove the principle of unique choice in the presence of function
extensionality.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module UF.UniqueChoice where

open import MLTT.Spartan
open import UF.Equiv
open import UF.FunExt
open import UF.Hedberg
open import UF.ImageAndSurjection
open import UF.PropTrunc
open import UF.Sets
open import UF.Sets-Properties
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.Subsingletons-Properties
open import UF.SubtypeClassifier

\end{code}

TypeTopology has a clever formulation of unique existence but we show it is
equivalent to a more niave notion using propositional truncation when the
family is propositional and function extensionality is assumed.

\begin{code}

module unique-existence (pt : propositional-truncations-exist) where

 open PropositionalTruncation pt

 ∃!-implies-∃ : {X : 𝓤 ̇ } {A : X → 𝓥 ̇}
              → ∃! A → ∃ A
 ∃!-implies-∃ (c , C) = ∣ c ∣

 ∃'! : {X : 𝓤 ̇ }
     → (A : X → 𝓥 ̇)
     → 𝓤 ⊔ 𝓥 ̇
 ∃'! {_} {_} {X} A = ∥ Σ x ꞉ X , (A x × ((x' : X) → A x' → x ＝ x')) ∥

 existsUnique' : (X : 𝓤 ̇ ) (A : X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
 existsUnique' X A = ∃'! A

 syntax existsUnique' X (λ x → b) = ∃'! x ꞉ X , b

 ∃'!-is-prop : {X : 𝓤 ̇ } {A : X → 𝓥 ̇} 
             → is-prop (∃'! A)
 ∃'!-is-prop {_} {_} {_} {_} = ∥∥-is-prop

\end{code}

We now show that the two notions of unique existence are equivalent.

\begin{code}

 ∃!-to-∃'! : {X : 𝓤 ̇ } {A : X → 𝓥 ̇}
           → ∃! A → ∃'! A 
 ∃!-to-∃'! {_} {_} {_} {A} s
  = ∣ ∃!-witness s , ∃!-is-witness s ,
       (λ x' Ax' → ap pr₁ (∃!-uniqueness s x' Ax')) ∣

 ∃'!-to-∃! : {X : 𝓤 ̇ } {A : X → 𝓥 ̇} (p : (x : X) → is-prop (A x))
           → Fun-Ext
           → ∃'! A → ∃! A
 ∃'!-to-∃! {_} {_} {X} {A} p fe
  = ∥∥-rec (being-singleton-is-prop fe) I 
  where
   I : Σ x ꞉ X , (A x × ((x' : X) → A x' → x ＝ x')) → ∃! A
   I (x , a , u) = ((x , a) , II)
    where
     II : is-central (Σ A) (x , a)
     II (x' , a') = to-subtype-＝ p (u x' a')

 ∃!-≃-∃'! : {X : 𝓤 ̇ } {A : X → 𝓥 ̇} (p : (x : X) → is-prop (A x))
          → Fun-Ext
          → ∃! A ≃ ∃'! A
 ∃!-≃-∃'! p fe
  = logically-equivalent-props-are-equivalent (being-singleton-is-prop fe)
     ∃'!-is-prop ∃!-to-∃'! (∃'!-to-∃! p fe)

\end{code}

We establish an analog of the "set-theoretic principle of unique choice" from
ONLY function extensionality (notably with no use of propositional truncation).

\begin{code}

PUC : (X : 𝓤 ̇) (Y : 𝓥 ̇) (R : X → Y → 𝓣 ̇) (p : (x : X) (y : Y) → is-prop (R x y))
    → 𝓤 ⊔ 𝓥 ⊔ 𝓣 ̇
PUC X Y R p
 = ((x : X) → ∃! y ꞉ Y , R x y) → ∃! f ꞉ (X → Y) , ((x : X) → R x (f x))

puc : {X : 𝓤 ̇} {Y : 𝓥 ̇} {R : X → Y → 𝓣 ̇} {p : (x : X) (y : Y) → is-prop (R x y)}
    → Fun-Ext
    → PUC X Y R p
puc {_} {_} {_} {X} {Y} {R} {p} fe m = ((f , r) , G)
 where
  f : X → Y
  f x = ∃!-witness (m x)
  r : (x : X) → R x (f x)
  r x = ∃!-is-witness (m x)
  C : (x : X) (y : Y) (a : R x y) → (f x , r x) ＝ (y , a)
  C x = ∃!-uniqueness (m x)
  G : ((g , s) : (Σ g ꞉ (X → Y) , ((x : X) → R x (g x))))
    → (f , r) ＝ (g , s)
  G (g , s) = to-subtype-＝ II (dfunext fe I)
   where
    I : f ∼ g
    I x = ap pr₁ (C x (g x) (s x))
    II : (h : X → Y) → is-prop ((x : X) → R x (h x))
    II = λ h → Π-is-prop fe (λ x → p x (h x))
    
\end{code}

Evidently a version of unique choice is true in MLTT + FunExt. But as we saw in
the previous section this version is stable under the addition of propositional
truncation since any sensible version of unique existence will be equivalent to
∃!. Thus, in a very precise sense we can simply say MLTT + FunExt satsifies
unique choice, with no qualificaiton.

---------------------------------------------------------------------------

This is a work in progress related to a note on the subtlety of unique
existence and unique choice.

We now record for completeness that unique choice stated in terms of ∃'! is
directly provable only(?) when Y is a set.

For this we first record the set recursion principle for propositional
truncation due to Kraus et al.

\begin{code}

module _ (pt : propositional-truncations-exist) where

 open PropositionalTruncation pt
 open unique-existence pt

 ∥∥-set-rec : {X : 𝓤 ̇}
              (Y : 𝓥 ̇) (Y-set : is-set Y) (f : X → Y)
            → wconstant f
            → ∥ X ∥ → Y
 ∥∥-set-rec Y Y-set f wcons
  = pr₁ (wconstant-map-to-set-factors-through-truncation-of-domain
          pt Y-set f wcons)

 ∥∥-set-rec-comp : {X : 𝓤 ̇}
                   (Y : 𝓥 ̇) (Y-set : is-set Y) (f : X → Y)
                 → (wcons : wconstant f)
                 → (x : X)
                 → f x ＝ ∥∥-set-rec Y Y-set f wcons ∣ x ∣
 ∥∥-set-rec-comp Y Y-set f wcons
  = pr₂ (wconstant-map-to-set-factors-through-truncation-of-domain
          pt Y-set f wcons)

 ∥∥-set-rec-char : {X : 𝓤 ̇}
                   {Y : 𝓥 ̇} {Y-set : is-set Y} {f : X → Y}
                 → (wcons : wconstant f)
                 → (x : X) (w : ∥ X ∥)
                 → f x ＝ ∥∥-set-rec Y Y-set f wcons w
 ∥∥-set-rec-char {_} {_} {_} {Y} {Y-set} {f} wcons x w
  = f x                              ＝⟨ ∥∥-set-rec-comp Y Y-set f wcons x ⟩
    ∥∥-set-rec Y Y-set f wcons ∣ x ∣ ＝⟨ ap (∥∥-set-rec Y Y-set f wcons)
                                            (∥∥-is-prop ∣ x ∣ w) ⟩
    ∥∥-set-rec Y Y-set f wcons w     ∎ 

 PUC' : (X : 𝓤 ̇) (Y : 𝓥 ̇) (Y-set : is-set Y) (R : X → Y → 𝓣 ̇)
        (p : (x : X) (y : Y) → is-prop (R x y))
      → 𝓤 ⊔ 𝓥 ⊔ 𝓣 ̇
 PUC' X Y Y-set R p
  = ((x : X) → ∃'! y ꞉ Y , R x y) → ∃'! f ꞉ (X → Y) , ((x : X) → R x (f x))

 puc' : {X : 𝓤 ̇} {Y : 𝓥 ̇} {Y-set : is-set Y} {R : X → Y → 𝓣 ̇}
        {p : (x : X) (y : Y) → is-prop (R x y)}
      → Fun-Ext
      → PUC' X Y Y-set R p
 puc' {𝓤} {𝓥} {𝓣} {X} {Y} {Y-set} {R} {p} fe m
  = ∣ f , Rxfx , f-unique ∣
  where
   un-trunc-source : (x : X) → 𝓥 ⊔ 𝓣 ̇
   un-trunc-source x = (Σ y ꞉ Y , R x y × ((y' : Y) → R x y' → y ＝ y'))
   proj₁ : (x : X)
         → un-trunc-source x
         → Y
   proj₁ x (y , r , u) = y
   proj₁-wconst : (x : X) → wconstant (proj₁ x)
   proj₁-wconst x (y , r , u) (y' , r' , u') = u y' r'
   f : X → Y
   f x = ∥∥-set-rec Y Y-set (proj₁ x) (proj₁-wconst x) (m x)
   Rxfx : (x : X) → R x (f x)
   Rxfx x = ∥∥-rec (p x (f x)) I (m x)
    where
     I : un-trunc-source x
       → R x (f x)
     I (y , r , u)
      = transport (R x) (∥∥-set-rec-char (proj₁-wconst x) (y , r , u) (m x)) r
   f-unique : (g : X → Y) → ((x : X) → R x (g x)) → f ＝ g
   f-unique g Rxgx = dfunext fe (λ x → ∥∥-rec Y-set (I x) (m x))
    where
     I : (x : X)
       → un-trunc-source x
       → f x ＝ g x
     I x (y , r , u)
      = f x  ＝⟨ ∥∥-set-rec-char (proj₁-wconst x) (y , r , u) (m x) ⁻¹ ⟩
        y    ＝⟨ u (g x) (Rxgx x) ⟩
        g x  ∎
   
\end{code}
