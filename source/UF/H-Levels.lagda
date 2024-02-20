Martin Escardo and Ian Ray, 06/02/2024

We develop H-levels (a la Voevodsky). In Homotopy Type Theory there is a
natural stratification of types defined inductively starting with contractible
types and saying the an (n+1)-type has an identity type that is an n-type.
Voevodsky introduced the notion of H-level where contractible types are at
level n = 0. Alternatively, in book HoTT, truncated types are defined so that
contractible types are at level k = -2. Of course, the two notions are
equivalent as they are indexed by equivalent types, that is ℕ ≃ ℤ₋₂, but it is
important to be aware of the fact that concepts are 'off by 2' when translating
between conventions. 

In this file we will assume function extensionality globally but not univalence.
The final result of the file will be proved in the local presence of univalence.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.Base
open import UF.Embeddings
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.Equiv-FunExt
open import UF.FunExt
open import UF.IdentitySystems
open import UF.Retracts
open import UF.Sets
open import UF.Singleton-Properties
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.Subsingletons-Properties
open import UF.Univalence
open import UF.UA-FunExt
open import Naturals.Order

module UF.H-Levels (fe : FunExt) (fe' : Fun-Ext) where

_is-of-hlevel_ : 𝓤 ̇ → ℕ → 𝓤 ̇
X is-of-hlevel zero = is-contr X
X is-of-hlevel succ n = (x x' : X) → (x ＝ x') is-of-hlevel n

hlevel-relation-is-prop : {𝓤 : Universe} (n : ℕ) (X : 𝓤 ̇ )
                        → is-prop (X is-of-hlevel n)
hlevel-relation-is-prop {𝓤} zero X = being-singleton-is-prop (fe 𝓤 𝓤)
hlevel-relation-is-prop {𝓤} (succ n) X =
  Π₂-is-prop fe'
             (λ x x' → hlevel-relation-is-prop n (x ＝ x'))

map_is-of-hlevel_ : {X : 𝓤 ̇} {Y : 𝓥 ̇} → (f : X → Y) → ℕ → 𝓤 ⊔ 𝓥 ̇
map f is-of-hlevel n = (y : codomain f) → (fiber f y) is-of-hlevel n

\end{code}

H-Levels are cumulative.

TODO: Move the following contractibility lemma to a more apropriate location.

\begin{code}

contr-lemma : {X : 𝓤 ̇} → is-contr X → (x x' : X) → is-contr (x ＝ x')
contr-lemma (c , C) x x' = (((C x)⁻¹ ∙ C x') , D)
 where
  D : is-central (x ＝ x') (C x ⁻¹ ∙ C x')
  D refl = left-inverse (C x)

hlevels-are-upper-closed : (n : ℕ) (X : 𝓤 ̇)
                         → (X is-of-hlevel n)
                         → (X is-of-hlevel succ n)
hlevels-are-upper-closed zero X h-level = contr-lemma h-level
hlevels-are-upper-closed (succ n) X h-level = step
 where
  step : (x x' : X) (p q : x ＝ x') → (p ＝ q) is-of-hlevel n
  step x x' p q = hlevels-are-upper-closed n (x ＝ x') (h-level x x') p q

id-types-are-same-hlevel : {X : 𝓤 ̇ } (n : ℕ)
                         → X is-of-hlevel n
                         → (x x' : X) → (x ＝ x') is-of-hlevel n
id-types-are-same-hlevel zero X-hlev x x' = contr-lemma X-hlev x x'
id-types-are-same-hlevel (succ n) X-hlev x x' =
  hlevels-are-upper-closed n (x ＝ x') (X-hlev x x')

\end{code}

We will now give some closure results about H-levels.

\begin{code}

hlevel-closed-under-retract : (n : ℕ)
                            → (X : 𝓤 ̇ ) (Y : 𝓥 ̇ )
                            → retract X of Y
                            → Y is-of-hlevel n
                            → X is-of-hlevel n
hlevel-closed-under-retract zero X Y X-retract-Y Y-contr =
  singleton-closed-under-retract X Y X-retract-Y Y-contr
hlevel-closed-under-retract (succ n) X Y (r , s , H) Y-h-level x x' =
  hlevel-closed-under-retract n (x ＝ x') (s x ＝ s x') retr
                              (Y-h-level (s x) (s x'))
 where
  t : (s x ＝ s x') → x ＝ x'
  t q = H x ⁻¹ ∙ ap r q ∙ H x'
  G : (p : x ＝ x') → H x ⁻¹ ∙ ap r (ap s p) ∙ H x' ＝ p
  G refl = left-inverse (H x)
  retr : retract x ＝ x' of (s x ＝ s x')
  retr = (t , ap s , G)

hlevel-closed-under-equiv : (n : ℕ)
                          → (X : 𝓤 ̇ ) (Y : 𝓥 ̇ )
                          → X ≃ Y
                          → Y is-of-hlevel n
                          → X is-of-hlevel n
hlevel-closed-under-equiv n X Y e =
  hlevel-closed-under-retract n X Y (≃-gives-◁ e)

\end{code}

We can prove closure under embeddings as a consequence of the previous result.

\begin{code}

hlevel-closed-under-embedding : (n : ℕ)
                              → 1 ≤ℕ n
                              → (X : 𝓤 ̇ ) (Y : 𝓥 ̇ )
                              → X ↪ Y
                              → Y is-of-hlevel n
                              → X is-of-hlevel n
hlevel-closed-under-embedding
  (succ n) n-above-one X Y (e , is-emb) Y-h-level x x' =
    hlevel-closed-under-equiv n (x ＝ x') (e x ＝ e x')
                              (ap e , embedding-gives-embedding' e is-emb x x')
                              (Y-h-level (e x) (e x'))

\end{code}

Using closure under equivalence we can show closure under Σ and Π.

\begin{code}

hlevel-closed-under-Σ : (n : ℕ)
                      → (X : 𝓤 ̇ ) (Y : X → 𝓤 ̇ )
                      → X is-of-hlevel n
                      → ((x : X) → (Y x) is-of-hlevel n)
                      → (Σ Y) is-of-hlevel n
hlevel-closed-under-Σ zero X Y l m = Σ-is-singleton l m
hlevel-closed-under-Σ (succ n) X Y l m (x , y) (x' , y') =
  hlevel-closed-under-equiv n ((x , y) ＝ (x' , y'))
                            (Σ p ꞉ x ＝ x' , transport Y p y ＝ y') Σ-＝-≃
                            (hlevel-closed-under-Σ n (x ＝ x')
                                                   (λ p → transport Y p y ＝ y')
                                                   (l x x')
                                                   (λ p → m x'
                                                            (transport Y p y)
                                                            y'))

hlevel-closed-under-Π : {𝓤 : Universe}
                      → (n : ℕ)
                      → (X : 𝓤 ̇ ) (Y : X → 𝓤 ̇ )
                      → ((x : X) → (Y x) is-of-hlevel n)
                      → (Π Y) is-of-hlevel n
hlevel-closed-under-Π {𝓤} zero X Y m = Π-is-singleton (fe 𝓤 𝓤) m
hlevel-closed-under-Π {𝓤} (succ n) X Y m f g =
  hlevel-closed-under-equiv n (f ＝ g) (f ∼ g) (happly-≃ (fe 𝓤 𝓤))
                            (hlevel-closed-under-Π n X (λ x → f x ＝ g x)
                                                   (λ x → m x (f x) (g x)))

\end{code}

The subuniverse of types of hlevel n is defined as follows.

\begin{code}

ℍ : ℕ → (𝓤 : Universe) → 𝓤 ⁺ ̇
ℍ n 𝓤 = Σ X ꞉ 𝓤 ̇ , X is-of-hlevel n

\end{code}

Being of hlevel one is equivalent to being a proposition.
We will quickly demonstrate this fact. 

\begin{code}

is-prop' : (X : 𝓤 ̇) → 𝓤  ̇
is-prop' X = X is-of-hlevel (succ zero)

being-prop'-is-prop : (X : 𝓤 ̇) → is-prop (is-prop' X)
being-prop'-is-prop X = hlevel-relation-is-prop (succ zero) X

is-prop-implies-is-prop' : {X : 𝓤 ̇} → is-prop X → is-prop' X
is-prop-implies-is-prop' X-is-prop x x' =
  pointed-props-are-singletons (X-is-prop x x') (props-are-sets X-is-prop)

is-prop'-implies-is-prop : {X : 𝓤 ̇} → is-prop' X → is-prop X
is-prop'-implies-is-prop X-is-prop' x x' = center (X-is-prop' x x')

is-prop-equiv-is-prop' : {𝓤 : Universe} {X :  𝓤 ̇} → is-prop X ≃ is-prop' X
is-prop-equiv-is-prop' {𝓤} {X} =
  logically-equivalent-props-are-equivalent (being-prop-is-prop (fe 𝓤 𝓤))
                                            (being-prop'-is-prop X)
                                            is-prop-implies-is-prop'
                                            is-prop'-implies-is-prop

\end{code}

From Univalence we can show that (ℍ n) is of level (n + 1), for all n : ℕ.

\begin{code}

ℍ-is-of-next-hlevel : (n : ℕ)
                    → (𝓤 : Universe)
                    → is-univalent 𝓤
                    → (ℍ n 𝓤) is-of-hlevel (succ n)
ℍ-is-of-next-hlevel zero 𝓤 ua = C
 where
  C : (X X' : ℍ zero 𝓤) → is-contr (X ＝ X')
  C (X , X-is-contr) (X' , X'-is-contr) =
    hlevel-closed-under-equiv zero ((X , X-is-contr) ＝ (X' , X'-is-contr))
                              (X ≃ X') e C'
   where
    e = ((X , X-is-contr) ＝ (X' , X'-is-contr)) ≃⟨ ≃-sym (to-subtype-＝-≃
                                                  (λ X → being-singleton-is-prop
                                                         (fe 𝓤 𝓤))) ⟩
        (X ＝ X')                                ≃⟨ univalence-≃ ua X X' ⟩
        (X ≃ X')                                 ■
    P : is-prop (X ≃ X')
    P = ≃-is-prop fe (is-prop'-implies-is-prop
                        (hlevels-are-upper-closed zero X' X'-is-contr))
    C' : is-contr (X ≃ X')
    C' = pointed-props-are-singletons (singleton-≃ X-is-contr X'-is-contr) P
ℍ-is-of-next-hlevel (succ n) 𝓤 ua (X , l) (X' , l') =
  hlevel-closed-under-equiv (succ n) ((X , l) ＝ (X' , l')) (X ≃ X') e
      (hlevel-closed-under-embedding (succ n) ⋆ (X ≃ X') (X → X') e'
                                     (hlevel-closed-under-Π (succ n) X
                                                            (λ _ → X')
                                                            (λ x x' → l' x')))
  where
   e = ((X , l) ＝ (X' , l')) ≃⟨ ≃-sym (to-subtype-＝-≃
                                  (λ _ → Π-is-prop (fe 𝓤 𝓤)
                                  (λ x → Π-is-prop (fe 𝓤 𝓤)
                                  (λ x' → hlevel-relation-is-prop
                                            n (x ＝ x'))))) ⟩
       (X ＝ X')              ≃⟨ univalence-≃ ua X X' ⟩
       (X ≃ X')               ■

   e' : (X ≃ X') ↪ (X → X')
   e' = (pr₁ , pr₁-is-embedding (λ f → being-equiv-is-prop fe f))

\end{code}

We now define the notion of a k-truncation using record types.

\begin{code}

record H-level-truncations-exist : 𝓤ω where
 field
  ∣∣_∣∣_ : {𝓤 : Universe} → 𝓤 ̇ → ℕ → 𝓤 ̇
  ∣∣∣∣-is-hlevel : {𝓤 : Universe} {X : 𝓤 ̇ } {n : ℕ}
                 → (∣∣ X ∣∣ n) is-of-hlevel n
  ∣_∣_ :  {𝓤 : Universe} {X : 𝓤 ̇ } → X → (n : ℕ) → ∣∣ X ∣∣ n
  ∣∣∣∣-induction : {𝓤 𝓥 : Universe} {X : 𝓤 ̇ } {n : ℕ}
                 → (P : ∣∣ X ∣∣ n → 𝓥 ̇ )
                 → ((s : ∣∣ X ∣∣ n) → (P s) is-of-hlevel n)
                 → ((x : X) → P (∣ x ∣ n))
                 → (s : ∣∣ X ∣∣ n) → P s
  ∣∣∣∣-comp-ind : {𝓤 𝓥 : Universe} {X : 𝓤 ̇ } {n : ℕ}
                → (P : ∣∣ X ∣∣ n → 𝓥 ̇ )
                → (h-lev : (s : ∣∣ X ∣∣ n) → (P s) is-of-hlevel n)
                → (f : (x : X) → P (∣ x ∣ n))
                → (x : X)
                → ∣∣∣∣-induction P h-lev f (∣ x ∣ n) ＝ f x
 infix 0 ∣∣_∣∣_
 infix 0 ∣_∣_

module truncation-properties (te : H-level-truncations-exist) where

 open H-level-truncations-exist te

 ∣∣∣∣-rec : {𝓤 𝓥 : Universe} {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {n : ℕ}
          → Y is-of-hlevel n → (X → Y) → ∣∣ X ∣∣ n → Y
 ∣∣∣∣-rec {𝓤} {𝓥} {X} {Y} {n} H-lev f s =
   ∣∣∣∣-induction (λ _ → Y) (λ _ → H-lev) f s

 ∣∣∣∣-uniqueness : {𝓤 𝓥 : Universe} {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {n : ℕ}
                 → Y is-of-hlevel n
                 → (f g : ∣∣ X ∣∣ n → Y)
                 → ((x : X) → f (∣ x ∣ n) ＝ g (∣ x ∣ n))
                 → (s : ∣∣ X ∣∣ n) → f s ＝ g s
 ∣∣∣∣-uniqueness {𝓤} {𝓥} {X} {Y} {n} Y-h-lev f g H =
   ∣∣∣∣-induction (λ s → f s ＝ g s)
                  (λ s → id-types-are-same-hlevel n Y-h-lev (f s) (g s)) H

 ∣∣∣∣-comp-rec : {𝓤 𝓥 : Universe} {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {n : ℕ}
               → (Y-h-lev : Y is-of-hlevel n)
               → (f : (X → Y))
               → (x : X)
               → ∣∣∣∣-rec Y-h-lev f (∣ x ∣ n) ＝ f x
 ∣∣∣∣-comp-rec {𝓤} {𝓥} {X} {Y} {n} Y-h-lev f x =
   ∣∣∣∣-comp-ind (λ _ → Y) (λ _ → Y-h-lev) f x 

 zero-hlevel-is-contr : {X : 𝓤 ̇ } → is-contr (∣∣ X ∣∣ zero)
 zero-hlevel-is-contr = ∣∣∣∣-is-hlevel

 one-hlevel-is-prop : {X : 𝓤 ̇ } → is-prop (∣∣ X ∣∣ succ zero)
 one-hlevel-is-prop = is-prop'-implies-is-prop ∣∣∣∣-is-hlevel

 two-hlevel-is-set : {X : 𝓤 ̇ } → is-set (∣∣ X ∣∣ succ (succ zero))
 two-hlevel-is-set {𝓤} {X} {x} {y} =
   is-prop'-implies-is-prop (∣∣∣∣-is-hlevel x y)

 canonical-pred-map : {X : 𝓤 ̇} {n : ℕ}
                    → ∣∣ X ∣∣ succ n → ∣∣ X ∣∣ n
 canonical-pred-map {𝓤} {X} {n} x =
        ∣∣∣∣-rec (hlevels-are-upper-closed n (∣∣ X ∣∣ n) ∣∣∣∣-is-hlevel)
                 (λ x → ∣ x ∣ n) x

 canonical-pred-map-comp : {X : 𝓤 ̇} {n : ℕ} (x : X)
                         → canonical-pred-map (∣ x ∣ succ n) ＝ (∣ x ∣ n)
 canonical-pred-map-comp {𝓤} {X} {n} x =
   ∣∣∣∣-comp-rec (hlevels-are-upper-closed n (∣∣ X ∣∣ n) ∣∣∣∣-is-hlevel)
                 (λ _ → ∣ _ ∣ n) x

 truncation-closed-under-equiv : {𝓤 𝓥 : Universe}
                               → (n : ℕ)
                               → (X : 𝓤 ̇ ) (Y : 𝓥 ̇ )
                               → X ≃ Y
                               → (∣∣ X ∣∣ n) ≃ (∣∣ Y ∣∣ n)
 truncation-closed-under-equiv n X Y e = (f , (b , G) , (b , H))
  where
   f : ∣∣ X ∣∣ n → ∣∣ Y ∣∣ n
   f = ∣∣∣∣-rec ∣∣∣∣-is-hlevel (λ x → ∣ (⌜ e ⌝ x) ∣ n)
   b : ∣∣ Y ∣∣ n → ∣∣ X ∣∣ n
   b = ∣∣∣∣-rec ∣∣∣∣-is-hlevel (λ y → ∣ (⌜ e ⌝⁻¹ y) ∣ n)
   H : b ∘ f ∼ id
   H = ∣∣∣∣-induction (λ s → b (f s) ＝ s)
                      (λ s → id-types-are-same-hlevel n ∣∣∣∣-is-hlevel
                                                      (b (f s)) s)
                      H'
    where
     H' : (x : X) → b (f (∣ x ∣ n)) ＝ (∣ x ∣ n)
     H' x = b (f (∣ x ∣ n))           ＝⟨ ap b (∣∣∣∣-comp-rec ∣∣∣∣-is-hlevel
                                               (λ x → ∣ (⌜ e ⌝ x) ∣ n) x) ⟩
            b (∣ ⌜ e ⌝ x ∣ n)         ＝⟨ ∣∣∣∣-comp-rec ∣∣∣∣-is-hlevel
                                               (λ y → ∣ (⌜ e ⌝⁻¹ y) ∣ n)
                                               (⌜ e ⌝ x) ⟩
            (∣ ⌜ e ⌝⁻¹ (⌜ e ⌝ x) ∣ n) ＝⟨ ap (λ x → ∣ x ∣ n)
                                             (inverses-are-retractions' e x) ⟩
            (∣ x ∣ n)                 ∎ 
   G : f ∘ b ∼ id
   G = ∣∣∣∣-induction (λ s → f (b s) ＝ s)
                      (λ s → id-types-are-same-hlevel n ∣∣∣∣-is-hlevel
                                                      (f (b s)) s)
                      G'
    where
     G' : (y : Y) → f (b (∣ y ∣ n)) ＝ (∣ y ∣ n)
     G' y = f (b (∣ y ∣ n))           ＝⟨ ap f (∣∣∣∣-comp-rec ∣∣∣∣-is-hlevel
                                               (λ y → ∣ (⌜ e ⌝⁻¹ y) ∣ n) y) ⟩
            f (∣ (⌜ e ⌝⁻¹ y) ∣ n)     ＝⟨ ∣∣∣∣-comp-rec ∣∣∣∣-is-hlevel
                                            (λ x → ∣ ⌜ e ⌝ x ∣ n) (⌜ e ⌝⁻¹ y) ⟩
            (∣ ⌜ e ⌝ (⌜ e ⌝⁻¹ y) ∣ n) ＝⟨ ap (λ y → ∣ y ∣ n)
                                            (inverses-are-sections' e y) ⟩
            (∣ y ∣ n)                 ∎ 

 succesive-truncations-equiv : (X : 𝓤 ̇) (n : ℕ)
                             → (∣∣ X ∣∣ n) ≃ (∣∣ (∣∣ X ∣∣ succ n) ∣∣ n)
 succesive-truncations-equiv X n = (f , (b , G) , (b , H))
  where
   f : (∣∣ X ∣∣ n) → (∣∣ (∣∣ X ∣∣ succ n) ∣∣ n)
   f = ∣∣∣∣-rec ∣∣∣∣-is-hlevel (λ x → ∣ ∣ x ∣ succ n ∣ n)
   b : (∣∣ (∣∣ X ∣∣ succ n) ∣∣ n) → (∣∣ X ∣∣ n)
   b = ∣∣∣∣-rec ∣∣∣∣-is-hlevel (canonical-pred-map)
   G : f ∘ b ∼ id
   G = ∣∣∣∣-induction (λ s → f ( b s) ＝ s)
                      (λ s → id-types-are-same-hlevel n ∣∣∣∣-is-hlevel
                                                      (f (b s)) s)
                      (∣∣∣∣-induction (λ t → f (b (∣ t ∣ n)) ＝ (∣ t ∣ n))
                                      (λ t → id-types-are-same-hlevel n
                                              (id-types-are-same-hlevel n
                                               ∣∣∣∣-is-hlevel (f (b (∣ t ∣ n)))
                                                               ((∣ t ∣ n))))
                                      G')
    where
     G' : (x : X) → f (b (∣ ∣ x ∣ succ n ∣ n)) ＝ (∣ ∣ x ∣ succ n ∣ n)
     G' x = f (b (∣ ∣ x ∣ succ n ∣ n))            ＝⟨ ap f (∣∣∣∣-comp-rec
                                                         ∣∣∣∣-is-hlevel
                                                         canonical-pred-map
                                                         (∣ x ∣ succ n)) ⟩
            f (canonical-pred-map (∣ x ∣ succ n)) ＝⟨ ap f
                                                   (canonical-pred-map-comp x) ⟩
            f (∣ x ∣ n)                           ＝⟨ ∣∣∣∣-comp-rec
                                                      ∣∣∣∣-is-hlevel
                                                      (λ x → ∣ ∣ x ∣ succ n ∣ n)
                                                      x ⟩
            (∣ ∣ x ∣ succ n ∣ n)                  ∎
   H : b ∘ f ∼ id
   H = ∣∣∣∣-induction (λ s → b (f s) ＝ s)
                      (λ s → id-types-are-same-hlevel n ∣∣∣∣-is-hlevel
                                                      (b (f s)) s)
                      H'
    where
     H' : (x : X) → b (f (∣ x ∣ n)) ＝ (∣ x ∣ n)
     H' x = b (f (∣ x ∣ n))             ＝⟨ ap b (∣∣∣∣-comp-rec ∣∣∣∣-is-hlevel
                                              (λ x → ∣ ∣ x ∣ succ n ∣ n) x) ⟩
            b (∣ ∣ x ∣ succ n ∣ n)      ＝⟨ ∣∣∣∣-comp-rec ∣∣∣∣-is-hlevel
                                            canonical-pred-map (∣ x ∣ succ n) ⟩
            canonical-pred-map (∣ x ∣ succ n) ＝⟨ canonical-pred-map-comp x ⟩
            (∣ x ∣ n)                         ∎
   

\end{code}

We now define the notion of k-connectedness for types and functions with respect
to H-levels. We will then see that connectedness as defined elsewhere is a
special case:
Connectedness typically means set connectedness. In terms of H-levels defined
here it will mean 2-connectedness.

\begin{code}

module k-connectedness (te : H-level-truncations-exist) where

 open H-level-truncations-exist te
 open truncation-properties te

 _is_connected : 𝓤 ̇ → ℕ → 𝓤 ̇
 X is k connected = is-contr (∣∣ X ∣∣ k)

 map_is_connected : {X : 𝓤 ̇} {Y : 𝓥 ̇} → (f : X → Y) → ℕ → 𝓤 ⊔ 𝓥 ̇
 map f is k connected = (y : codomain f) → (fiber f y) is k connected

 connectedness-closed-under-equiv : {𝓤 𝓥 : Universe}
                                  → (k : ℕ)
                                  → (X : 𝓤 ̇ ) (Y : 𝓥 ̇ )
                                  → X ≃ Y
                                  → Y is k connected
                                  → X is k connected
 connectedness-closed-under-equiv k X Y e Y-con =
   equiv-to-singleton (truncation-closed-under-equiv k X Y e) Y-con

 contractible-types-are-connected : {𝓤 : Universe}
                                  → (X : 𝓤 ̇ )
                                  → is-contr X
                                  → (n : ℕ)
                                  → X is n connected
 contractible-types-are-connected X (c , C) n = ((∣ c ∣ n) , C')
  where
   C' : (s : ∣∣ X ∣∣ n) → (∣ c ∣ n) ＝ s
   C' = ∣∣∣∣-induction (λ s → (∣ c ∣ n) ＝ s)
                       (id-types-are-same-hlevel n ∣∣∣∣-is-hlevel (∣ c ∣ n))
                       (λ x → ap (λ x → ∣ x ∣ n) (C x))

 connectedness-is-lower-closed : (X : 𝓤 ̇) (k : ℕ)
                               → X is (succ k) connected
                               → X is k connected
 connectedness-is-lower-closed X k X-succ-con =
   equiv-to-singleton (succesive-truncations-equiv X k)
                      (contractible-types-are-connected (∣∣ X ∣∣ succ k)
                                                        X-succ-con k)

\end{code}
