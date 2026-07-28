Ian Ray. July 21st 2026.

This is a explicit account of colimits but we should consider an approach
that uses natural transformations or something more sophisticated...

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import Categories.Functor
open import Categories.Functor-Composition
open import Categories.Pre
open import Categories.Wild
open import Categories.Notation.Functor
open import Categories.Notation.Pre
open import Categories.Notation.Wild

module Categories.Colimits where

\end{code}

We start by defining a cocone on a given diagram D : X → Y, which consists of
an object y : obj Y

\begin{code}

module _ {X : Precategory 𝓤 𝓥} {Y : Precategory 𝓦 𝓣} (D : Functor X Y)
       where

 open PrecategoryNotation X
 open PrecategoryNotation Y

 record cocone : 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓣 ̇ where
  field
   appex : obj Y
   compo : (x : obj X) → hom (Functor.F₀ D x) appex
   commu : (x x' : obj X) (f : hom x x')
         → compo x' ◦ Functor.F₁ D f ＝ compo x

 module _ (c : cocone) where

  record is-colim : 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓣 ̇ where
   field
    universal : (x : obj X) (C : cocone)
              → hom (cocone.appex c) (cocone.appex C)
    universal-commu : (x : obj X) (C : cocone)
                    → universal x C ◦ cocone.compo c x ＝ cocone.compo C x
    unique : (x : obj X) (C : cocone)
           → (m : hom (cocone.appex c) (cocone.appex C))
           → m ◦ cocone.compo c x ＝ cocone.compo C x
           → universal x C ＝ m

 Colim : 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓣 ̇
 Colim = Σ c ꞉ cocone , is-colim c

\end{code}

We will give some boilerplate naming for all the fields and projections.

\begin{code}

 module _ (𝓒@(c , u) : Colim) where
 
  colim : obj Y
  colim = cocone.appex c

  colim-component : (x : obj X) → hom (Functor.F₀ D x) colim
  colim-component = cocone.compo c

  colim-commutes : (x x' : obj X) (f : hom x x')
                 → colim-component x' ◦ Functor.F₁ D f ＝ colim-component x
  colim-commutes = cocone.commu c

  colim-universal : (x : obj X) (C : cocone)
                  → hom colim (cocone.appex C)
  colim-universal = is-colim.universal u
  
  colim-universal-commutes
   : (x : obj X) (C : cocone)
   → colim-universal x C ◦ colim-component x ＝ cocone.compo C x
  colim-universal-commutes = is-colim.universal-commu u

  colim-unique : (x : obj X) (C : cocone)
               → (m : hom colim (cocone.appex C))
               → m ◦ colim-component x ＝ cocone.compo C x
               → colim-universal x C ＝ m
  colim-unique = is-colim.unique u

\end{code}

We define a cocomplete category with respect to the universes for which
it has colimits.

\begin{code}

module _ (P : Precategory 𝓤 𝓥) where

 has-colimits : (𝓣 𝓦 : Universe) → 𝓤 ⊔ 𝓥 ⊔ (𝓣 ⊔ 𝓦)⁺ ̇
 has-colimits 𝓣 𝓦 = {C : Precategory 𝓣 𝓦} (D : Functor C P)
                  → Colim D

module _ {𝓤 𝓥 : Universe} where

 Cocomplete-Category : (𝓣 𝓦 : Universe) → (𝓤 ⊔ 𝓥 ⊔ 𝓣 ⊔ 𝓦)⁺ ̇
 Cocomplete-Category 𝓣 𝓦 = Σ P ꞉ Precategory 𝓤 𝓥 , has-colimits P 𝓣 𝓦

\end{code}

We now give define some important interactions between colimits and functors.

\begin{code}

module _ {C : Precategory 𝓦 𝓣}
         {X : Precategory 𝓤 𝓥}
         {Y : Precategory 𝓤' 𝓥'}
         {𝓓 : Functor C X}
       where

 open PrecategoryNotation C
 open PrecategoryNotation X
 open PrecategoryNotation Y

 cocone-on : (𝓕 : Functor X Y) (c : Colim 𝓓) → cocone (𝓕 F∘ 𝓓)
 cocone-on 𝓕 c = record{appex = F (colim 𝓓 c) ;
                        compo = I ;
                        commu = II }
  where
   open FunctorNotation 𝓕 renaming (functor-map to F)
   open FunctorNotation 𝓓 renaming (functor-map to D)

   I : (x : obj C) → hom (Functor.F₀ (𝓕 F∘ 𝓓) x) (F (colim 𝓓 c))
   I x = F (colim-component 𝓓 c x) 
   II : (x x' : obj C) (f : hom x x')
      → F (colim-component 𝓓 c x') ◦ F (D f) ＝ F (colim-component 𝓓 c x)
   II x x' f = F (colim-component 𝓓 c x') ◦ F (D f) ＝⟨ III ⟩
               F (colim-component 𝓓 c x' ◦ D f)     ＝⟨ IV ⟩
               F (colim-component 𝓓 c x)            ∎
    where
     III = Functor.distributivity 𝓕 (colim-component 𝓓 c x') (D f) ⁻¹
     IV = ap F (colim-commutes 𝓓 c x x' f)
     
 _preserves_ : (𝓕 : Functor X Y) (c : Colim 𝓓) → 𝓦 ⊔ 𝓣 ⊔ 𝓤' ⊔ 𝓥' ̇
 𝓕 preserves c = is-colim (𝓕 F∘ 𝓓) (cocone-on 𝓕 c)

\end{code}


