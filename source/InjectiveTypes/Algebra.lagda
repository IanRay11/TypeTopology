Martin Escardo, 22nd October 2024 - June 2025

WARNING. This file has one gap.

This file is work in progress and aims to eventually subsume the file
gist.InjectivesVersusAlgebras (at which point that file will be deleted).

We give conditions on algebraic injective structure on a type so that
it coincides with the algebraic structure for the partial-map
classifier (aka lifting) monad 𝓛 on types.

We call these conditions "associativity" and "pullback naturality".

Associativity says that an extension (f|j)|k of an extension f|j is
the extension f|(k∘j) along the composition of the embeddings j and k,
as in the following commutative diagram.


                   j         k
              X ──────→ Y ──────→ Z
               ╲        │        ╱
                ╲       │       ╱
             f   ╲      │ f|j  ╱ (f|j)|k = f(k∘j
                  ╲     │     ╱
                   ╲    │    ╱
                    ╲   │   ╱
                     ➘  ↓  ↙
                        D

Pullback naturality is expressed by the following diagram, where the
square is a pullback and j (and hence k) is an embedding.

                   k
              A ──────→ B
              │ ⌟       │
           g  │         │ h
              │         │
              ↓    j    ↓
              X ──────→ Y
               ╲        │
                ╲       │
             f   ╲      │ f|j ∘ h = (f ∘ g) | k
                  ╲     │
                   ╲    │
                    ╲   │
                     ➘  ↓
                        D

It actually suffices to consider pullbacks of the form


        fiber j y ────→ 𝟙
              │ ⌟       │
              │         │ y
              │         │
              ↓    j    ↓
              X ──────→ Y

This is a sense in which extensions are pointwise.

One may wonder whether it is reasonable to consider naturality with
respect to all commutative squares

                   k
              A ──────→ B
              │         │
           g  │         │ h
              │         │
              ↓    j    ↓
              X ──────→ Y

where j and k are embeddings, but which are not necessarily
pullbacks. However, a counter-example is the commutative square


              𝟘 ──────→ 𝟙
              │         │
              │         │
              │         │
              ↓         ↓
              𝟙 ──────→ 𝟙

Now, an algebra α : 𝓛 D → D of the lifting monad amounts flabbiness
structure plus an associativity law on this structure. Via the
canonical correspondence between algebraic injective structure and
algebraic flabby structure, the above associativity condition
corresponds to the associativity law for 𝓛-algebras (which justifies
our terminology in the case of injectivity). In terms of flabbinnes,
this says that if we have a situation

            P × Q ────→ 𝟙
               ╲        │
                ╲       │
             f   ╲      │
                  ╲     │
                   ╲    │
                    ╲   │
                     ➘  ↓
                        D

where P and Q propositions, so that also P × Q is a proposition, then
we can

 1. extend f at once, or
 2. extend f in its first variable and then in its second variable,

and these two processes give the same result.

As for pullback naturality, it is given automatically by the canonical
construction of algebraic injectivity data from algebraic flabiness
data.

If we define homomorphisms h : D → E of algebraic injectives in the
obvious way, namely, that for any f : X → D and j : X ↪ Y we have that

    h ∘ f ∣ j = (h ∘ f) ∣ j

as (partially) illustrated by the (incomplete, due to typographical
reasons) diagram

                   j
              X ───────→ Y
               ╲       ╱
                ╲     ╱
               f ╲   ╱ f/j
                  ➘ ↙
                   D
                   │
                   │ h
                   ↓
                   E

then injective homomorphisms correspond to 𝓛-homomorphisms.

When we restrict to types that are sets, we get that the category of
associative, pullback-natural algebraically injective objects is
isomorphic to the category of 𝓛-algebras.

This result holds for the objects of any 1-topos, due to our
constructive reasoning in a restricted type theory.

However, at the moment we don't have a result for ∞-toposes, because,
although the associativity, pullback naturality and the algebra
equations are all property for sets, they are data, and we have proved
only a logical equivalence of associativity + pullback-naturality and
the 𝓛-algebra equations, rather than a full type equivalence (whose
possibility we are currently investigating).

\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import MLTT.Spartan
open import UF.FunExt

module InjectiveTypes.Algebra
        (gap : {𝓤 : Universe} {X : 𝓤 ̇} → X) -- WARNING. This file has gaps.
        {𝓦 : Universe}
        (D : 𝓦 ̇ )
        (fe : FunExt)
       where

fe' : Fun-Ext
fe' {𝓤} {𝓥} = fe 𝓤 𝓥

open import InjectiveTypes.Repackaging
open import Lifting.Algebras hiding (is-hom)
open import UF.Base
open import UF.Embeddings renaming (_∘↪_ to _⊚_)
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.Pullback
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.SubtypeClassifier
open import UF.Univalence

\end{code}

Definition of algebraic injective homomorphisms.

\begin{code}

module _
        {𝓤 𝓥 𝓣 : Universe}
        (E : 𝓣 ̇ )
        ((_∣ᴰ_ , _) : injective-structure D 𝓤 𝓥)
        ((_∣ᴱ_ , _) : injective-structure E 𝓤 𝓥)
       where

 is-hom : (D → E) → 𝓥 ⁺ ⊔ 𝓤 ⁺ ⊔ 𝓦 ⊔ 𝓣 ̇
 is-hom h = {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → D) (𝕛 : X ↪ Y)
          → h ∘ f ∣ᴰ 𝕛 ∼ (h ∘ f) ∣ᴱ 𝕛

\end{code}

Definitions of associativity and pullback naturality for injectivity structure.

\begin{code}

module _
        {𝓤 : Universe}
        ((_∣_ , _) : injective-structure D 𝓤 𝓤)
       where

 injective-associativity : 𝓦 ⊔ 𝓤 ⁺ ̇
 injective-associativity = {X Y Z : 𝓤 ̇ } (f : X → D) (𝕛 : X ↪ Y) (𝕜 : Y ↪ Z)
               → f ∣ (𝕜 ⊚ 𝕛) ∼ (f ∣ 𝕛) ∣ 𝕜

\end{code}

For the following definition, we consider the standard pullback

                   pb₂
    pullback j h ─────→ B
              │ ⌟       │
          pb₁ │         │ h
              │         │
              ↓     j   ↓
              X ──────→ Y

where pullback j h := Σ (x , y) ꞉ X × B , j x ＝ h y and pb₁ and pb₂
are the projections, rather than an abstract pullback, for simplicity,
so that the above naturality condition becomes

                   pb₂
    pullback j h ─────→ B
              │ ⌟       │
          pb₁ │         │ h
              │         │
              ↓     j   ↓
              X ──────→ Y
               ╲        │
                ╲       │
             f   ╲      │ (f | j) ∘ h = (f ∘ pb₁) | pb₂
                  ╲     │
                   ╲    │
                    ╲   │
                     ➘  ↓
                        D


\begin{code}

 module _
         {X Y B : 𝓤 ̇ }
         (f : X → D)
         (𝕛 : X ↪ Y)
         (h : B → Y)
        where

  open pullback ⌊ 𝕛 ⌋ h

  private
   𝑝𝑏₂ : pullback ↪ B
   𝑝𝑏₂ = 𝕡𝕓₂ ⌊ 𝕛 ⌋-is-embedding

  pullback-naturality : 𝓤 ⊔ 𝓦 ̇
  pullback-naturality = (f ∣ 𝕛) ∘ h ∼ (f ∘ pb₁) ∣ 𝑝𝑏₂

 Pullback-Naturality : (𝓤 ⁺) ⊔ 𝓦 ̇
 Pullback-Naturality = (X Y B : 𝓤 ̇ )
                       (f : X → D)
                       (𝕛 : X ↪ Y)
                       (h : B → Y)
                     → pullback-naturality f 𝕛 h

 fiber-map : {X Y : 𝓤 ̇ } (f : X → D) (j : X ↪ Y) (y : Y)
           → fiber ⌊ j ⌋ y → D
 fiber-map f j y (x , _) = f x

 fiber-to-𝟙 : {X : 𝓤 ̇ } {Y : 𝓤 ̇ } (𝕛 : X ↪ Y) (y : Y)
            → fiber ⌊ 𝕛 ⌋ y ↪ 𝟙 {𝓤}
 fiber-to-𝟙 𝕛 y = embedding-to-𝟙 {𝓤} {𝓤} {Fiber 𝕛 y}

 extensions-are-fiberwise : 𝓤 ⁺ ⊔ 𝓦 ̇
 extensions-are-fiberwise = (X Y B : 𝓤 ̇ )
                            (f : X → D)
                            (𝕛 : X ↪ Y)
                            (y : Y)
                          → (f ∣ 𝕛) y ＝ (fiber-map f 𝕛 y ∣ fiber-to-𝟙 𝕛 y) ⋆

 Pullback-Naturality-gives-that-extensions-are-fiberwise
  : Pullback-Naturality
  → extensions-are-fiberwise
 Pullback-Naturality-gives-that-extensions-are-fiberwise = gap

\end{code}

We now observe that the pullback requirement in the naturality
condition is essential, no matter which injectivity structure we have,
provided D has the property that for every d : D there is a designated
d' ≠ d. We also need function extensionality for functions defined on
the empty type.

\begin{code}

module counter-example-to-general-naturality
        (ϕ : D → D)
        (δ : (d : D) → ϕ d ≠ d)
        (𝓤 𝓥 : Universe)
        ((_∣_ , e) : injective-structure D 𝓤 𝓥)
        (fe : funext 𝓤 𝓦)
      where

 A X : 𝓤 ̇
 B Y : 𝓥 ̇

 A = 𝟘
 B = 𝟙
 X = 𝟙
 Y = 𝟙

 𝕜 : A ↪ B
 𝕛 : X ↪ Y
 g : A → X
 h : B → Y

 𝕜 = unique-from-𝟘 , unique-from-𝟘-is-embedding
 𝕛 = unique-to-𝟙 , maps-of-props-are-embeddings _ 𝟙-is-prop 𝟙-is-prop
 g = unique-from-𝟘
 h = id

 f₀ : A → D
 f₀ = unique-from-𝟘

 d₀ : D
 d₀ = (f₀ ∣ 𝕜) ⋆

 f : X → D
 f _ = ϕ d₀

 naturality-failure : ¬ ((f ∣ 𝕛) ∘ h ∼ (f ∘ g) ∣ 𝕜)
 naturality-failure p = δ d₀ II
  where
   I : f ∘ g ＝ f₀
   I = dfunext fe (λ x → 𝟘-elim x)

   II = ϕ d₀              ＝⟨ refl ⟩
        f ⋆               ＝⟨ (e f 𝕛 ⋆)⁻¹ ⟩
        (f ∣ 𝕛) (⌊ 𝕛 ⌋ ⋆) ＝⟨ refl ⟩
        (f ∣ 𝕛) ⋆         ＝⟨ refl ⟩
        ((f ∣ 𝕛) ∘ h) ⋆   ＝⟨ p ⋆ ⟩
        ((f ∘ g) ∣ 𝕜) ⋆   ＝⟨ ap (λ - → (- ∣ 𝕜) ⋆) I ⟩
        (f₀ ∣ 𝕜) ⋆        ＝⟨ refl ⟩
        d₀                ∎

\end{code}

Now the definition of flabby associativity.

\begin{code}

module _
        {𝓤 : Universe}
        (s@(⨆ , _) : flabby-structure D 𝓤)
       where

 flabby-associativity : 𝓤 ⁺ ⊔ 𝓦 ̇
 flabby-associativity = (P : Ω 𝓤) (Q : P holds → Ω 𝓤) (f : ΣΩ Q holds → D)
                      → ⨆ (ΣΩ Q) f ＝ ⨆ P (λ p → ⨆ (Q p) (λ q → f (p , q)))

\end{code}

To show that flabby associativity implies injective associativity and
pullback naturality of the derived injective structure, we need to
assume propositional and functional extensionality.

\begin{code}

 module _
         (pe : Prop-Ext)
         (fe : Fun-Ext)
         (fassoc : flabby-associativity)
       where

  private
   _∣_ : {X Y : 𝓤 ̇ } → (X → D) → (X ↪ Y) → (Y → D)
   _∣_ = injective-extension-operator D (derived-injective-structure D s)


  derived-injective-associativity
   : injective-associativity (derived-injective-structure D s)
  derived-injective-associativity f 𝕛 𝕜 z = V
   where
    I : ⨆ (ΣΩ w ꞉ Fiber 𝕜 z , Fiber 𝕛 (fiber-point w)) (λ q → f (fiber-point (pr₂ q)))
      ＝ ⨆ (Fiber 𝕜 z) (λ u → ⨆ (Fiber 𝕛 (fiber-point u)) (f ∘ fiber-point))
    I = fassoc
          (Fiber 𝕜 z)
          (λ (p : fiber ⌊ 𝕜 ⌋ z) → Fiber 𝕛 (fiber-point p))
          (λ (q : (Σ w ꞉ fiber ⌊ 𝕜 ⌋ z , fiber ⌊ 𝕛 ⌋ (fiber-point w))) → f (fiber-point (pr₂ q)))

    II : (fiber ⌊ 𝕜 ⊚ 𝕛 ⌋ z) ≃ (Σ w ꞉ fiber ⌊ 𝕜 ⌋ z , fiber ⌊ 𝕛 ⌋ (fiber-point w))
    II = fiber-of-composite ⌊ 𝕛 ⌋ ⌊ 𝕜 ⌋ z

    III : ⨆ (Fiber (𝕜 ⊚ 𝕛) z) (f ∘ fiber-point)
      ＝ ⨆ (ΣΩ w ꞉ Fiber 𝕜 z , Fiber 𝕛 (fiber-point w)) (λ q → f (fiber-point (pr₂ q)))
    III = ⨆-change-of-variable-≃ D pe fe ⨆ (f ∘ fiber-point) II

    IV : ⨆ (Fiber (𝕜 ⊚ 𝕛) z) (f ∘ fiber-point)
      ＝ ⨆ (Fiber 𝕜 z) (λ w → ⨆ (Fiber 𝕛 (fiber-point w)) (f ∘ fiber-point))
    IV = III ∙ I

    V : (f ∣ (𝕜 ⊚ 𝕛)) z ＝ ((f ∣ 𝕛) ∣ 𝕜) z
    V = IV

  derived-injective-pullback-naturality
   : Pullback-Naturality (derived-injective-structure D s)
  derived-injective-pullback-naturality X Y B f 𝕛 h = II
   where
    open pullback ⌊ 𝕛 ⌋ h

    𝑝𝑏₂ : pullback ↪ B
    𝑝𝑏₂ = 𝕡𝕓₂ ⌊ 𝕛 ⌋-is-embedding

    module _ (b : B) where

     ϕ : fiber ⌊ 𝕛 ⌋ (h b) → fiber ⌊ 𝑝𝑏₂ ⌋ b
     ϕ = (λ (x , e) → ((x , b) , e) , refl)

     ψ : fiber ⌊ 𝑝𝑏₂ ⌋ b → fiber ⌊ 𝕛 ⌋ (h b)
     ψ (((x , _) , e) , refl) = (x , e)

     I : f ∘ pr₁ ∘ ψ ∼ f ∘ pb₁ ∘ fiber-point
     I (((x , _) , e) , refl) = refl


     II : (f ∣ 𝕛) (h b) ＝ ((f ∘ pb₁) ∣ 𝑝𝑏₂) b
     II = (f ∣ 𝕛) (h b)                            ＝⟨ refl ⟩
          ⨆ (Fiber 𝕛 (h b)) (f ∘ fiber-point)      ＝⟨ II₀ ⟩
          ⨆ (Fiber 𝑝𝑏₂ b) (f ∘ fiber-point ∘ ψ)    ＝⟨ II₁ ⟩
          ⨆ (Fiber 𝑝𝑏₂ b) (f ∘ pb₁ ∘ fiber-point)  ＝⟨ refl ⟩
          ((f ∘ pb₁) ∣ 𝑝𝑏₂) b                      ∎
           where
            II₀ = ⨆-change-of-variable D pe fe ⨆ (f ∘ fiber-point) (ϕ , ψ)
            II₁ = ap (⨆ (Fiber 𝑝𝑏₂ b)) (dfunext fe I)

\end{code}

Notice that we didn't use the extension properties of the flabby
structure or the derive injective structure.

We now show that injective associativity implies flabby associativity
of the derived flabby structure, assuming pullback naturality.

\begin{code}

module _
        {𝓤          : Universe}
        (s@(_∣_ , e) : injective-structure D 𝓤 𝓤)
        (pe          : Prop-Ext)
        (fe          : Fun-Ext)
        (iassoc      : injective-associativity s)
        (pbn         : Pullback-Naturality s)
      where

 private
  ⨆ : (P : Ω 𝓤) → (P holds → D) → D
  ⨆ = flabby-extension-operator D (derived-flabby-structure D s)

 derived-flabby-associativity
  : Pullback-Naturality s
  → flabby-associativity (derived-flabby-structure D s)
 derived-flabby-associativity pbn P Q f
  = ⨆ (ΣΩ Q) f                             ＝⟨ refl ⟩
    (f ∣ w) ⋆                              ＝⟨ ap (λ - → (f ∣ -) ⋆) I ⟩
    (f ∣ (v ⊚ u)) ⋆                        ＝⟨ iassoc f u v ⋆ ⟩
    ((f ∣ u) ∣ v) ⋆                        ＝⟨ refl ⟩
    ⨆ P (f ∣ u)                            ＝⟨ ap (⨆ P) (dfunext fe II) ⟩
    ⨆ P (λ p → ⨆ (Q p) (λ q → f (p , q))) ∎
    where
     u : ΣΩ Q holds ↪ P holds
     u = pr₁ , pr₁-is-embedding (λ p → holds-is-prop (Q p))

     v : P holds ↪ 𝟙
     v = embedding-to-𝟙

     w : ΣΩ Q holds ↪ 𝟙
     w = embedding-to-𝟙

     I : w ＝ v ⊚ u
     I = to-subtype-＝ (being-embedding-is-prop fe') refl

     II-lemma : (p : P holds)
              → ⨆ (Fiber u p) (f ∘ fiber-point) ＝ ⨆ (Q p) (λ q → f (p , q))
     II-lemma p = ⨆-change-of-variable D pe fe ⨆ (f ∘ fiber-point) (g , h)
      where
       g : fiber ⌊ u ⌋ p → Q p holds
       g ((p' , q) , _) = transport (λ - → Q - holds) (holds-is-prop P p' p) q

       h : Q p holds → fiber ⌊ u ⌋ p
       h q = (p , q) , holds-is-prop P (⌊ u ⌋ (p , q)) p


     II : (p : P holds) → (f ∣ u) p ＝ ⨆ (Q p) (λ q → f (p , q))
     II p = (f ∣ u) p                                ＝⟨ II₀ ⟩
            (fiber-map s f u p ∣ fiber-to-𝟙 s u p) ⋆ ＝⟨ refl ⟩
            ⨆ (Fiber u p) (f ∘ fiber-point)         ＝⟨ II-lemma p ⟩
            ⨆ (Q p) (λ q → f (p , q))               ∎
             where
              II₀ = Pullback-Naturality-gives-that-extensions-are-fiberwise
                     s pbn (ΣΩ Q holds) (P holds) (P holds) f u p

\end{code}

To be continued.

In addition to filling one gap, we need to add the things discussed in
the following talk,

https://martinescardo.github.io/.talks/2025-05-29-Note-09-58-algebraic-injectives-assume_pdf.pdf

regarding round trips between injective structure and flabby structure.
