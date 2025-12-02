Ian Ray. 2nd September 2025.

We provide some equivalent descriptions of univalent reflexive graphs (see
Sterling, Ulrik, etc.)


\begin{code}

{-# OPTIONS --safe --without-K #-}

module DURGs.UnivalentReflexiveGraphs where

open import MLTT.Spartan
open import UF.Base
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.FunExt
open import UF.PropIndexedPiSigma
open import UF.Retracts
open import UF.Subsingletons
open import UF.Subsingletons-Properties
open import DURGs.ReflexiveGraphs

fan : (𝓐 : refl-graph 𝓤 𝓥)
    → ⊰ 𝓐 ⊱
    → 𝓤 ⊔ 𝓥 ̇ 
fan 𝓐 x = Σ y ꞉ ⊰ 𝓐 ⊱ , x ≈⟨ 𝓐 ⟩ y

cofan : (𝓐 : refl-graph 𝓤 𝓥)
      → ⊰ 𝓐 ⊱
      → 𝓤 ⊔ 𝓥 ̇ 
cofan 𝓐 x = Σ y ꞉ ⊰ 𝓐 ⊱ , y ≈⟨ 𝓐 ⟩ x

prop-fan-to-cofan' : Fun-Ext
                  → (𝓐 : refl-graph 𝓤 𝓥)
                  → ((x : ⊰ 𝓐 ⊱) → is-prop (fan 𝓐 x))
                  → ((x : ⊰ 𝓐 ⊱) → is-prop (cofan 𝓐 x))
prop-fan-to-cofan' {𝓤} {𝓥} fe 𝓐 fan-prop = ⌜ I ⌝⁻¹ (λ - → refl)
 where
  I = ((x : ⊰ 𝓐 ⊱) → is-prop (cofan 𝓐 x))
        ≃⟨refl⟩
      ((x : ⊰ 𝓐 ⊱) → ((y , s) (y' , t) : cofan 𝓐 x) → (y , s) ＝ (y' , t))
        ≃⟨ II ⟩
      ((x y : ⊰ 𝓐 ⊱) (s : y ≈⟨ 𝓐 ⟩ x) (y' : ⊰ 𝓐 ⊱) (t : y' ≈⟨ 𝓐 ⟩ x)
        → (y , s) ＝ (y' , t))
        ≃⟨ Π-flip ⟩
      ((y x : ⊰ 𝓐 ⊱) (s : y ≈⟨ 𝓐 ⟩ x) (y' : ⊰ 𝓐 ⊱) (t : y' ≈⟨ 𝓐 ⟩ x)
        → (y , s) ＝ (y' , t))
        ≃⟨ Π-cong fe fe (λ y → ≃-sym (curry-uncurry' fe fe)) ⟩
      ((y : ⊰ 𝓐 ⊱) ((x , s) : fan 𝓐 y) (y' : ⊰ 𝓐 ⊱) (t : y' ≈⟨ 𝓐 ⟩ x)
        → (y , s) ＝ (y' , t))
        ≃⟨ III ⟩
      ((y y' : ⊰ 𝓐 ⊱) (t : y' ≈⟨ 𝓐 ⟩ y) → (y , 𝓻 𝓐 y) ＝ (y' , t))
        ≃⟨ Π-flip ⟩
      ((y' y : ⊰ 𝓐 ⊱) (t : y' ≈⟨ 𝓐 ⟩ y) → (y , 𝓻 𝓐 y) ＝ (y' , t))
        ≃⟨ Π-cong fe fe (λ y' → ≃-sym (curry-uncurry' fe fe)) ⟩
      ((y' : ⊰ 𝓐 ⊱) ((y , t) : fan 𝓐 y') → (y , 𝓻 𝓐 y) ＝ (y' , t))
        ≃⟨ IV ⟩
      ((y' : ⊰ 𝓐 ⊱) → (y' , 𝓻 𝓐 y') ＝ (y' , 𝓻 𝓐 y'))               ■
   where
    II = Π-cong fe fe (λ - → ≃-comp (curry-uncurry' fe fe)
          (Π-cong fe fe (λ y → Π-cong fe fe (λ s → curry-uncurry' fe fe))))
    III = Π-cong fe fe (λ y → prop-indexed-product (y , 𝓻 𝓐 y) fe (fan-prop y))
    IV = Π-cong fe fe
          (λ y' → prop-indexed-product (y' , 𝓻 𝓐 y') fe (fan-prop y'))

prop-fan-to-cofan : (𝓐 : refl-graph 𝓤 𝓥)
                  → ((x : ⊰ 𝓐 ⊱) → is-prop (fan 𝓐 x))
                  → ((x : ⊰ 𝓐 ⊱) → is-prop (cofan 𝓐 x))
prop-fan-to-cofan 𝓐 fan-prop x (y , s) (y' , t)
 = I III VI IV VII
 where
  I : (p : y ＝ x) (q : x ＝ y')
      (α : transport (λ - → y ≈⟨ 𝓐 ⟩ -) p (𝓻 𝓐 y) ＝ s)
      (β : transport (λ - → y' ≈⟨ 𝓐 ⟩ -) q t ＝ 𝓻 𝓐 y')
    → (y , s) ＝ (y' , t)
  I refl refl refl refl = refl
  II : (y , 𝓻 𝓐 y) ＝ (x , s)
  II = fan-prop y (y , 𝓻 𝓐 y) (x , s)
  III : y ＝ x
  III = ap pr₁ II
  IV : transport (λ - → y ≈⟨ 𝓐 ⟩ -) III (𝓻 𝓐 y) ＝ s
  IV = pr₂ (from-Σ-＝ II)
  V : (x , t) ＝ (y' , 𝓻 𝓐 y')
  V = fan-prop y' (x , t) (y' , 𝓻 𝓐 y')
  VI : x ＝ y'
  VI = pr₁ (from-Σ-＝ V)
  VII : transport (λ - → y' ≈⟨ 𝓐 ⟩ -) VI t ＝ 𝓻 𝓐 y'
  VII = pr₂ (from-Σ-＝ V)

prop-cofan-to-fan : (𝓐 : refl-graph 𝓤 𝓥) 
                  → ((x : ⊰ 𝓐 ⊱) → is-prop (cofan 𝓐 x))
                  → ((x : ⊰ 𝓐 ⊱) → is-prop (fan 𝓐 x))
prop-cofan-to-fan 𝓐 cofan-prop x (y , s) (y' , t)
 = I III VI IV VII
 where
  I : (p : y ＝ x) (q : x ＝ y')
      (α : transport (λ - → - ≈⟨ 𝓐 ⟩ y) p (𝓻 𝓐 y) ＝ s)
      (β : transport (λ - → - ≈⟨ 𝓐 ⟩ y') q t ＝ 𝓻 𝓐 y')
    → (y , s) ＝ (y' , t)
  I refl refl refl refl = to-Σ-＝ (refl , refl)
  II : (y , 𝓻 𝓐 y) ＝ (x , s)
  II = cofan-prop y (y , 𝓻 𝓐 y) (x , s)
  III : y ＝ x
  III = pr₁ (from-Σ-＝ II)
  IV : transport (λ - → - ≈⟨ 𝓐 ⟩ y) III (𝓻 𝓐 y) ＝ s
  IV = pr₂ (from-Σ-＝ II)
  V : (x , t) ＝ (y' , 𝓻 𝓐 y')
  V = cofan-prop y' (x , t) (y' , 𝓻 𝓐 y')
  VI : x ＝ y'
  VI = pr₁ (from-Σ-＝ V)
  VII : transport (λ - → - ≈⟨ 𝓐 ⟩ y') VI t ＝ 𝓻 𝓐 y'
  VII = pr₂ (from-Σ-＝ V)

contr-fan-to-prop : (𝓐 : refl-graph 𝓤 𝓥)
                  → ((x : ⊰ 𝓐 ⊱) → is-contr (fan 𝓐 x))
                  → ((x : ⊰ 𝓐 ⊱) → is-prop (fan 𝓐 x))
contr-fan-to-prop 𝓐 fan-contr x = singletons-are-props (fan-contr x)

prop-fan-to-contr : (𝓐 : refl-graph 𝓤 𝓥)
                  → ((x : ⊰ 𝓐 ⊱) → is-prop (fan 𝓐 x))
                  → ((x : ⊰ 𝓐 ⊱) → is-contr (fan 𝓐 x))
prop-fan-to-contr 𝓐 fan-prop x
 = pointed-props-are-singletons (x , 𝓻 𝓐 x) (fan-prop x)

contr-fan-to-cofan : (𝓐 : refl-graph 𝓤 𝓥)
                   → ((x : ⊰ 𝓐 ⊱) → is-contr (fan 𝓐 x))
                   → ((x : ⊰ 𝓐 ⊱) → is-contr (cofan 𝓐 x))
contr-fan-to-cofan 𝓐 contr-fan x
 = pointed-props-are-singletons (x , 𝓻 𝓐 x)
    (prop-fan-to-cofan 𝓐 (λ - → singletons-are-props (contr-fan -)) x)

prop-fan-to-contr-cofan : (𝓐 : refl-graph 𝓤 𝓥)
                        → ((x : ⊰ 𝓐 ⊱) → is-prop (fan 𝓐 x))
                        → ((x : ⊰ 𝓐 ⊱) → is-contr (cofan 𝓐 x))
prop-fan-to-contr-cofan 𝓐 fan-prop x
 = contr-fan-to-cofan 𝓐 (prop-fan-to-contr 𝓐 fan-prop) x

contr-cofan-to-fan : (𝓐 : refl-graph 𝓤 𝓥)
                   → ((x : ⊰ 𝓐 ⊱) → is-contr (cofan 𝓐 x))
                   → ((x : ⊰ 𝓐 ⊱) → is-contr (fan 𝓐 x))
contr-cofan-to-fan 𝓐 contr-cofan x
 = pointed-props-are-singletons (x , 𝓻 𝓐 x)
    (prop-cofan-to-fan 𝓐 (λ - → singletons-are-props (contr-cofan -)) x)

\end{code}

We give the canonical function from an identification to an edge.

\begin{code}

id-to-edge : (𝓐 : refl-graph 𝓤 𝓥) {x y : ⊰ 𝓐 ⊱}
           → x ＝ y
           → x ≈⟨ 𝓐 ⟩ y
id-to-edge 𝓐 {x} {x} refl = 𝓻 𝓐 x

\end{code}

If each fan is propositional then id-to-edge has a section and retraction.

\begin{code}

helper-edge-to-id : {𝓐 : refl-graph 𝓤 𝓥}
                  → (x y : ⊰ 𝓐 ⊱)
                  → (p : x ≈⟨ 𝓐 ⟩ y)
                  → (x , 𝓻 𝓐 x) ＝ (y , p)
                  → x ＝ y
helper-edge-to-id {_} {_} {𝓐} x .x .(𝓻 𝓐 x) refl = refl

prop-fans-edge-to-id : {𝓐 : refl-graph 𝓤 𝓥}
                     → ((x : ⊰ 𝓐 ⊱) → is-prop (fan 𝓐 x))
                     → (x y : ⊰ 𝓐 ⊱)
                     → x ≈⟨ 𝓐 ⟩ y
                     → x ＝ y
prop-fans-edge-to-id {_} {_} {𝓐} prop-fan x y p
 = helper-edge-to-id {_} {_} {𝓐} x y p (prop-fan x (x , 𝓻 𝓐 x) (y , p))

prop-fans-gives-retraction : {𝓐 : refl-graph 𝓤 𝓥}
                           → ((x : ⊰ 𝓐 ⊱) → is-prop (fan 𝓐 x))
                           → (x y : ⊰ 𝓐 ⊱)
                           → has-retraction (id-to-edge 𝓐)
prop-fans-gives-retraction {_} {_} {𝓐} fan-prop x y
 = (prop-fans-edge-to-id fan-prop x y , II x y)
 where
  I : (x : ⊰ 𝓐 ⊱) → fan-prop x (x , 𝓻 𝓐 x) (x , 𝓻 𝓐 x) ＝ refl
  I x = props-are-sets (fan-prop x) (fan-prop x (x , 𝓻 𝓐 x) (x , 𝓻 𝓐 x)) refl
  II : (x y : ⊰ 𝓐 ⊱) (p : x ＝ y)
     → (prop-fans-edge-to-id {_} {_} {𝓐} fan-prop x y)
        (id-to-edge 𝓐 p) ＝ p
  II x .x refl = ap (helper-edge-to-id x x (𝓻 𝓐 x)) (I x)

paths-are-retracts-of-edges : {𝓐 : refl-graph 𝓤 𝓥}
                            → ((x : ⊰ 𝓐 ⊱) → is-prop (fan 𝓐 x))
                            → (x y : ⊰ 𝓐 ⊱)
                            → retract (x ＝ y) of (x ≈⟨ 𝓐 ⟩ y)
paths-are-retracts-of-edges {_} {_} {𝓐} fan-prop x y
 = (prop-fans-edge-to-id fan-prop x y , id-to-edge 𝓐 ,
    retraction-equation (id-to-edge 𝓐)
     (prop-fans-gives-retraction fan-prop x y))

prop-fans-gives-section : {𝓐 : refl-graph 𝓤 𝓥}
                        → ((x : ⊰ 𝓐 ⊱) → is-prop (fan 𝓐 x))
                        → (x y : ⊰ 𝓐 ⊱)
                        → has-section (id-to-edge 𝓐)
prop-fans-gives-section {_} {_} {𝓐} fan-prop x y
 = (prop-fans-edge-to-id {_} {_} {𝓐} fan-prop x y , II)
 where
  I : (p : x ≈⟨ 𝓐 ⟩ y) (ϕ : (x , 𝓻 𝓐 x) ＝ (y , p))
    → id-to-edge 𝓐 (helper-edge-to-id {_} {_} {𝓐} x y p ϕ) ＝ p
  I p refl = refl
  II : (p : x ≈⟨ 𝓐 ⟩ y)
     → id-to-edge 𝓐 (prop-fans-edge-to-id fan-prop x y p) ＝ p
  II p = I p (fan-prop x (x , 𝓻 𝓐 x) (y , p))

edges-are-retracts-of-paths : {𝓐 : refl-graph 𝓤 𝓥}
                            → ((x : ⊰ 𝓐 ⊱) → is-prop (fan 𝓐 x))
                            → (x y : ⊰ 𝓐 ⊱)
                            → retract (x ≈⟨ 𝓐 ⟩ y) of (x ＝ y)
edges-are-retracts-of-paths {_} {_} {𝓐} fan-prop x y
 = (id-to-edge 𝓐 , prop-fans-gives-section fan-prop x y)

\end{code}

Now we show that id-to-edge is an equiv iff all fans are propositional.

\begin{code}

id-to-edge-equiv-implies-prop-fans : {𝓐 : refl-graph 𝓤 𝓥}
                                   → ((x y : ⊰ 𝓐 ⊱) → is-equiv (id-to-edge 𝓐))
                                   → ((x : ⊰ 𝓐 ⊱) → is-prop (fan 𝓐 x))
id-to-edge-equiv-implies-prop-fans {_} {_} {𝓐} e
 = contr-fan-to-prop 𝓐 fan-is-contr
 where
  fan-is-contr : (x : ⊰ 𝓐 ⊱) → is-contr (fan 𝓐 x)
  fan-is-contr x = equiv-to-singleton' (Σ-cong (λ y → id-to-edge 𝓐 , e x y))
                    (singleton-types-are-singletons x)

prop-fans-implies-id-to-edge-equiv
 : {𝓐 : refl-graph 𝓤 𝓥}
 → ((x : ⊰ 𝓐 ⊱) → is-prop (fan 𝓐 x))
 → ((x y : ⊰ 𝓐 ⊱) → is-equiv (id-to-edge 𝓐))
prop-fans-implies-id-to-edge-equiv {_} {_} {𝓐} prop-fans x y
 = (prop-fans-gives-section prop-fans x y ,
     prop-fans-gives-retraction prop-fans x y) 

\end{code}

We now define univalent reflexive graphs in terms of propositional fans, but
one could use any of the equivalent characterizations.

\begin{code}

is-univalent-refl-graph : (𝓐 : refl-graph 𝓤 𝓥) → 𝓤 ⊔ 𝓥 ̇ 
is-univalent-refl-graph 𝓐 = (x : ⊰ 𝓐 ⊱) → is-prop (fan 𝓐 x)

univalent-refl-graph : (𝓤 𝓥 : Universe) → (𝓤 ⁺) ⊔ (𝓥 ⁺) ̇
univalent-refl-graph 𝓤 𝓥 = Σ 𝓐 ꞉ (refl-graph 𝓤 𝓥) , is-univalent-refl-graph 𝓐

\end{code}

We will now record some boiler plate code for univalent reflexive graphs.

\begin{code}

⊰_⊱ᵤ : univalent-refl-graph 𝓤 𝓥 → 𝓤 ̇
⊰ (𝓐 , _) ⊱ᵤ = ⊰ 𝓐 ⊱

edge-relᵤ : (𝓐 : univalent-refl-graph 𝓤 𝓥) → ⊰ 𝓐 ⊱ᵤ → ⊰ 𝓐 ⊱ᵤ → 𝓥 ̇
edge-relᵤ (𝓐 , _) = edge-rel 𝓐

syntax edge-relᵤ 𝓐 x y = x ≈ᵤ⟨ 𝓐 ⟩ y

𝓻ᵤ : (𝓐 : univalent-refl-graph 𝓤 𝓥) → (x : ⊰ 𝓐 ⊱ᵤ) → x ≈ᵤ⟨ 𝓐 ⟩ x
𝓻ᵤ (𝓐 , _) x = 𝓻 𝓐 x

underlying-refl-graph : (𝓐 : univalent-refl-graph 𝓤 𝓥)
                      → refl-graph 𝓤 𝓥
underlying-refl-graph (𝓐 , _) = 𝓐

syntax underlying-refl-graph 𝓐 = 𝓐 /ᵤ 

is-univalent : (𝓐 : univalent-refl-graph 𝓤 𝓥)
             → is-univalent-refl-graph (𝓐 /ᵤ)
is-univalent (𝓐 , is-ua) = is-ua

id-equiv-edge : (𝓐 : univalent-refl-graph 𝓤 𝓥)
              → (x y : ⊰ 𝓐 ⊱ᵤ)
              → (x ＝ y) ≃ (x ≈ᵤ⟨ 𝓐 ⟩ y)
id-equiv-edge 𝓐 x y
 = (id-to-edge (𝓐 /ᵤ) , prop-fans-implies-id-to-edge-equiv (is-univalent 𝓐) x y)

edge-to-id : (𝓐 : univalent-refl-graph 𝓤 𝓥) {x y : ⊰ 𝓐 ⊱ᵤ}
           → x ≈ᵤ⟨ 𝓐 ⟩ y
           → x ＝ y
edge-to-id 𝓐 {x} {y} = ⌜ id-equiv-edge 𝓐 x y ⌝⁻¹

edge-to-id-comp : (𝓐 : univalent-refl-graph 𝓤 𝓥) {x : ⊰ 𝓐 ⊱ᵤ}
                → edge-to-id 𝓐 (𝓻 (𝓐 /ᵤ) x) ＝ refl
edge-to-id-comp 𝓐 {x}
 = inverses-are-retractions (id-to-edge (𝓐 /ᵤ))
    (prop-fans-implies-id-to-edge-equiv (is-univalent 𝓐) x x) refl

\end{code}

We consider the notion of edge induction and show univalence implies it.

TODO: show they are also equivalent.

\begin{code}

edge-induction : (𝓣 : Universe) (𝓐 : refl-graph 𝓤 𝓥) → 𝓤 ⊔ 𝓥 ⊔ (𝓣 ⁺) ̇ 
edge-induction 𝓣 𝓐 = (P : (x y : ⊰ 𝓐 ⊱) → (x ≈⟨ 𝓐 ⟩ y) → 𝓣 ̇)
                   → ((x : ⊰ 𝓐 ⊱) → P x x (𝓻 𝓐 x))
                   → (x y : ⊰ 𝓐 ⊱)
                   → (p : x ≈⟨ 𝓐 ⟩ y)
                   → P x y p

univalence-implies-edge-induction : {𝓐 : refl-graph 𝓤 𝓥}
                                  → is-univalent-refl-graph 𝓐
                                  → edge-induction 𝓣 𝓐
univalence-implies-edge-induction {𝓤} {𝓥} {𝓣} {𝓐} ua P R x y p
 = I (ua x (x , 𝓻 𝓐 x) (y , p))
 where
  I : (x , 𝓻 𝓐 x) ＝ (y , p) → P x y p
  I refl = R x  

\end{code}
