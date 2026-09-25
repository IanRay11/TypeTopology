\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons

module OrderedTypes.Powerset-suplattice-small-basis
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : Prop-Ext)
       where

private
 fe' : FunExt
 fe' 𝓤 𝓥 = fe {𝓤} {𝓥}

open import MLTT.Spartan
open import UF.Embeddings
open import UF.Equiv
open import UF.Logic
open import UF.Powerset-MultiUniverse
open import UF.Retracts
open import UF.Sets
open import UF.Sets-Properties
open import UF.Size
open import UF.SmallnessProperties
open import UF.Subsingletons-Properties
open import UF.SubtypeClassifier
open import OrderedTypes.SupLattice pt fe
open import OrderedTypes.SupLattice-SmallBasis pt fe

open AllCombinators pt fe
open PropositionalTruncation pt hiding (_∨_)
open import Locales.Frame pt fe hiding (⟨_⟩ ; join-of)
open import Slice.Family

\end{code}

We show that the powerset of some given type A is itself a sup-lattice with
small basis. To do this we first need to define the truncated singleton
construction and show that it has the proper characterization of the singleton.

\begin{code}

module _ (A : 𝓤 ̇) where

 open singleton-subsets
 open unions-of-small-families pt 𝓤 𝓤 A
 open PropositionalSubsetInclusionNotation fe
 open Joins {𝓤 ⁺} {𝓤} {𝓟 {𝓤} A} _⊆ₚ_

 𝓟-sup-lattice : Sup-Lattice (𝓤 ⁺) 𝓤 𝓤
 𝓟-sup-lattice
  = (𝓟 {𝓤} A , (_⊆ₚ_ , sup) , (par-ord , suprema))
  where
   sup : Fam 𝓤 (𝓟 A) → 𝓟 {𝓤} A
   sup (S , s) a = ⋃ s a
   par-ord : is-partial-order (𝓟 A) _⊆ₚ_
   par-ord = ((⊆-refl , ⊆-trans) , subset-extensionality pe fe)
   suprema : (S : Fam 𝓤 (𝓟 {𝓤} A)) → ((sup S) is-lub-of S) holds
   suprema (S , s)
    = (⋃-is-upperbound s , λ (U , O) → ⋃-is-lowerbound-of-upperbounds s U O)
 
 ❴_❵ₜᵣ : A → 𝓟 {𝓤} A
 ❴ x ❵ₜᵣ = λ y → (∥ x ＝ y ∥ , ∥∥-is-prop)

 ∈-❴❵ₜᵣ : {x : A} → x ∈ ❴ x ❵ₜᵣ
 ∈-❴❵ₜᵣ {x} = ∣ refl ∣

 ❴❵ₜᵣ-subset-characterization : {x : A} (S : 𝓟 {𝓥} A) → x ∈ S ↔ ❴ x ❵ₜᵣ ⊆ S
 ❴❵ₜᵣ-subset-characterization {𝓥} {x} S = ⦅⇒⦆ , ⦅⇐⦆
  where
   ⦅⇒⦆ : x ∈ S → ❴ x ❵ₜᵣ ⊆ S
   ⦅⇒⦆ x∈S y = ∥∥-rec (holds-is-prop (S y)) (λ p → transport (_∈ S) p x∈S)
   ⦅⇐⦆ : ❴ x ❵ₜᵣ ⊆ S → x ∈ S
   ⦅⇐⦆ γ = γ x ∣ refl ∣

 basis-char : (S : 𝓟 {𝓤} A)
            → ⋃ (↓ᴮ-inclusion 𝓟-sup-lattice ❴_❵ₜᵣ S) ＝ S
 basis-char S = subset-extensionality pe fe I II
  where
   I : ⋃ (↓ᴮ-inclusion 𝓟-sup-lattice ❴_❵ₜᵣ S) ⊆ S
   I x = ∥∥-rec (holds-is-prop (S x))
          (λ ((a , a∈↓S) , o)
            → ∥∥-rec (holds-is-prop (S x))
               (λ p → transport (_∈ S) p (a∈↓S a ∈-❴❵ₜᵣ)) o)
   II : S ⊆ ⋃ (↓ᴮ-inclusion 𝓟-sup-lattice ❴_❵ₜᵣ S)
   II x x∈S
    = ∣ (x , pr₁ (❴❵ₜᵣ-subset-characterization {_} {x} S) x∈S) , ∈-❴❵ₜᵣ ∣

 ❴❵ₜᵣ-is-basis : is-basis 𝓟-sup-lattice ❴_❵ₜᵣ
 ❴❵ₜᵣ-is-basis
  = record{≤-is-small = λ S a → ((❴ a ❵ₜᵣ ⊆ S) , ≃-refl (❴ a ❵ₜᵣ ⊆ S)) ;
           ↓-is-sup
            = λ S → transport
                     (λ - → (- is-lub-of (↓ᴮ 𝓟-sup-lattice ❴_❵ₜᵣ S
                                   , ↓ᴮ-inclusion 𝓟-sup-lattice ❴_❵ₜᵣ S)) holds)
                     (basis-char S)
                     (⋃-is-upperbound (↓ᴮ-inclusion 𝓟-sup-lattice ❴_❵ₜᵣ S)
                      , λ (U , O) → ⋃-is-lowerbound-of-upperbounds
                                    (↓ᴮ-inclusion 𝓟-sup-lattice ❴_❵ₜᵣ S) U O) }

\end{code}

We will now observe that a sup lattice L, with small basis B, gives L as a
retraction of 𝓟 B

           L --- ↓ᴮ ---> 𝓟 B --- ⋁ ---> L
            \                          ^
             \                        /
               -------- id ----------

\begin{code}

module _ {𝓤 𝓣 𝓥 : Universe}
         (L : Sup-Lattice 𝓤 𝓣 𝓥)
         {B : 𝓥 ̇} (β : B → ⟨ L ⟩) (h : is-basis L β)
       where

 open is-basis h

 sup-lat-to-pow : ⟨ L ⟩ → 𝓟 {𝓥} B
 sup-lat-to-pow x b = ((b ≤ᴮ x) , ≤ᴮ-is-prop-valued)

 pow-to-sup-lat : 𝓟 {𝓥} B → ⟨ L ⟩
 pow-to-sup-lat S = ⋁⟨ L ⟩ (𝕋 S , β ∘ 𝕋-to-carrier S)

 sup-lat-pow-compose-to-id
  : pow-to-sup-lat ∘ sup-lat-to-pow ∼ id
 sup-lat-pow-compose-to-id x = is-supᴮ' x ⁻¹

 sup-lattice-retract-of-pow : retract ⟨ L ⟩ of 𝓟 {𝓥} B
 sup-lattice-retract-of-pow
  = (pow-to-sup-lat , sup-lat-to-pow , sup-lat-pow-compose-to-id)

\end{code}

We now show in the presence of prop resizing any small generated sup lattice
is small.

\begin{code}

 sup-lattice-is-small : Ω-resizing 𝓥
                      → ⟨ L ⟩ is 𝓥 small
 sup-lattice-is-small omega-res
  = embedded-retract-is-small sup-lattice-retract-of-pow
     (sections-into-sets-are-embeddings sup-lat-to-pow
      (pow-to-sup-lat , sup-lat-pow-compose-to-id)
      (powersets-are-sets fe pe))
     (Π-is-small fe' (B , ≃-refl B) (λ _ → omega-res))

\end{code}
