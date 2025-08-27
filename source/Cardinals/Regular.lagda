Ian Ray August 26 2025.

Regular cardinals and their constructive limitations are explored.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.Base
open import UF.Embeddings
open import UF.FunExt
open import UF.Logic
open import UF.PropTrunc
open import UF.Sets
open import UF.Sets-Properties
open import UF.SetTrunc
open import UF.Subsingletons
open import UF.Subsingletons-Properties
open import UF.SubtypeClassifier
open import UF.SubtypeClassifier-Properties

module Cardinals.Regular
 (fe : FunExt)
 (pe : PropExt)
 (st : set-truncations-exist)
 (pt : propositional-truncations-exist)
 where

open import Cardinals.Type st
open import Cardinals.Preorder fe pe st pt

open set-truncations-exist st
open propositional-truncations-exist pt
open Truncation pt

\end{code}

We need to define cardinality of sets.

\begin{code}

card : hSet 𝓤 → Card 𝓤
card = set-trunc-in

\end{code}

We start by defining what it means for an set and by extension a cardinal to
be infinite.

TODO. Put infinite set some where else if it doesn't already exist.

\begin{code}

infinite-set : hSet 𝓤 → Ω 𝓤
infinite-set (X , s) = ∥ ℕ ↪ X ∥Ω

infinite-cardinal : Card 𝓤 → Ω 𝓤
infinite-cardinal {𝓤}
 = set-trunc-rec (Ω 𝓤) (Ω-is-set (fe 𝓤 𝓤) (pe 𝓤)) infinite-set

\end{code}

We now define a regular cardinal using one of the classically equivalent
definitions found on the n-lab.

\begin{code}

module _ {𝓥 𝓦 : Universe} where

 regular-cardinal : Card 𝓤 → {!(𝓥 ⁺) ⊔ (𝓦 ⁺) ⊔ 𝓤!} ̇ 
 regular-cardinal α = (infinite-cardinal α holds)
                    × ({P : hSet 𝓥} {X : hSet 𝓦}
                    → (f : underlying-set P → underlying-set X)
                    → ((x : underlying-set X)
                       → (card (fiber f x , Σ-is-set (underlying-set-is-set P)
    (λ - → props-are-sets (underlying-set-is-set X))) < α) holds)
                    × ((card X < α) holds)
                    → (card P < α) holds)

\end{code}
