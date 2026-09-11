Ian Ray. September 05 2026.

We construct W-sets in the presence of the natural numbers and a modified
version of Tarski's least fixed point principle that is provable from
propositional resizing but makes sense in a predicative setting. 

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons

module OrderedTypes.W-SetsfromTarskiLFP-SmallBasis
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : Prop-Ext)
       where

private
 fe' : FunExt
 fe' 𝓤 𝓥 = fe {𝓤} {𝓥}

open import MLTT.Spartan
open import UF.DiscreteAndSeparated
open import UF.Logic
open import UF.Powerset-MultiUniverse
open import UF.Sets
open import UF.Sets-Properties
open import UF.SubtypeClassifier
open import UF.Subsingletons-FunExt
open import UF.Subsingletons-Properties
open import Naturals.Order

open AllCombinators pt fe
open PropositionalTruncation pt 

\end{code}

We are going to assume the natural numbers and a weaker version of elimination
restricted to sets.

\begin{code}

ℕ-set-elimination : (𝓤 : Universe) → (𝓤 ⁺) ̇
ℕ-set-elimination 𝓤 = (P : ℕ → 𝓤 ̇)
                    → ((n : ℕ) → is-set (P n))
                    → P zero
                    → ((n : ℕ) → P n → P (succ n))
                    → (n : ℕ) → P n

ℕ-set-recursion : (𝓤 : Universe) → (𝓤 ⁺) ̇
ℕ-set-recursion 𝓤 = (A : 𝓤 ̇)
                  → is-set A
                  → A
                  → (ℕ → A → A)
                  → ℕ → A

module ℕ-Rec (ℕ-set-elim : ℕ-set-elimination 𝓤) where

 ℕ-set-rec : ℕ-set-recursion 𝓤
 ℕ-set-rec A is-set-A a₀ s
  = ℕ-set-elim (λ _ → A) (λ _ → is-set-A) a₀ s

\end{code}

We need to define a type of (non-well-founded) trees with nodes taken from a
set A, which we denote Tree A, so that we can consider monotone maps on
𝓟 (Tree A) which encode the the constructor of a W-set W (A : 𝓤) (B a).

We start by defining what a branch through a tree is. Each particular branch
is finite and we represent them as pairs of (n , p) where n : ℕ and p : ℕ → A
is a sequence of nodes (where f(m) for m ≥ n is junk. I guess we could use maps
from Fin n ?...)

\begin{code}

module _ (ℕ-set-elim : ℕ-set-elimination 𝓤)
         (A : 𝓤 ̇) (A-set : is-set A)
         (B : A → 𝓥 ̇) (B-set : (a : A) → is-set (B a))
       where

 open ℕ-Rec ℕ-set-elim

 Branch : 𝓤 ̇
 Branch = ℕ × (ℕ → A)

 Branch-is-set : is-set Branch
 Branch-is-set = ×-is-set ℕ-is-set (Π-is-set fe (λ _ → A-set))

 branch-extension : A
                  → Branch
                  → Branch
 branch-extension a (k , b) = (succ k , ℕ-set-rec A A-set a (λ n _ → b n))

{- We probably need computation rules -}

\end{code}

We need sub-branches to agree up to their index.

\begin{code}

 _⊑_ : Branch → Branch → 𝓤 ̇
 (n , b) ⊑ (m , b') = (n ≤ℕ m) × ((i : ℕ) → i <ℕ n → b i ＝ b' i)

\end{code}

A tree is then a collection of branches that are pre-fix closed.

\begin{code}

 Tree : 𝓤 ⁺ ̇
 Tree = Σ T ꞉ 𝓟 {𝓤} Branch , ((b b' : Branch) → (b' ∈ T) × (b ⊑ b') → b ∈ T)

 Tree-is-set : is-set Tree
 Tree-is-set
  = Σ-is-set (𝓟-is-set' fe pe)
     (λ - → props-are-sets (Π₃-is-prop fe (λ b _ _ → holds-is-prop (- b))))

 branch-set-extension : A
                      → 𝓟 {𝓤} Branch
                      → 𝓟 {𝓤} Branch
 branch-set-extension a T b
  = ((∃ b' ꞉ Branch , b' ∈ T × (b ＝ branch-extension a b')) , ∃-is-prop)

\end{code}

Can we attatch a node to a set of trees?

\begin{code}

 attatch : (a : A) (f : B a → Tree)
         → Tree
 attatch a f = (branch-set-extension a {!???!} , {!!})

\end{code}

Now we consider a monotone map on the powerset of Tree which encodes W-sets.

\begin{code}

 wf-tree-constr : 𝓟 {𝓤} Tree → 𝓟 {𝓤} Tree
 wf-tree-constr S = {!!}

\end{code}
