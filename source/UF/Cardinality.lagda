Ian Ray, 24th August 2025

We introduce cardinality as defined in the HoTT book

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module UF.Cardinality (fe : Fun-Ext) where

open import MLTT.Spartan 
open import Notation.Decimal
open import UF.Sets
open import UF.TruncationLevels hiding (_+_)
open import UF.Truncations fe

module _ (ge : general-truncations-exist) where

 open general-truncations-exist ge

 Card : (𝓤 : Universe) → (𝓤 ⁺)  ̇
 Card 𝓤 = ∥ hSet 𝓤 ∥[ 0 ]

 cardinality : hSet 𝓤 → Card 𝓤
 cardinality = ∣_∣[ 0 ]
 
\end{code}

We define cardinal addition

\begin{code}

 _+'_ : Card 𝓤 → Card 𝓤 → Card 𝓤
 _+'_ = ∥∥ₙ-rec₂ ∥∥ₙ-is-truncated I
  where
   I : hSet 𝓤 → hSet 𝓤 → Card 𝓤
   I (A , A-is-set) (B , B-is-set) = ∣ ((A + B) , II) ∣[ 0 ]
    where
     II : is-set (A + B)
     II = +-is-set A B A-is-set B-is-set 

\end{code}

Cardinal inequality

\begin{code}

 _≤'_ : Card 𝓤 → Card 𝓤 → Card 𝓤
 _≤'_ = ∥∥ₙ-rec₂ ∥∥ₙ-is-truncated
         (λ (A , A-is-set) → λ (B , B-is-set) → ∣ {!!} , {!!} ∣[ 0 ])

\end{code}
